import V185TrunkScan23Chunk0886

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5249927 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_5249927 : Nat := 118140960795 + 5249927 * 2 ^ 59
def prefixEnd_5249927 : Nat := 4983230072969 + 3 ^ 40 * 5249927 * 2
def baseEnd_5249927 : Nat := 2695735952016786370168531

theorem tailTrace_5249927 : CollatzResearch.WordTrace tailWord_5249927 prefixEnd_5249927 2695735952016786370168531 := by
  unfold tailWord_5249927
  simp only [CollatzResearch.WordTrace]
  refine ⟨191480568451418569993452035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127653712300945713328968023 191480568451418569993452035)
  ·
    refine ⟨287220852677127854990178053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191480568451418569993452035 287220852677127854990178053)
    ·
      refine ⟨53853909876961472810658385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287220852677127854990178053 53853909876961472810658385)
      ·
        refine ⟨40390432407721104607993789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53853909876961472810658385 40390432407721104607993789)
        ·
          refine ⟨15146412152895414227997671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40390432407721104607993789 15146412152895414227997671)
          ·
            refine ⟨22719618229343121341996507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15146412152895414227997671 22719618229343121341996507)
            ·
              refine ⟨34079427344014682012994761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22719618229343121341996507 34079427344014682012994761)
              ·
                refine ⟨25559570508011011509746071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34079427344014682012994761 25559570508011011509746071)
                ·
                  refine ⟨38339355762016517264619107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25559570508011011509746071 38339355762016517264619107)
                  ·
                    refine ⟨57509033643024775896928661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38339355762016517264619107 57509033643024775896928661)
                    ·
                      refine ⟨2695735952016786370168531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57509033643024775896928661 2695735952016786370168531)
                      ·
                        rfl

theorem cell23_5249927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_5249927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249927 prefixEnd_5249927 := by exact prefixLift 5249927
  have htrace : WordTrace (prefixWord ++ tailWord_5249927) baseStart_5249927 baseEnd_5249927 := by
    simpa [prefixWord, tailWord_5249927, baseEnd_5249927] using wordTrace_append hprefix tailTrace_5249927
  have hstable : (prefixWord ++ tailWord_5249927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249927).length < 2 ^ (prefixWord ++ tailWord_5249927).sum := by decide
  have hdescent : baseEnd_5249927 < baseStart_5249927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249931 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 3, 2, 2]
def baseStart_5249931 : Nat := 118140960795 + 5249931 * 2 ^ 59
def prefixEnd_5249931 : Nat := 4983230072969 + 3 ^ 40 * 5249931 * 2
def baseEnd_5249931 : Nat := 2695738005939404354518513

theorem tailTrace_5249931 : CollatzResearch.WordTrace tailWord_5249931 prefixEnd_5249931 2695738005939404354518513 := by
  unfold tailWord_5249931
  simp only [CollatzResearch.WordTrace]
  refine ⟨191480714343404078676597647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127653809562269385784398431 191480714343404078676597647)
  ·
    refine ⟨287221071515106118014896471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191480714343404078676597647 287221071515106118014896471)
    ·
      refine ⟨430831607272659177022344707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287221071515106118014896471 430831607272659177022344707)
      ·
        refine ⟨646247410908988765533517061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430831607272659177022344707 646247410908988765533517061)
        ·
          refine ⟨121171389545435393537534449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 646247410908988765533517061 121171389545435393537534449)
          ·
            refine ⟨90878542159076545153150837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121171389545435393537534449 90878542159076545153150837)
            ·
              refine ⟨8519863327413426108107891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90878542159076545153150837 8519863327413426108107891)
              ·
                refine ⟨12779794991120139162161837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8519863327413426108107891 12779794991120139162161837)
                ·
                  refine ⟨4792423121670052185810689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12779794991120139162161837 4792423121670052185810689)
                  ·
                    refine ⟨3594317341252539139358017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4792423121670052185810689 3594317341252539139358017)
                    ·
                      refine ⟨2695738005939404354518513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594317341252539139358017 2695738005939404354518513)
                      ·
                        rfl

theorem cell23_5249931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 2, 2].length) (baseStart_5249931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249931 prefixEnd_5249931 := by exact prefixLift 5249931
  have htrace : WordTrace (prefixWord ++ tailWord_5249931) baseStart_5249931 baseEnd_5249931 := by
    simpa [prefixWord, tailWord_5249931, baseEnd_5249931] using wordTrace_append hprefix tailTrace_5249931
  have hstable : (prefixWord ++ tailWord_5249931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249931).length < 2 ^ (prefixWord ++ tailWord_5249931).sum := by decide
  have hdescent : baseEnd_5249931 < baseStart_5249931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249941 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_5249941 : Nat := 118140960795 + 5249941 * 2 ^ 59
def prefixEnd_5249941 : Nat := 4983230072969 + 3 ^ 40 * 5249941 * 2
def baseEnd_5249941 : Nat := 898581046915316438464489

theorem tailTrace_5249941 : CollatzResearch.WordTrace tailWord_5249941 prefixEnd_5249941 898581046915316438464489 := by
  unfold tailWord_5249941
  simp only [CollatzResearch.WordTrace]
  refine ⟨191481079073367850384461677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127654052715578566922974451 191481079073367850384461677)
  ·
    refine ⟨71805404652512943894173129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191481079073367850384461677 71805404652512943894173129)
    ·
      refine ⟨53854053489384707920629847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71805404652512943894173129 53854053489384707920629847)
      ·
        refine ⟨80781080234077061880944771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53854053489384707920629847 80781080234077061880944771)
        ·
          refine ⟨121171620351115592821417157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80781080234077061880944771 121171620351115592821417157)
          ·
            refine ⟨22719678815834173654015717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121171620351115592821417157 22719678815834173654015717)
            ·
              refine ⟨4259939777968907560127947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22719678815834173654015717 4259939777968907560127947)
              ·
                refine ⟨6389909666953361340191921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259939777968907560127947 6389909666953361340191921)
                ·
                  refine ⟨4792432250215021005143941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6389909666953361340191921 4792432250215021005143941)
                  ·
                    refine ⟨898581046915316438464489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792432250215021005143941 898581046915316438464489)
                    ·
                      rfl

theorem cell23_5249941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_5249941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249941 prefixEnd_5249941 := by exact prefixLift 5249941
  have htrace : WordTrace (prefixWord ++ tailWord_5249941) baseStart_5249941 baseEnd_5249941 := by
    simpa [prefixWord, tailWord_5249941, baseEnd_5249941] using wordTrace_append hprefix tailTrace_5249941
  have hstable : (prefixWord ++ tailWord_5249941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249941).length < 2 ^ (prefixWord ++ tailWord_5249941).sum := by decide
  have hdescent : baseEnd_5249941 < baseStart_5249941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249948 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5249948 : Nat := 118140960795 + 5249948 * 2 ^ 59
def prefixEnd_5249948 : Nat := 4983230072969 + 3 ^ 40 * 5249948 * 2
def baseEnd_5249948 : Nat := 2695746735110530788005935

theorem tailTrace_5249948 : CollatzResearch.WordTrace tailWord_5249948 prefixEnd_5249948 2695746735110530788005935 := by
  unfold tailWord_5249948
  simp only [CollatzResearch.WordTrace]
  refine ⟨95740667192171245289983249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127654222922894993719977665 95740667192171245289983249)
  ·
    refine ⟨71805500394128433967487437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95740667192171245289983249 71805500394128433967487437)
    ·
      refine ⟨26927062647798162737807789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71805500394128433967487437 26927062647798162737807789)
      ·
        refine ⟨10097648492924311026677921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26927062647798162737807789 10097648492924311026677921)
        ·
          refine ⟨7573236369693233270008441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10097648492924311026677921 7573236369693233270008441)
          ·
            refine ⟨5679927277269924952506331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7573236369693233270008441 5679927277269924952506331)
            ·
              refine ⟨8519890915904887428759497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679927277269924952506331 8519890915904887428759497)
              ·
                refine ⟨6389918186928665571569623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8519890915904887428759497 6389918186928665571569623)
                ·
                  refine ⟨9584877280392998357354435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6389918186928665571569623 9584877280392998357354435)
                  ·
                    refine ⟨14377315920589497536031653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9584877280392998357354435 14377315920589497536031653)
                    ·
                      refine ⟨2695746735110530788005935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14377315920589497536031653 2695746735110530788005935)
                      ·
                        rfl

theorem cell23_5249948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5249948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249948 prefixEnd_5249948 := by exact prefixLift 5249948
  have htrace : WordTrace (prefixWord ++ tailWord_5249948) baseStart_5249948 baseEnd_5249948 := by
    simpa [prefixWord, tailWord_5249948, baseEnd_5249948] using wordTrace_append hprefix tailTrace_5249948
  have hstable : (prefixWord ++ tailWord_5249948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249948).length < 2 ^ (prefixWord ++ tailWord_5249948).sum := by decide
  have hdescent : baseEnd_5249948 < baseStart_5249948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249951 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 3]
def baseStart_5249951 : Nat := 118140960795 + 5249951 * 2 ^ 59
def prefixEnd_5249951 : Nat := 4983230072969 + 3 ^ 40 * 5249951 * 2
def baseEnd_5249951 : Nat := 2695748275552494276268421

theorem tailTrace_5249951 : CollatzResearch.WordTrace tailWord_5249951 prefixEnd_5249951 2695748275552494276268421 := by
  unfold tailWord_5249951
  simp only [CollatzResearch.WordTrace]
  refine ⟨191481443803331622092325707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127654295868887748061550471 191481443803331622092325707)
  ·
    refine ⟨287222165704997433138488561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191481443803331622092325707 287222165704997433138488561)
    ·
      refine ⟨215416624278748074853866421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287222165704997433138488561 215416624278748074853866421)
      ·
        refine ⟨20195308526132632017549977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215416624278748074853866421 20195308526132632017549977)
        ·
          refine ⟨15146481394599474013162483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20195308526132632017549977 15146481394599474013162483)
          ·
            refine ⟨22719722091899211019743725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15146481394599474013162483 22719722091899211019743725)
            ·
              refine ⟨8519895784462204132403897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22719722091899211019743725 8519895784462204132403897)
              ·
                refine ⟨6389921838346653099302923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8519895784462204132403897 6389921838346653099302923)
                ·
                  refine ⟨9584882757519979648954385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6389921838346653099302923 9584882757519979648954385)
                  ·
                    refine ⟨7188662068139984736715789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9584882757519979648954385 7188662068139984736715789)
                    ·
                      refine ⟨2695748275552494276268421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7188662068139984736715789 2695748275552494276268421)
                      ·
                        rfl

theorem cell23_5249951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_5249951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249951 prefixEnd_5249951 := by exact prefixLift 5249951
  have htrace : WordTrace (prefixWord ++ tailWord_5249951) baseStart_5249951 baseEnd_5249951 := by
    simpa [prefixWord, tailWord_5249951, baseEnd_5249951] using wordTrace_append hprefix tailTrace_5249951
  have hstable : (prefixWord ++ tailWord_5249951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249951).length < 2 ^ (prefixWord ++ tailWord_5249951).sum := by decide
  have hdescent : baseEnd_5249951 < baseStart_5249951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249965 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5249965 : Nat := 118140960795 + 5249965 * 2 ^ 59
def prefixEnd_5249965 : Nat := 4983230072969 + 3 ^ 40 * 5249965 * 2
def baseEnd_5249965 : Nat := 2695755464281657221493357

theorem tailTrace_5249965 : CollatzResearch.WordTrace tailWord_5249965 prefixEnd_5249965 2695755464281657221493357 := by
  unfold tailWord_5249965
  simp only [CollatzResearch.WordTrace]
  refine ⟨191481954425280902483335349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127654636283520601655556899 191481954425280902483335349)
  ·
    refine ⟨17951433227370084607812689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191481954425280902483335349 17951433227370084607812689)
    ·
      refine ⟨13463574920527563455859517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17951433227370084607812689 13463574920527563455859517)
      ·
        refine ⟨5048840595197836295947319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13463574920527563455859517 5048840595197836295947319)
        ·
          refine ⟨7573260892796754443920979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048840595197836295947319 7573260892796754443920979)
          ·
            refine ⟨11359891339195131665881469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7573260892796754443920979 11359891339195131665881469)
            ·
              refine ⟨4259959252198174374705551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11359891339195131665881469 4259959252198174374705551)
              ·
                refine ⟨6389938878297261562058327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259959252198174374705551 6389938878297261562058327)
                ·
                  refine ⟨9584908317445892343087491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6389938878297261562058327 9584908317445892343087491)
                  ·
                    refine ⟨14377362476168838514631237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9584908317445892343087491 14377362476168838514631237)
                    ·
                      refine ⟨2695755464281657221493357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14377362476168838514631237 2695755464281657221493357)
                      ·
                        rfl

theorem cell23_5249965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5249965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249965 prefixEnd_5249965 := by exact prefixLift 5249965
  have htrace : WordTrace (prefixWord ++ tailWord_5249965) baseStart_5249965 baseEnd_5249965 := by
    simpa [prefixWord, tailWord_5249965, baseEnd_5249965] using wordTrace_append hprefix tailTrace_5249965
  have hstable : (prefixWord ++ tailWord_5249965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249965).length < 2 ^ (prefixWord ++ tailWord_5249965).sum := by decide
  have hdescent : baseEnd_5249965 < baseStart_5249965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5249988 : List Nat := [2, 3, 3, 3, 2, 1, 1, 8]
def baseStart_5249988 : Nat := 118140960795 + 5249988 * 2 ^ 59
def prefixEnd_5249988 : Nat := 4983230072969 + 3 ^ 40 * 5249988 * 2
def baseEnd_5249988 : Nat := 99843232382841134500213

theorem tailTrace_5249988 : CollatzResearch.WordTrace tailWord_5249988 prefixEnd_5249988 99843232382841134500213 := by
  unfold tailWord_5249988
  simp only [CollatzResearch.WordTrace]
  refine ⟨95741396652098788705711309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127655195536131718274281745 95741396652098788705711309)
  ·
    refine ⟨35903023744537045764641741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95741396652098788705711309 35903023744537045764641741)
    ·
      refine ⟨13463633904201392161740653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35903023744537045764641741 13463633904201392161740653)
      ·
        refine ⟨5048862714075522060652745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13463633904201392161740653 5048862714075522060652745)
        ·
          refine ⟨3786647035556641545489559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5048862714075522060652745 3786647035556641545489559)
          ·
            refine ⟨5679970553334962318234339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786647035556641545489559 5679970553334962318234339)
            ·
              refine ⟨8519955830002443477351509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679970553334962318234339 8519955830002443477351509)
              ·
                refine ⟨99843232382841134500213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8519955830002443477351509 99843232382841134500213)
                ·
                  rfl

theorem cell23_5249988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 8].length) (baseStart_5249988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5249988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5249988 prefixEnd_5249988 := by exact prefixLift 5249988
  have htrace : WordTrace (prefixWord ++ tailWord_5249988) baseStart_5249988 baseEnd_5249988 := by
    simpa [prefixWord, tailWord_5249988, baseEnd_5249988] using wordTrace_append hprefix tailTrace_5249988
  have hstable : (prefixWord ++ tailWord_5249988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5249988).length < 2 ^ (prefixWord ++ tailWord_5249988).sum := by decide
  have hdescent : baseEnd_5249988 < baseStart_5249988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5249988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250007 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_5250007 : Nat := 118140960795 + 5250007 * 2 ^ 59
def prefixEnd_5250007 : Nat := 4983230072969 + 3 ^ 40 * 5250007 * 2
def baseEnd_5250007 : Nat := 2695777030469146057168163

theorem tailTrace_5250007 : CollatzResearch.WordTrace tailWord_5250007 prefixEnd_5250007 2695777030469146057168163 := by
  unfold tailWord_5250007
  simp only [CollatzResearch.WordTrace]
  refine ⟨191483486291128743656364275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127655657527419162437576183 191483486291128743656364275)
  ·
    refine ⟨287225229436693115484546413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191483486291128743656364275 287225229436693115484546413)
    ·
      refine ⟨107709461038759918306704905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287225229436693115484546413 107709461038759918306704905)
      ·
        refine ⟨80782095779069938730028679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107709461038759918306704905 80782095779069938730028679)
        ·
          refine ⟨121173143668604908095043019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80782095779069938730028679 121173143668604908095043019)
          ·
            refine ⟨181759715502907362142564529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121173143668604908095043019 181759715502907362142564529)
            ·
              refine ⟨136319786627180521606923397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181759715502907362142564529 136319786627180521606923397)
              ·
                refine ⟨25559959992596347801298137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136319786627180521606923397 25559959992596347801298137)
                ·
                  refine ⟨19169969994447260850973603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25559959992596347801298137 19169969994447260850973603)
                  ·
                    refine ⟨28754954991670891276460405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19169969994447260850973603 28754954991670891276460405)
                    ·
                      refine ⟨2695777030469146057168163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28754954991670891276460405 2695777030469146057168163)
                      ·
                        rfl

theorem cell23_5250007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_5250007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250007 prefixEnd_5250007 := by exact prefixLift 5250007
  have htrace : WordTrace (prefixWord ++ tailWord_5250007) baseStart_5250007 baseEnd_5250007 := by
    simpa [prefixWord, tailWord_5250007, baseEnd_5250007] using wordTrace_append hprefix tailTrace_5250007
  have hstable : (prefixWord ++ tailWord_5250007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250007).length < 2 ^ (prefixWord ++ tailWord_5250007).sum := by decide
  have hdescent : baseEnd_5250007 < baseStart_5250007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250017 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_5250017 : Nat := 118140960795 + 5250017 * 2 ^ 59
def prefixEnd_5250017 : Nat := 4983230072969 + 3 ^ 40 * 5250017 * 2
def baseEnd_5250017 : Nat := 2695782165275691018043117

theorem tailTrace_5250017 : CollatzResearch.WordTrace tailWord_5250017 prefixEnd_5250017 2695782165275691018043117 := by
  unfold tailWord_5250017
  simp only [CollatzResearch.WordTrace]
  refine ⟨191483851021092515364228305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127655900680728343576152203 191483851021092515364228305)
  ·
    refine ⟨143612888265819386523171229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191483851021092515364228305 143612888265819386523171229)
    ·
      refine ⟨53854833099682269946189211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143612888265819386523171229 53854833099682269946189211)
      ·
        refine ⟨80782249649523404919283817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53854833099682269946189211 80782249649523404919283817)
        ·
          refine ⟨60586687237142553689462863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80782249649523404919283817 60586687237142553689462863)
          ·
            refine ⟨90880030855713830534194295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60586687237142553689462863 90880030855713830534194295)
            ·
              refine ⟨136320046283570745801291443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90880030855713830534194295 136320046283570745801291443)
              ·
                refine ⟨204480069425356118701937165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136320046283570745801291443 204480069425356118701937165)
                ·
                  refine ⟨76680026034508544513226437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204480069425356118701937165 76680026034508544513226437)
                  ·
                    refine ⟨14377504881470352096229957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76680026034508544513226437 14377504881470352096229957)
                    ·
                      refine ⟨2695782165275691018043117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14377504881470352096229957 2695782165275691018043117)
                      ·
                        rfl

theorem cell23_5250017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_5250017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250017 prefixEnd_5250017 := by exact prefixLift 5250017
  have htrace : WordTrace (prefixWord ++ tailWord_5250017) baseStart_5250017 baseEnd_5250017 := by
    simpa [prefixWord, tailWord_5250017, baseEnd_5250017] using wordTrace_append hprefix tailTrace_5250017
  have hstable : (prefixWord ++ tailWord_5250017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250017).length < 2 ^ (prefixWord ++ tailWord_5250017).sum := by decide
  have hdescent : baseEnd_5250017 < baseStart_5250017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250044 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 7]
def baseStart_5250044 : Nat := 118140960795 + 5250044 * 2 ^ 59
def prefixEnd_5250044 : Nat := 4983230072969 + 3 ^ 40 * 5250044 * 2
def baseEnd_5250044 : Nat := 299532892139262490267277

theorem tailTrace_5250044 : CollatzResearch.WordTrace tailWord_5250044 prefixEnd_5250044 299532892139262490267277 := by
  unfold tailWord_5250044
  simp only [CollatzResearch.WordTrace]
  refine ⟨95742417895997349487730593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127656557194663132650307457 95742417895997349487730593)
  ·
    refine ⟨71806813421998012115797945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95742417895997349487730593 71806813421998012115797945)
    ·
      refine ⟨53855110066498509086848459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71806813421998012115797945 53855110066498509086848459)
      ·
        refine ⟨80782665099747763630272689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53855110066498509086848459 80782665099747763630272689)
        ·
          refine ⟨60586998824810822722704517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80782665099747763630272689 60586998824810822722704517)
          ·
            refine ⟨11360062279652029260507097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60586998824810822722704517 11360062279652029260507097)
            ·
              refine ⟨8520046709739021945380323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11360062279652029260507097 8520046709739021945380323)
              ·
                refine ⟨12780070064608532918070485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8520046709739021945380323 12780070064608532918070485)
                ·
                  refine ⟨299532892139262490267277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12780070064608532918070485 299532892139262490267277)
                  ·
                    rfl

theorem cell23_5250044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_5250044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250044 prefixEnd_5250044 := by exact prefixLift 5250044
  have htrace : WordTrace (prefixWord ++ tailWord_5250044) baseStart_5250044 baseEnd_5250044 := by
    simpa [prefixWord, tailWord_5250044, baseEnd_5250044] using wordTrace_append hprefix tailTrace_5250044
  have hstable : (prefixWord ++ tailWord_5250044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250044).length < 2 ^ (prefixWord ++ tailWord_5250044).sum := by decide
  have hdescent : baseEnd_5250044 < baseStart_5250044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250055 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_5250055 : Nat := 118140960795 + 5250055 * 2 ^ 59
def prefixEnd_5250055 : Nat := 4983230072969 + 3 ^ 40 * 5250055 * 2
def baseEnd_5250055 : Nat := 2695801677540561869367943

theorem tailTrace_5250055 : CollatzResearch.WordTrace tailWord_5250055 prefixEnd_5250055 2695801677540561869367943 := by
  unfold tailWord_5250055
  simp only [CollatzResearch.WordTrace]
  refine ⟨191485236994954847854111619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127656824663303231902741079 191485236994954847854111619)
  ·
    refine ⟨287227855492432271781167429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191485236994954847854111619 287227855492432271781167429)
    ·
      refine ⟨53855222904831050958968893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287227855492432271781167429 53855222904831050958968893)
      ·
        refine ⟨20195708589311644109613335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53855222904831050958968893 20195708589311644109613335)
        ·
          refine ⟨30293562883967466164420003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20195708589311644109613335 30293562883967466164420003)
          ·
            refine ⟨45440344325951199246630005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30293562883967466164420003 45440344325951199246630005)
            ·
              refine ⟨4260032280557924929371563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45440344325951199246630005 4260032280557924929371563)
              ·
                refine ⟨6390048420836887394057345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260032280557924929371563 6390048420836887394057345)
                ·
                  refine ⟨4792536315627665545543009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390048420836887394057345 4792536315627665545543009)
                  ·
                    refine ⟨3594402236720749159157257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4792536315627665545543009 3594402236720749159157257)
                    ·
                      refine ⟨2695801677540561869367943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594402236720749159157257 2695801677540561869367943)
                      ·
                        rfl

theorem cell23_5250055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_5250055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250055 prefixEnd_5250055 := by exact prefixLift 5250055
  have htrace : WordTrace (prefixWord ++ tailWord_5250055) baseStart_5250055 baseEnd_5250055 := by
    simpa [prefixWord, tailWord_5250055, baseEnd_5250055] using wordTrace_append hprefix tailTrace_5250055
  have hstable : (prefixWord ++ tailWord_5250055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250055).length < 2 ^ (prefixWord ++ tailWord_5250055).sum := by decide
  have hdescent : baseEnd_5250055 < baseStart_5250055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250067 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_5250067 : Nat := 118140960795 + 5250067 * 2 ^ 59
def prefixEnd_5250067 : Nat := 4983230072969 + 3 ^ 40 * 5250067 * 2
def baseEnd_5250067 : Nat := 2695807839308415822417887

theorem tailTrace_5250067 : CollatzResearch.WordTrace tailWord_5250067 prefixEnd_5250067 2695807839308415822417887 := by
  unfold tailWord_5250067
  simp only [CollatzResearch.WordTrace]
  refine ⟨191485674670911373903548455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127657116447274249269032303 191485674670911373903548455)
  ·
    refine ⟨287228512006367060855322683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191485674670911373903548455 287228512006367060855322683)
    ·
      refine ⟨430842768009550591282984025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287228512006367060855322683 430842768009550591282984025)
      ·
        refine ⟨323132076007162943462238019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430842768009550591282984025 323132076007162943462238019)
        ·
          refine ⟨484698114010744415193357029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323132076007162943462238019 484698114010744415193357029)
          ·
            refine ⟨90880896377014577848754443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 484698114010744415193357029 90880896377014577848754443)
            ·
              refine ⟨136321344565521866773131665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90880896377014577848754443 136321344565521866773131665)
              ·
                refine ⟨102241008424141400079848749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136321344565521866773131665 102241008424141400079848749)
                ·
                  refine ⟨38340378159053025029943281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102241008424141400079848749 38340378159053025029943281)
                  ·
                    refine ⟨28755283619289768772457461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38340378159053025029943281 28755283619289768772457461)
                    ·
                      refine ⟨2695807839308415822417887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28755283619289768772457461 2695807839308415822417887)
                      ·
                        rfl

theorem cell23_5250067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_5250067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250067 prefixEnd_5250067 := by exact prefixLift 5250067
  have htrace : WordTrace (prefixWord ++ tailWord_5250067) baseStart_5250067 baseEnd_5250067 := by
    simpa [prefixWord, tailWord_5250067, baseEnd_5250067] using wordTrace_append hprefix tailTrace_5250067
  have hstable : (prefixWord ++ tailWord_5250067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250067).length < 2 ^ (prefixWord ++ tailWord_5250067).sum := by decide
  have hdescent : baseEnd_5250067 < baseStart_5250067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250074 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_5250074 : Nat := 118140960795 + 5250074 * 2 ^ 59
def prefixEnd_5250074 : Nat := 4983230072969 + 3 ^ 40 * 5250074 * 2
def baseEnd_5250074 : Nat := 898603811224332431676785

theorem tailTrace_5250074 : CollatzResearch.WordTrace tailWord_5250074 prefixEnd_5250074 898603811224332431676785 := by
  unfold tailWord_5250074
  simp only [CollatzResearch.WordTrace]
  refine ⟨47871482495471503524763319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127657286654590676066035517 47871482495471503524763319)
  ·
    refine ⟨71807223743207255287144979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47871482495471503524763319 71807223743207255287144979)
    ·
      refine ⟨107710835614810882930717469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71807223743207255287144979 107710835614810882930717469)
      ·
        refine ⟨40391563355554081099019051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107710835614810882930717469 40391563355554081099019051)
        ·
          refine ⟨60587345033331121648528577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40391563355554081099019051 60587345033331121648528577)
          ·
            refine ⟨45440508774998341236396433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60587345033331121648528577 45440508774998341236396433)
            ·
              refine ⟨34080381581248755927297325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45440508774998341236396433 34080381581248755927297325)
              ·
                refine ⟨12780143092968283472736497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34080381581248755927297325 12780143092968283472736497)
                ·
                  refine ⟨9585107319726212604552373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12780143092968283472736497 9585107319726212604552373)
                  ·
                    refine ⟨898603811224332431676785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9585107319726212604552373 898603811224332431676785)
                    ·
                      rfl

theorem cell23_5250074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_5250074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250074 prefixEnd_5250074 := by exact prefixLift 5250074
  have htrace : WordTrace (prefixWord ++ tailWord_5250074) baseStart_5250074 baseEnd_5250074 := by
    simpa [prefixWord, tailWord_5250074, baseEnd_5250074] using wordTrace_append hprefix tailTrace_5250074
  have hstable : (prefixWord ++ tailWord_5250074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250074).length < 2 ^ (prefixWord ++ tailWord_5250074).sum := by decide
  have hdescent : baseEnd_5250074 < baseStart_5250074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250127 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_5250127 : Nat := 118140960795 + 5250127 * 2 ^ 59
def prefixEnd_5250127 : Nat := 4983230072969 + 3 ^ 40 * 5250127 * 2
def baseEnd_5250127 : Nat := 2695838648147685587667611

theorem tailTrace_5250127 : CollatzResearch.WordTrace tailWord_5250127 prefixEnd_5250127 2695838648147685587667611 := by
  unfold tailWord_5250127
  simp only [CollatzResearch.WordTrace]
  refine ⟨191487863050694004150732635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127658575367129336100488423 191487863050694004150732635)
  ·
    refine ⟨287231794576041006226098953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191487863050694004150732635 287231794576041006226098953)
    ·
      refine ⟨215423845932030754669574215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287231794576041006226098953 215423845932030754669574215)
      ·
        refine ⟨323135768898046132004361323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215423845932030754669574215 323135768898046132004361323)
        ·
          refine ⟨484703653347069198006541985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323135768898046132004361323 484703653347069198006541985)
          ·
            refine ⟨363527740010301898504906489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484703653347069198006541985 363527740010301898504906489)
            ·
              refine ⟨272645805007726423878679867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363527740010301898504906489 272645805007726423878679867)
              ·
                refine ⟨408968707511589635818019801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272645805007726423878679867 408968707511589635818019801)
                ·
                  refine ⟨306726530633692226863514851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408968707511589635818019801 306726530633692226863514851)
                  ·
                    refine ⟨460089795950538340295272277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306726530633692226863514851 460089795950538340295272277)
                    ·
                      refine ⟨2695838648147685587667611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 460089795950538340295272277 2695838648147685587667611)
                      ·
                        rfl

theorem cell23_5250127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_5250127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250127 prefixEnd_5250127 := by exact prefixLift 5250127
  have htrace : WordTrace (prefixWord ++ tailWord_5250127) baseStart_5250127 baseEnd_5250127 := by
    simpa [prefixWord, tailWord_5250127, baseEnd_5250127] using wordTrace_append hprefix tailTrace_5250127
  have hstable : (prefixWord ++ tailWord_5250127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250127).length < 2 ^ (prefixWord ++ tailWord_5250127).sum := by decide
  have hdescent : baseEnd_5250127 < baseStart_5250127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250151 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 6]
def baseStart_5250151 : Nat := 118140960795 + 5250151 * 2 ^ 59
def prefixEnd_5250151 : Nat := 4983230072969 + 3 ^ 40 * 5250151 * 2
def baseEnd_5250151 : Nat := 299538996853710388196389

theorem tailTrace_5250151 : CollatzResearch.WordTrace tailWord_5250151 prefixEnd_5250151 299538996853710388196389 := by
  unfold tailWord_5250151
  simp only [CollatzResearch.WordTrace]
  refine ⟨191488738402607056249606307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127659158935071370833070871 191488738402607056249606307)
  ·
    refine ⟨287233107603910584374409461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191488738402607056249606307 287233107603910584374409461)
    ·
      refine ⟨26928103837866617285100887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287233107603910584374409461 26928103837866617285100887)
      ·
        refine ⟨40392155756799925927651331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26928103837866617285100887 40392155756799925927651331)
        ·
          refine ⟨60588233635199888891476997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40392155756799925927651331 60588233635199888891476997)
          ·
            refine ⟨11360293806599979167151937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60588233635199888891476997 11360293806599979167151937)
            ·
              refine ⟨8520220354949984375363953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11360293806599979167151937 8520220354949984375363953)
              ·
                refine ⟨6390165266212488281522965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8520220354949984375363953 6390165266212488281522965)
                ·
                  refine ⟨299538996853710388196389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6390165266212488281522965 299538996853710388196389)
                  ·
                    rfl

theorem cell23_5250151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 6].length) (baseStart_5250151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250151 prefixEnd_5250151 := by exact prefixLift 5250151
  have htrace : WordTrace (prefixWord ++ tailWord_5250151) baseStart_5250151 baseEnd_5250151 := by
    simpa [prefixWord, tailWord_5250151, baseEnd_5250151] using wordTrace_append hprefix tailTrace_5250151
  have hstable : (prefixWord ++ tailWord_5250151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250151).length < 2 ^ (prefixWord ++ tailWord_5250151).sum := by decide
  have hdescent : baseEnd_5250151 < baseStart_5250151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250171 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 4, 3, 2]
def baseStart_5250171 : Nat := 118140960795 + 5250171 * 2 ^ 59
def prefixEnd_5250171 : Nat := 4983230072969 + 3 ^ 40 * 5250171 * 2
def baseEnd_5250171 : Nat := 2695861241296483415517409

theorem tailTrace_5250171 : CollatzResearch.WordTrace tailWord_5250171 prefixEnd_5250171 2695861241296483415517409 := by
  unfold tailWord_5250171
  simp only [CollatzResearch.WordTrace]
  refine ⟨191489467862534599665334367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127659645241689733110222911 191489467862534599665334367)
  ·
    refine ⟨287234201793801899498001551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191489467862534599665334367 287234201793801899498001551)
    ·
      refine ⟨430851302690702849247002327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287234201793801899498001551 430851302690702849247002327)
      ·
        refine ⟨646276954036054273870503491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430851302690702849247002327 646276954036054273870503491)
        ·
          refine ⟨969415431054081410805755237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646276954036054273870503491 969415431054081410805755237)
          ·
            refine ⟨181765393322640264526079107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 969415431054081410805755237 181765393322640264526079107)
            ·
              refine ⟨272648089983960396789118661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181765393322640264526079107 272648089983960396789118661)
              ·
                refine ⟨51121516871992574397959749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272648089983960396789118661 51121516871992574397959749)
                ·
                  refine ⟨9585284413498607699617453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51121516871992574397959749 9585284413498607699617453)
                  ·
                    refine ⟨3594481655061977887356545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9585284413498607699617453 3594481655061977887356545)
                    ·
                      refine ⟨2695861241296483415517409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594481655061977887356545 2695861241296483415517409)
                      ·
                        rfl

theorem cell23_5250171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3, 2].length) (baseStart_5250171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250171 prefixEnd_5250171 := by exact prefixLift 5250171
  have htrace : WordTrace (prefixWord ++ tailWord_5250171) baseStart_5250171 baseEnd_5250171 := by
    simpa [prefixWord, tailWord_5250171, baseEnd_5250171] using wordTrace_append hprefix tailTrace_5250171
  have hstable : (prefixWord ++ tailWord_5250171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250171).length < 2 ^ (prefixWord ++ tailWord_5250171).sum := by decide
  have hdescent : baseEnd_5250171 < baseStart_5250171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250269 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5250269 : Nat := 118140960795 + 5250269 * 2 ^ 59
def prefixEnd_5250269 : Nat := 4983230072969 + 3 ^ 40 * 5250269 * 2
def baseEnd_5250269 : Nat := 2695911562400624032091959

theorem tailTrace_5250269 : CollatzResearch.WordTrace tailWord_5250269 prefixEnd_5250269 2695911562400624032091959 := by
  unfold tailWord_5250269
  simp only [CollatzResearch.WordTrace]
  refine ⟨191493042216179562402401861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127662028144119708268267907 191493042216179562402401861)
  ·
    refine ⟨35904945415533667950450349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191493042216179562402401861 35904945415533667950450349)
    ·
      refine ⟨13464354530825125481418881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35904945415533667950450349 13464354530825125481418881)
      ·
        refine ⟨10098265898118844111064161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13464354530825125481418881 10098265898118844111064161)
        ·
          refine ⟨7573699423589133083298121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10098265898118844111064161 7573699423589133083298121)
          ·
            refine ⟨5680274567691849812473591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7573699423589133083298121 5680274567691849812473591)
            ·
              refine ⟨8520411851537774718710387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680274567691849812473591 8520411851537774718710387)
              ·
                refine ⟨12780617777306662078065581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8520411851537774718710387 12780617777306662078065581)
                ·
                  refine ⟨4792731666489998279274593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12780617777306662078065581 4792731666489998279274593)
                  ·
                    refine ⟨3594548749867498709455945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4792731666489998279274593 3594548749867498709455945)
                    ·
                      refine ⟨2695911562400624032091959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594548749867498709455945 2695911562400624032091959)
                      ·
                        rfl

theorem cell23_5250269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5250269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250269 prefixEnd_5250269 := by exact prefixLift 5250269
  have htrace : WordTrace (prefixWord ++ tailWord_5250269) baseStart_5250269 baseEnd_5250269 := by
    simpa [prefixWord, tailWord_5250269, baseEnd_5250269] using wordTrace_append hprefix tailTrace_5250269
  have hstable : (prefixWord ++ tailWord_5250269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250269).length < 2 ^ (prefixWord ++ tailWord_5250269).sum := by decide
  have hdescent : baseEnd_5250269 < baseStart_5250269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250279 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 2, 4]
def baseStart_5250279 : Nat := 118140960795 + 5250279 * 2 ^ 59
def prefixEnd_5250279 : Nat := 4983230072969 + 3 ^ 40 * 5250279 * 2
def baseEnd_5250279 : Nat := 898638899069056330988971

theorem tailTrace_5250279 : CollatzResearch.WordTrace tailWord_5250279 prefixEnd_5250279 898638899069056330988971 := by
  unfold tailWord_5250279
  simp only [CollatzResearch.WordTrace]
  refine ⟨191493406946143334110265891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127662271297428889406843927 191493406946143334110265891)
  ·
    refine ⟨287240110419215001165398837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191493406946143334110265891 287240110419215001165398837)
    ·
      refine ⟨26928760351801406359256141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287240110419215001165398837 26928760351801406359256141)
      ·
        refine ⟨10098285131925527384721053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26928760351801406359256141 10098285131925527384721053)
        ·
          refine ⟨3786856924472072769270395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10098285131925527384721053 3786856924472072769270395)
          ·
            refine ⟨5680285386708109153905593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786856924472072769270395 5680285386708109153905593)
            ·
              refine ⟨4260214040031081865429195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5680285386708109153905593 4260214040031081865429195)
              ·
                refine ⟨6390321060046622798143793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260214040031081865429195 6390321060046622798143793)
                ·
                  refine ⟨4792740795034967098607845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390321060046622798143793 4792740795034967098607845)
                  ·
                    refine ⟨898638899069056330988971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792740795034967098607845 898638899069056330988971)
                    ·
                      rfl

theorem cell23_5250279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_5250279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250279 prefixEnd_5250279 := by exact prefixLift 5250279
  have htrace : WordTrace (prefixWord ++ tailWord_5250279) baseStart_5250279 baseEnd_5250279 := by
    simpa [prefixWord, tailWord_5250279, baseEnd_5250279] using wordTrace_append hprefix tailTrace_5250279
  have hstable : (prefixWord ++ tailWord_5250279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250279).length < 2 ^ (prefixWord ++ tailWord_5250279).sum := by decide
  have hdescent : baseEnd_5250279 < baseStart_5250279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250321 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_5250321 : Nat := 118140960795 + 5250321 * 2 ^ 59
def prefixEnd_5250321 : Nat := 4983230072969 + 3 ^ 40 * 5250321 * 2
def baseEnd_5250321 : Nat := 2695938263394657828641719

theorem tailTrace_5250321 : CollatzResearch.WordTrace tailWord_5250321 prefixEnd_5250321 2695938263394657828641719 := by
  unfold tailWord_5250321
  simp only [CollatzResearch.WordTrace]
  refine ⟨191494938811991175283294817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127663292541327450188863211 191494938811991175283294817)
  ·
    refine ⟨143621204108993381462471113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191494938811991175283294817 143621204108993381462471113)
    ·
      refine ⟨107715903081745036096853335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143621204108993381462471113 107715903081745036096853335)
      ·
        refine ⟨161573854622617554145280003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107715903081745036096853335 161573854622617554145280003)
        ·
          refine ⟨242360781933926331217920005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161573854622617554145280003 242360781933926331217920005)
          ·
            refine ⟨45442646612611187103360001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242360781933926331217920005 45442646612611187103360001)
            ·
              refine ⟨34081984959458390327520001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45442646612611187103360001 34081984959458390327520001)
              ·
                refine ⟨25561488719593792745640001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34081984959458390327520001 25561488719593792745640001)
                ·
                  refine ⟨19171116539695344559230001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25561488719593792745640001 19171116539695344559230001)
                  ·
                    refine ⟨14378337404771508419422501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19171116539695344559230001 14378337404771508419422501)
                    ·
                      refine ⟨2695938263394657828641719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14378337404771508419422501 2695938263394657828641719)
                      ·
                        rfl

theorem cell23_5250321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_5250321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250321 prefixEnd_5250321 := by exact prefixLift 5250321
  have htrace : WordTrace (prefixWord ++ tailWord_5250321) baseStart_5250321 baseEnd_5250321 := by
    simpa [prefixWord, tailWord_5250321, baseEnd_5250321] using wordTrace_append hprefix tailTrace_5250321
  have hstable : (prefixWord ++ tailWord_5250321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250321).length < 2 ^ (prefixWord ++ tailWord_5250321).sum := by decide
  have hdescent : baseEnd_5250321 < baseStart_5250321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250418 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_5250418 : Nat := 118140960795 + 5250418 * 2 ^ 59
def prefixEnd_5250418 : Nat := 4983230072969 + 3 ^ 40 * 5250418 * 2
def baseEnd_5250418 : Nat := 2695988071018143949128773

theorem tailTrace_5250418 : CollatzResearch.WordTrace tailWord_5250418 prefixEnd_5250418 2695988071018143949128773 := by
  unfold tailWord_5250418
  simp only [CollatzResearch.WordTrace]
  refine ⟨47874619173159940212393977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127665651128426507233050605 47874619173159940212393977)
  ·
    refine ⟨35905964379869955159295483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47874619173159940212393977 35905964379869955159295483)
    ·
      refine ⟨53858946569804932738943225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35905964379869955159295483 53858946569804932738943225)
      ·
        refine ⟨40394209927353699554207419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53858946569804932738943225 40394209927353699554207419)
        ·
          refine ⟨60591314891030549331311129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40394209927353699554207419 60591314891030549331311129)
          ·
            refine ⟨45443486168272911998483347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60591314891030549331311129 45443486168272911998483347)
            ·
              refine ⟨68165229252409367997725021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45443486168272911998483347 68165229252409367997725021)
              ·
                refine ⟨25561960969653512999146883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68165229252409367997725021 25561960969653512999146883)
                ·
                  refine ⟨38342941454480269498720325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25561960969653512999146883 38342941454480269498720325)
                  ·
                    refine ⟨7189301522715050531010061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38342941454480269498720325 7189301522715050531010061)
                    ·
                      refine ⟨2695988071018143949128773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7189301522715050531010061 2695988071018143949128773)
                      ·
                        rfl

theorem cell23_5250418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_5250418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250418 prefixEnd_5250418 := by exact prefixLift 5250418
  have htrace : WordTrace (prefixWord ++ tailWord_5250418) baseStart_5250418 baseEnd_5250418 := by
    simpa [prefixWord, tailWord_5250418, baseEnd_5250418] using wordTrace_append hprefix tailTrace_5250418
  have hstable : (prefixWord ++ tailWord_5250418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250418).length < 2 ^ (prefixWord ++ tailWord_5250418).sum := by decide
  have hdescent : baseEnd_5250418 < baseStart_5250418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250435 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 3]
def baseStart_5250435 : Nat := 118140960795 + 5250435 * 2 ^ 59
def prefixEnd_5250435 : Nat := 4983230072969 + 3 ^ 40 * 5250435 * 2
def baseEnd_5250435 : Nat := 2695996800189270382616195

theorem tailTrace_5250435 : CollatzResearch.WordTrace tailWord_5250435 prefixEnd_5250435 2695996800189270382616195 := by
  unfold tailWord_5250435
  simp only [CollatzResearch.WordTrace]
  refine ⟨191499096733578172752944759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127666064489052115168629839 191499096733578172752944759)
  ·
    refine ⟨287248645100367259129417139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191499096733578172752944759 287248645100367259129417139)
    ·
      refine ⟨430872967650550888694125709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287248645100367259129417139 430872967650550888694125709)
      ·
        refine ⟨161577362868956583260297141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430872967650550888694125709 161577362868956583260297141)
        ·
          refine ⟨15147877768964679680652857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161577362868956583260297141 15147877768964679680652857)
          ·
            refine ⟨11360908326723509760489643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15147877768964679680652857 11360908326723509760489643)
            ·
              refine ⟨17041362490085264640734465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11360908326723509760489643 17041362490085264640734465)
              ·
                refine ⟨12781021867563948480550849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17041362490085264640734465 12781021867563948480550849)
                ·
                  refine ⟨9585766400672961360413137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12781021867563948480550849 9585766400672961360413137)
                  ·
                    refine ⟨7189324800504721020309853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9585766400672961360413137 7189324800504721020309853)
                    ·
                      refine ⟨2695996800189270382616195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7189324800504721020309853 2695996800189270382616195)
                      ·
                        rfl

theorem cell23_5250435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_5250435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250435 prefixEnd_5250435 := by exact prefixLift 5250435
  have htrace : WordTrace (prefixWord ++ tailWord_5250435) baseStart_5250435 baseEnd_5250435 := by
    simpa [prefixWord, tailWord_5250435, baseEnd_5250435] using wordTrace_append hprefix tailTrace_5250435
  have hstable : (prefixWord ++ tailWord_5250435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250435).length < 2 ^ (prefixWord ++ tailWord_5250435).sum := by decide
  have hdescent : baseEnd_5250435 < baseStart_5250435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250499 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 1, 1, 3]
def baseStart_5250499 : Nat := 118140960795 + 5250499 * 2 ^ 59
def prefixEnd_5250499 : Nat := 4983230072969 + 3 ^ 40 * 5250499 * 2
def baseEnd_5250499 : Nat := 2696029662951158132215901

theorem tailTrace_5250499 : CollatzResearch.WordTrace tailWord_5250499 prefixEnd_5250499 2696029662951158132215901 := by
  unfold tailWord_5250499
  simp only [CollatzResearch.WordTrace]
  refine ⟨191501431005346311683274551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127667620670230874455516367 191501431005346311683274551)
  ·
    refine ⟨287252146508019467524911827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191501431005346311683274551 287252146508019467524911827)
    ·
      refine ⟨430878219762029201287367741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287252146508019467524911827 430878219762029201287367741)
      ·
        refine ⟨161579332410760950482762903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430878219762029201287367741 161579332410760950482762903)
        ·
          refine ⟨242368998616141425724144355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161579332410760950482762903 242368998616141425724144355)
          ·
            refine ⟨363553497924212138586216533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242368998616141425724144355 363553497924212138586216533)
            ·
              refine ⟨4260392553799360999057225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 363553497924212138586216533 4260392553799360999057225)
              ·
                refine ⟨3195294415349520749292919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4260392553799360999057225 3195294415349520749292919)
                ·
                  refine ⟨4792941623024281123939379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195294415349520749292919 4792941623024281123939379)
                  ·
                    refine ⟨7189412434536421685909069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4792941623024281123939379 7189412434536421685909069)
                    ·
                      refine ⟨2696029662951158132215901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7189412434536421685909069 2696029662951158132215901)
                      ·
                        rfl

theorem cell23_5250499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_5250499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250499 prefixEnd_5250499 := by exact prefixLift 5250499
  have htrace : WordTrace (prefixWord ++ tailWord_5250499) baseStart_5250499 baseEnd_5250499 := by
    simpa [prefixWord, tailWord_5250499, baseEnd_5250499] using wordTrace_append hprefix tailTrace_5250499
  have hstable : (prefixWord ++ tailWord_5250499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250499).length < 2 ^ (prefixWord ++ tailWord_5250499).sum := by decide
  have hdescent : baseEnd_5250499 < baseStart_5250499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250522 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2]
def baseStart_5250522 : Nat := 118140960795 + 5250522 * 2 ^ 59
def prefixEnd_5250522 : Nat := 4983230072969 + 3 ^ 40 * 5250522 * 2
def baseEnd_5250522 : Nat := 2696041473006211542228295

theorem tailTrace_5250522 : CollatzResearch.WordTrace tailWord_5250522 prefixEnd_5250522 2696041473006211542228295 := by
  unfold tailWord_5250522
  simp only [CollatzResearch.WordTrace]
  refine ⟨47875567471065746652840455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127668179922841991074241213 47875567471065746652840455)
  ·
    refine ⟨71813351206598619979260683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47875567471065746652840455 71813351206598619979260683)
    ·
      refine ⟨107720026809897929968891025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71813351206598619979260683 107720026809897929968891025)
      ·
        refine ⟨80790020107423447476668269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107720026809897929968891025 80790020107423447476668269)
        ·
          refine ⟨30296257540283792803750601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80790020107423447476668269 30296257540283792803750601)
          ·
            refine ⟨22722193155212844602812951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30296257540283792803750601 22722193155212844602812951)
            ·
              refine ⟨34083289732819266904219427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22722193155212844602812951 34083289732819266904219427)
              ·
                refine ⟨51124934599228900356329141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34083289732819266904219427 51124934599228900356329141)
                ·
                  refine ⟨4792962618677709408405857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51124934599228900356329141 4792962618677709408405857)
                  ·
                    refine ⟨3594721964008282056304393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4792962618677709408405857 3594721964008282056304393)
                    ·
                      refine ⟨2696041473006211542228295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594721964008282056304393 2696041473006211542228295)
                      ·
                        rfl

theorem cell23_5250522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_5250522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250522 prefixEnd_5250522 := by exact prefixLift 5250522
  have htrace : WordTrace (prefixWord ++ tailWord_5250522) baseStart_5250522 baseEnd_5250522 := by
    simpa [prefixWord, tailWord_5250522, baseEnd_5250522] using wordTrace_append hprefix tailTrace_5250522
  have hstable : (prefixWord ++ tailWord_5250522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250522).length < 2 ^ (prefixWord ++ tailWord_5250522).sum := by decide
  have hdescent : baseEnd_5250522 < baseStart_5250522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250535 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5250535 : Nat := 118140960795 + 5250535 * 2 ^ 59
def prefixEnd_5250535 : Nat := 4983230072969 + 3 ^ 40 * 5250535 * 2
def baseEnd_5250535 : Nat := 2696048148254719991365735

theorem tailTrace_5250535 : CollatzResearch.WordTrace tailWord_5250535 prefixEnd_5250535 2696048148254719991365735 := by
  unfold tailWord_5250535
  simp only [CollatzResearch.WordTrace]
  refine ⟨191502744033215889831585059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127668496022143926554390039 191502744033215889831585059)
  ·
    refine ⟨287254116049823834747377589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191502744033215889831585059 287254116049823834747377589)
    ·
      refine ⟨26930073379670984507566649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287254116049823834747377589 26930073379670984507566649)
      ·
        refine ⟨20197555034753238380674987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26930073379670984507566649 20197555034753238380674987)
        ·
          refine ⟨30296332552129857571012481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20197555034753238380674987 30296332552129857571012481)
          ·
            refine ⟨22722249414097393178259361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30296332552129857571012481 22722249414097393178259361)
            ·
              refine ⟨17041687060573044883694521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22722249414097393178259361 17041687060573044883694521)
              ·
                refine ⟨12781265295429783662770891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17041687060573044883694521 12781265295429783662770891)
                ·
                  refine ⟨19171897943144675494156337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12781265295429783662770891 19171897943144675494156337)
                  ·
                    refine ⟨14378923457358506620617253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19171897943144675494156337 14378923457358506620617253)
                    ·
                      refine ⟨2696048148254719991365735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14378923457358506620617253 2696048148254719991365735)
                      ·
                        rfl

theorem cell23_5250535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5250535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250535 prefixEnd_5250535 := by exact prefixLift 5250535
  have htrace : WordTrace (prefixWord ++ tailWord_5250535) baseStart_5250535 baseEnd_5250535 := by
    simpa [prefixWord, tailWord_5250535, baseEnd_5250535] using wordTrace_append hprefix tailTrace_5250535
  have hstable : (prefixWord ++ tailWord_5250535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250535).length < 2 ^ (prefixWord ++ tailWord_5250535).sum := by decide
  have hdescent : baseEnd_5250535 < baseStart_5250535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250542 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_5250542 : Nat := 118140960795 + 5250542 * 2 ^ 59
def prefixEnd_5250542 : Nat := 4983230072969 + 3 ^ 40 * 5250542 * 2
def baseEnd_5250542 : Nat := 2696051742619301463978203

theorem tailTrace_5250542 : CollatzResearch.WordTrace tailWord_5250542 prefixEnd_5250542 2696051742619301463978203 := by
  unfold tailWord_5250542
  simp only [CollatzResearch.WordTrace]
  refine ⟨23937874918023816253386235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127668666229460353351393253 23937874918023816253386235)
  ·
    refine ⟨35906812377035724380079353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23937874918023816253386235 35906812377035724380079353)
    ·
      refine ⟨26930109282776793285059515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35906812377035724380079353 26930109282776793285059515)
      ·
        refine ⟨40395163924165189927589273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26930109282776793285059515 40395163924165189927589273)
        ·
          refine ⟨30296372943123892445691955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40395163924165189927589273 30296372943123892445691955)
          ·
            refine ⟨45444559414685838668537933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30296372943123892445691955 45444559414685838668537933)
            ·
              refine ⟨17041709780507189500701725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45444559414685838668537933 17041709780507189500701725)
              ·
                refine ⟨6390641167690196062763147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17041709780507189500701725 6390641167690196062763147)
                ·
                  refine ⟨9585961751535294094144721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6390641167690196062763147 9585961751535294094144721)
                  ·
                    refine ⟨7189471313651470570608541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9585961751535294094144721 7189471313651470570608541)
                    ·
                      refine ⟨2696051742619301463978203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7189471313651470570608541 2696051742619301463978203)
                      ·
                        rfl

theorem cell23_5250542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_5250542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250542 prefixEnd_5250542 := by exact prefixLift 5250542
  have htrace : WordTrace (prefixWord ++ tailWord_5250542) baseStart_5250542 baseEnd_5250542 := by
    simpa [prefixWord, tailWord_5250542, baseEnd_5250542] using wordTrace_append hprefix tailTrace_5250542
  have hstable : (prefixWord ++ tailWord_5250542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250542).length < 2 ^ (prefixWord ++ tailWord_5250542).sum := by decide
  have hdescent : baseEnd_5250542 < baseStart_5250542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250549 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5250549 : Nat := 118140960795 + 5250549 * 2 ^ 59
def prefixEnd_5250549 : Nat := 4983230072969 + 3 ^ 40 * 5250549 * 2
def baseEnd_5250549 : Nat := 898685112327960978863557

theorem tailTrace_5250549 : CollatzResearch.WordTrace tailWord_5250549 prefixEnd_5250549 898685112327960978863557 := by
  unfold tailWord_5250549
  simp only [CollatzResearch.WordTrace]
  refine ⟨191503254655165170222594701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127668836436776780148396467 191503254655165170222594701)
  ·
    refine ⟨71813720495686938833473013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191503254655165170222594701 71813720495686938833473013)
    ·
      refine ⟨6732536296470650515638095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71813720495686938833473013 6732536296470650515638095)
      ·
        refine ⟨10098804444705975773457143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6732536296470650515638095 10098804444705975773457143)
        ·
          refine ⟨15148206667058963660185715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10098804444705975773457143 15148206667058963660185715)
          ·
            refine ⟨22722310000588445490278573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15148206667058963660185715 22722310000588445490278573)
            ·
              refine ⟨8520866250220667058854465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22722310000588445490278573 8520866250220667058854465)
              ·
                refine ⟨6390649687665500294140849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8520866250220667058854465 6390649687665500294140849)
                ·
                  refine ⟨4792987265749125220605637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390649687665500294140849 4792987265749125220605637)
                  ·
                    refine ⟨898685112327960978863557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792987265749125220605637 898685112327960978863557)
                    ·
                      rfl

theorem cell23_5250549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5250549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250549 prefixEnd_5250549 := by exact prefixLift 5250549
  have htrace : WordTrace (prefixWord ++ tailWord_5250549) baseStart_5250549 baseEnd_5250549 := by
    simpa [prefixWord, tailWord_5250549, baseEnd_5250549] using wordTrace_append hprefix tailTrace_5250549
  have hstable : (prefixWord ++ tailWord_5250549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250549).length < 2 ^ (prefixWord ++ tailWord_5250549).sum := by decide
  have hdescent : baseEnd_5250549 < baseStart_5250549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250555 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 3]
def baseStart_5250555 : Nat := 118140960795 + 5250555 * 2 ^ 59
def prefixEnd_5250555 : Nat := 4983230072969 + 3 ^ 40 * 5250555 * 2
def baseEnd_5250555 : Nat := 2696058417867809913115643

theorem tailTrace_5250555 : CollatzResearch.WordTrace tailWord_5250555 prefixEnd_5250555 2696058417867809913115643 := by
  unfold tailWord_5250555
  simp only [CollatzResearch.WordTrace]
  refine ⟨191503473493143433247313119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127668982328762288831542079 191503473493143433247313119)
  ·
    refine ⟨287255210239715149870969679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191503473493143433247313119 287255210239715149870969679)
    ·
      refine ⟨430882815359572724806454519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287255210239715149870969679 430882815359572724806454519)
      ·
        refine ⟨646324223039359087209681779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430882815359572724806454519 646324223039359087209681779)
        ·
          refine ⟨969486334559038630814522669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646324223039359087209681779 969486334559038630814522669)
          ·
            refine ⟨363557375459639486555446001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 969486334559038630814522669 363557375459639486555446001)
            ·
              refine ⟨272668031594729614916584501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363557375459639486555446001 272668031594729614916584501)
              ·
                refine ⟨25562627962005901398429797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 272668031594729614916584501 25562627962005901398429797)
                ·
                  refine ⟨4792992742876106512205587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25562627962005901398429797 4792992742876106512205587)
                  ·
                    refine ⟨7189489114314159768308381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4792992742876106512205587 7189489114314159768308381)
                    ·
                      refine ⟨2696058417867809913115643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7189489114314159768308381 2696058417867809913115643)
                      ·
                        rfl

theorem cell23_5250555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 3].length) (baseStart_5250555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250555 prefixEnd_5250555 := by exact prefixLift 5250555
  have htrace : WordTrace (prefixWord ++ tailWord_5250555) baseStart_5250555 baseEnd_5250555 := by
    simpa [prefixWord, tailWord_5250555, baseEnd_5250555] using wordTrace_append hprefix tailTrace_5250555
  have hstable : (prefixWord ++ tailWord_5250555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250555).length < 2 ^ (prefixWord ++ tailWord_5250555).sum := by decide
  have hdescent : baseEnd_5250555 < baseStart_5250555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250625 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5250625 : Nat := 118140960795 + 5250625 * 2 ^ 59
def prefixEnd_5250625 : Nat := 4983230072969 + 3 ^ 40 * 5250625 * 2
def baseEnd_5250625 : Nat := 2696094361513624639240321

theorem tailTrace_5250625 : CollatzResearch.WordTrace tailWord_5250625 prefixEnd_5250625 2696094361513624639240321 := by
  unfold tailWord_5250625
  simp only [CollatzResearch.WordTrace]
  refine ⟨191506026602889835202361329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127670684401926556801574219 191506026602889835202361329)
  ·
    refine ⟨143629519952167376401770997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191506026602889835202361329 143629519952167376401770997)
    ·
      refine ⟨13465267495515691537666031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143629519952167376401770997 13465267495515691537666031)
      ·
        refine ⟨20197901243273537306499047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13465267495515691537666031 20197901243273537306499047)
        ·
          refine ⟨30296851864910305959748571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20197901243273537306499047 30296851864910305959748571)
          ·
            refine ⟨45445277797365458939622857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30296851864910305959748571 45445277797365458939622857)
            ·
              refine ⟨34083958348024094204717143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45445277797365458939622857 34083958348024094204717143)
              ·
                refine ⟨51125937522036141307075715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34083958348024094204717143 51125937522036141307075715)
                ·
                  refine ⟨76688906283054211960613573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51125937522036141307075715 76688906283054211960613573)
                  ·
                    refine ⟨14379169928072664742615045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76688906283054211960613573 14379169928072664742615045)
                    ·
                      refine ⟨2696094361513624639240321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14379169928072664742615045 2696094361513624639240321)
                      ·
                        rfl

theorem cell23_5250625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5250625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250625 prefixEnd_5250625 := by exact prefixLift 5250625
  have htrace : WordTrace (prefixWord ++ tailWord_5250625) baseStart_5250625 baseEnd_5250625 := by
    simpa [prefixWord, tailWord_5250625, baseEnd_5250625] using wordTrace_append hprefix tailTrace_5250625
  have hstable : (prefixWord ++ tailWord_5250625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250625).length < 2 ^ (prefixWord ++ tailWord_5250625).sum := by decide
  have hdescent : baseEnd_5250625 < baseStart_5250625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250629 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 2, 2, 2]
def baseStart_5250629 : Nat := 118140960795 + 5250629 * 2 ^ 59
def prefixEnd_5250629 : Nat := 4983230072969 + 3 ^ 40 * 5250629 * 2
def baseEnd_5250629 : Nat := 2696096415436242623590303

theorem tailTrace_5250629 : CollatzResearch.WordTrace tailWord_5250629 prefixEnd_5250629 2696096415436242623590303 := by
  unfold tailWord_5250629
  simp only [CollatzResearch.WordTrace]
  refine ⟨191506172494875343885506941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127670781663250229257004627 191506172494875343885506941)
  ·
    refine ⟨71814814685578253957065103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191506172494875343885506941 71814814685578253957065103)
    ·
      refine ⟨107722222028367380935597655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71814814685578253957065103 107722222028367380935597655)
      ·
        refine ⟨161583333042551071403396483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107722222028367380935597655 161583333042551071403396483)
        ·
          refine ⟨242374999563826607105094725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161583333042551071403396483 242374999563826607105094725)
          ·
            refine ⟨45445312418217488832205261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242374999563826607105094725 45445312418217488832205261)
            ·
              refine ⟨17041992156831558312076973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45445312418217488832205261 17041992156831558312076973)
              ·
                refine ⟨6390747058811834367028865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17041992156831558312076973 6390747058811834367028865)
                ·
                  refine ⟨4793060294108875775271649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390747058811834367028865 4793060294108875775271649)
                  ·
                    refine ⟨3594795220581656831453737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4793060294108875775271649 3594795220581656831453737)
                    ·
                      refine ⟨2696096415436242623590303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594795220581656831453737 2696096415436242623590303)
                      ·
                        rfl

theorem cell23_5250629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_5250629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250629 prefixEnd_5250629 := by exact prefixLift 5250629
  have htrace : WordTrace (prefixWord ++ tailWord_5250629) baseStart_5250629 baseEnd_5250629 := by
    simpa [prefixWord, tailWord_5250629, baseEnd_5250629] using wordTrace_append hprefix tailTrace_5250629
  have hstable : (prefixWord ++ tailWord_5250629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250629).length < 2 ^ (prefixWord ++ tailWord_5250629).sum := by decide
  have hdescent : baseEnd_5250629 < baseStart_5250629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250645 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_5250645 : Nat := 118140960795 + 5250645 * 2 ^ 59
def prefixEnd_5250645 : Nat := 4983230072969 + 3 ^ 40 * 5250645 * 2
def baseEnd_5250645 : Nat := 2696104631126714560990229

theorem tailTrace_5250645 : CollatzResearch.WordTrace tailWord_5250645 prefixEnd_5250645 2696104631126714560990229 := by
  unfold tailWord_5250645
  simp only [CollatzResearch.WordTrace]
  refine ⟨191506756062817378618089389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127671170708544919078726259 191506756062817378618089389)
  ·
    refine ⟨71815033523556516981783521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191506756062817378618089389 71815033523556516981783521)
    ·
      refine ⟨53861275142667387736337641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71815033523556516981783521 53861275142667387736337641)
      ·
        refine ⟨40395956357000540802253231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53861275142667387736337641 40395956357000540802253231)
        ·
          refine ⟨60593934535500811203379847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40395956357000540802253231 60593934535500811203379847)
          ·
            refine ⟨90890901803251216805069771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60593934535500811203379847 90890901803251216805069771)
            ·
              refine ⟨136336352704876825207604657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90890901803251216805069771 136336352704876825207604657)
              ·
                refine ⟨102252264528657618905703493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136336352704876825207604657 102252264528657618905703493)
                ·
                  refine ⟨19172299599123303544819405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102252264528657618905703493 19172299599123303544819405)
                  ·
                    refine ⟨7189612349671238829307277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19172299599123303544819405 7189612349671238829307277)
                    ·
                      refine ⟨2696104631126714560990229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7189612349671238829307277 2696104631126714560990229)
                      ·
                        rfl

theorem cell23_5250645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_5250645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250645 prefixEnd_5250645 := by exact prefixLift 5250645
  have htrace : WordTrace (prefixWord ++ tailWord_5250645) baseStart_5250645 baseEnd_5250645 := by
    simpa [prefixWord, tailWord_5250645, baseEnd_5250645] using wordTrace_append hprefix tailTrace_5250645
  have hstable : (prefixWord ++ tailWord_5250645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250645).length < 2 ^ (prefixWord ++ tailWord_5250645).sum := by decide
  have hdescent : baseEnd_5250645 < baseStart_5250645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250665 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_5250665 : Nat := 118140960795 + 5250665 * 2 ^ 59
def prefixEnd_5250665 : Nat := 4983230072969 + 3 ^ 40 * 5250665 * 2
def baseEnd_5250665 : Nat := 898704966913268160913379

theorem tailTrace_5250665 : CollatzResearch.WordTrace tailWord_5250665 prefixEnd_5250665 898704966913268160913379 := by
  unfold tailWord_5250665
  simp only [CollatzResearch.WordTrace]
  refine ⟨191507485522744922033817449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127671657015163281355878299 191507485522744922033817449)
  ·
    refine ⟨143630614142058691525363087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191507485522744922033817449 143630614142058691525363087)
    ·
      refine ⟨215445921213088037288044631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143630614142058691525363087 215445921213088037288044631)
      ·
        refine ⟨323168881819632055932066947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215445921213088037288044631 323168881819632055932066947)
        ·
          refine ⟨484753322729448083898100421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323168881819632055932066947 484753322729448083898100421)
          ·
            refine ⟨90891248011771515730893829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 484753322729448083898100421 90891248011771515730893829)
            ·
              refine ⟨17042109002207159199542593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90891248011771515730893829 17042109002207159199542593)
              ·
                refine ⟨12781581751655369399656945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17042109002207159199542593 12781581751655369399656945)
                ·
                  refine ⟨9586186313741527049742709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12781581751655369399656945 9586186313741527049742709)
                  ·
                    refine ⟨898704966913268160913379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9586186313741527049742709 898704966913268160913379)
                    ·
                      rfl

theorem cell23_5250665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_5250665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250665 prefixEnd_5250665 := by exact prefixLift 5250665
  have htrace : WordTrace (prefixWord ++ tailWord_5250665) baseStart_5250665 baseEnd_5250665 := by
    simpa [prefixWord, tailWord_5250665, baseEnd_5250665] using wordTrace_append hprefix tailTrace_5250665
  have hstable : (prefixWord ++ tailWord_5250665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250665).length < 2 ^ (prefixWord ++ tailWord_5250665).sum := by decide
  have hdescent : baseEnd_5250665 < baseStart_5250665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250669 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 5]
def baseStart_5250669 : Nat := 118140960795 + 5250669 * 2 ^ 59
def prefixEnd_5250669 : Nat := 4983230072969 + 3 ^ 40 * 5250669 * 2
def baseEnd_5250669 : Nat := 299568550518046940787791

theorem tailTrace_5250669 : CollatzResearch.WordTrace tailWord_5250669 prefixEnd_5250669 299568550518046940787791 := by
  unfold tailWord_5250669
  simp only [CollatzResearch.WordTrace]
  refine ⟨191507631414730430716963061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127671754276486953811308707 191507631414730430716963061)
  ·
    refine ⟨17953840445130977879715287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191507631414730430716963061 17953840445130977879715287)
    ·
      refine ⟨26930760667696466819572931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17953840445130977879715287 26930760667696466819572931)
      ·
        refine ⟨40396141001544700229359397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26930760667696466819572931 40396141001544700229359397)
        ·
          refine ⟨7574276437789631293004887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40396141001544700229359397 7574276437789631293004887)
          ·
            refine ⟨11361414656684446939507331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574276437789631293004887 11361414656684446939507331)
            ·
              refine ⟨17042121985026670409260997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11361414656684446939507331 17042121985026670409260997)
              ·
                refine ⟨3195397872192500701736437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17042121985026670409260997 3195397872192500701736437)
                ·
                  refine ⟨299568550518046940787791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3195397872192500701736437 299568550518046940787791)
                  ·
                    rfl

theorem cell23_5250669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_5250669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250669 prefixEnd_5250669 := by exact prefixLift 5250669
  have htrace : WordTrace (prefixWord ++ tailWord_5250669) baseStart_5250669 baseEnd_5250669 := by
    simpa [prefixWord, tailWord_5250669, baseEnd_5250669] using wordTrace_append hprefix tailTrace_5250669
  have hstable : (prefixWord ++ tailWord_5250669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250669).length < 2 ^ (prefixWord ++ tailWord_5250669).sum := by decide
  have hdescent : baseEnd_5250669 < baseStart_5250669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250672 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 2, 5, 2]
def baseStart_5250672 : Nat := 118140960795 + 5250672 * 2 ^ 59
def prefixEnd_5250672 : Nat := 4983230072969 + 3 ^ 40 * 5250672 * 2
def baseEnd_5250672 : Nat := 2696118495104385955352605

theorem tailTrace_5250672 : CollatzResearch.WordTrace tailWord_5250672 prefixEnd_5250672 2696118495104385955352605 := by
  unfold tailWord_5250672
  simp only [CollatzResearch.WordTrace]
  refine ⟨95753870416859781114661135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127671827222479708152881513 95753870416859781114661135)
  ·
    refine ⟨143630805625289671671991703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95753870416859781114661135 143630805625289671671991703)
    ·
      refine ⟨215446208437934507507987555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143630805625289671671991703 215446208437934507507987555)
      ·
        refine ⟨323169312656901761261981333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215446208437934507507987555 323169312656901761261981333)
        ·
          refine ⟨15148561530792270059155375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 323169312656901761261981333 15148561530792270059155375)
          ·
            refine ⟨22722842296188405088733063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15148561530792270059155375 22722842296188405088733063)
            ·
              refine ⟨34084263444282607633099595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22722842296188405088733063 34084263444282607633099595)
              ·
                refine ⟨51126395166423911449649393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34084263444282607633099595 51126395166423911449649393)
                ·
                  refine ⟨38344796374817933587237045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51126395166423911449649393 38344796374817933587237045)
                  ·
                    refine ⟨3594824660139181273803473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38344796374817933587237045 3594824660139181273803473)
                    ·
                      refine ⟨2696118495104385955352605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3594824660139181273803473 2696118495104385955352605)
                      ·
                        rfl

theorem cell23_5250672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 5, 2].length) (baseStart_5250672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250672 prefixEnd_5250672 := by exact prefixLift 5250672
  have htrace : WordTrace (prefixWord ++ tailWord_5250672) baseStart_5250672 baseEnd_5250672 := by
    simpa [prefixWord, tailWord_5250672, baseEnd_5250672] using wordTrace_append hprefix tailTrace_5250672
  have hstable : (prefixWord ++ tailWord_5250672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250672).length < 2 ^ (prefixWord ++ tailWord_5250672).sum := by decide
  have hdescent : baseEnd_5250672 < baseStart_5250672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250702 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5250702 : Nat := 118140960795 + 5250702 * 2 ^ 59
def prefixEnd_5250702 : Nat := 4983230072969 + 3 ^ 40 * 5250702 * 2
def baseEnd_5250702 : Nat := 2696133899524020837977467

theorem tailTrace_5250702 : CollatzResearch.WordTrace tailWord_5250702 prefixEnd_5250702 2696133899524020837977467 := by
  unfold tailWord_5250702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23938604377951359669114295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127672556682407251568609573 23938604377951359669114295)
  ·
    refine ⟨35907906566927039503671443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23938604377951359669114295 35907906566927039503671443)
    ·
      refine ⟨53861859850390559255507165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35907906566927039503671443 53861859850390559255507165)
      ·
        refine ⟨20198197443896459720815187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53861859850390559255507165 20198197443896459720815187)
        ·
          refine ⟨30297296165844689581222781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20198197443896459720815187 30297296165844689581222781)
          ·
            refine ⟨11361486062191758592958543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30297296165844689581222781 11361486062191758592958543)
            ·
              refine ⟨17042229093287637889437815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11361486062191758592958543 17042229093287637889437815)
              ·
                refine ⟨25563343639931456834156723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17042229093287637889437815 25563343639931456834156723)
                ·
                  refine ⟨38345015459897185251235085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25563343639931456834156723 38345015459897185251235085)
                  ·
                    refine ⟨14379380797461444469213157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38345015459897185251235085 14379380797461444469213157)
                    ·
                      refine ⟨2696133899524020837977467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14379380797461444469213157 2696133899524020837977467)
                      ·
                        rfl

theorem cell23_5250702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5250702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250702 prefixEnd_5250702 := by exact prefixLift 5250702
  have htrace : WordTrace (prefixWord ++ tailWord_5250702) baseStart_5250702 baseEnd_5250702 := by
    simpa [prefixWord, tailWord_5250702, baseEnd_5250702] using wordTrace_append hprefix tailTrace_5250702
  have hstable : (prefixWord ++ tailWord_5250702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250702).length < 2 ^ (prefixWord ++ tailWord_5250702).sum := by decide
  have hdescent : baseEnd_5250702 < baseStart_5250702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250780 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5250780 : Nat := 118140960795 + 5250780 * 2 ^ 59
def prefixEnd_5250780 : Nat := 4983230072969 + 3 ^ 40 * 5250780 * 2
def baseEnd_5250780 : Nat := 898724650338357177600703

theorem tailTrace_5250780 : CollatzResearch.WordTrace tailWord_5250780 prefixEnd_5250780 898724650338357177600703 := by
  unfold tailWord_5250780
  simp only [CollatzResearch.WordTrace]
  refine ⟨95755839958664148337126897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127674453278218864449502529 95755839958664148337126897)
  ·
    refine ⟨71816879968998111252845173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95755839958664148337126897 71816879968998111252845173)
    ·
      refine ⟨6732832497093572929954235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71816879968998111252845173 6732832497093572929954235)
      ·
        refine ⟨10099248745640359394931353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6732832497093572929954235 10099248745640359394931353)
        ·
          refine ⟨7574436559230269546198515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10099248745640359394931353 7574436559230269546198515)
          ·
            refine ⟨11361654838845404319297773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574436559230269546198515 11361654838845404319297773)
            ·
              refine ⟨4260620564567026619736665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11361654838845404319297773 4260620564567026619736665)
              ·
                refine ⟨3195465423425269964802499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4260620564567026619736665 3195465423425269964802499)
                ·
                  refine ⟨4793198135137904947203749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195465423425269964802499 4793198135137904947203749)
                  ·
                    refine ⟨898724650338357177600703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793198135137904947203749 898724650338357177600703)
                    ·
                      rfl

theorem cell23_5250780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5250780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250780 prefixEnd_5250780 := by exact prefixLift 5250780
  have htrace : WordTrace (prefixWord ++ tailWord_5250780) baseStart_5250780 baseEnd_5250780 := by
    simpa [prefixWord, tailWord_5250780, baseEnd_5250780] using wordTrace_append hprefix tailTrace_5250780
  have hstable : (prefixWord ++ tailWord_5250780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250780).length < 2 ^ (prefixWord ++ tailWord_5250780).sum := by decide
  have hdescent : baseEnd_5250780 < baseStart_5250780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250802 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_5250802 : Nat := 118140960795 + 5250802 * 2 ^ 59
def prefixEnd_5250802 : Nat := 4983230072969 + 3 ^ 40 * 5250802 * 2
def baseEnd_5250802 : Nat := 898728415863156815575669

theorem tailTrace_5250802 : CollatzResearch.WordTrace tailWord_5250802 prefixEnd_5250802 898728415863156815575669 := by
  unfold tailWord_5250802
  simp only [CollatzResearch.WordTrace]
  refine ⟨47878120580812148607888665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127674988215499062954369773 47878120580812148607888665)
  ·
    refine ⟨35908590435609111455916499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47878120580812148607888665 35908590435609111455916499)
    ·
      refine ⟨53862885653413667183874749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35908590435609111455916499 53862885653413667183874749)
      ·
        refine ⟨20198582120030125193953031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53862885653413667183874749 20198582120030125193953031)
        ·
          refine ⟨30297873180045187790929547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20198582120030125193953031 30297873180045187790929547)
          ·
            refine ⟨45446809770067781686394321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30297873180045187790929547 45446809770067781686394321)
            ·
              refine ⟨34085107327550836264795741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45446809770067781686394321 34085107327550836264795741)
              ·
                refine ⟨12781915247831563599298403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34085107327550836264795741 12781915247831563599298403)
                ·
                  refine ⟨19172872871747345398947605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12781915247831563599298403 19172872871747345398947605)
                  ·
                    refine ⟨898728415863156815575669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19172872871747345398947605 898728415863156815575669)
                    ·
                      rfl

theorem cell23_5250802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_5250802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250802 prefixEnd_5250802 := by exact prefixLift 5250802
  have htrace : WordTrace (prefixWord ++ tailWord_5250802) baseStart_5250802 baseEnd_5250802 := by
    simpa [prefixWord, tailWord_5250802, baseEnd_5250802] using wordTrace_append hprefix tailTrace_5250802
  have hstable : (prefixWord ++ tailWord_5250802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250802).length < 2 ^ (prefixWord ++ tailWord_5250802).sum := by decide
  have hdescent : baseEnd_5250802 < baseStart_5250802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250806 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5250806 : Nat := 118140960795 + 5250806 * 2 ^ 59
def prefixEnd_5250806 : Nat := 4983230072969 + 3 ^ 40 * 5250806 * 2
def baseEnd_5250806 : Nat := 898729100504029477025663

theorem tailTrace_5250806 : CollatzResearch.WordTrace tailWord_5250806 prefixEnd_5250806 898729100504029477025663 := by
  unfold tailWord_5250806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11969539263452131444668767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127675085476822735409800181 11969539263452131444668767)
  ·
    refine ⟨17954308895178197167003151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11969539263452131444668767 17954308895178197167003151)
    ·
      refine ⟨26931463342767295750504727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17954308895178197167003151 26931463342767295750504727)
      ·
        refine ⟨40397195014150943625757091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26931463342767295750504727 40397195014150943625757091)
        ·
          refine ⟨60595792521226415438635637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40397195014150943625757091 60595792521226415438635637)
          ·
            refine ⟨5680855548864976447372091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60595792521226415438635637 5680855548864976447372091)
            ·
              refine ⟨8521283323297464671058137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680855548864976447372091 8521283323297464671058137)
              ·
                refine ⟨6390962492473098503293603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8521283323297464671058137 6390962492473098503293603)
                ·
                  refine ⟨9586443738709647754940405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6390962492473098503293603 9586443738709647754940405)
                  ·
                    refine ⟨898729100504029477025663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9586443738709647754940405 898729100504029477025663)
                    ·
                      rfl

theorem cell23_5250806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5250806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250806 prefixEnd_5250806 := by exact prefixLift 5250806
  have htrace : WordTrace (prefixWord ++ tailWord_5250806) baseStart_5250806 baseEnd_5250806 := by
    simpa [prefixWord, tailWord_5250806, baseEnd_5250806] using wordTrace_append hprefix tailTrace_5250806
  have hstable : (prefixWord ++ tailWord_5250806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250806).length < 2 ^ (prefixWord ++ tailWord_5250806).sum := by decide
  have hdescent : baseEnd_5250806 < baseStart_5250806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250815 : List Nat := [1, 1, 2, 2, 1, 3, 4, 9]
def baseStart_5250815 : Nat := 118140960795 + 5250815 * 2 ^ 59
def prefixEnd_5250815 : Nat := 4983230072969 + 3 ^ 40 * 5250815 * 2
def baseEnd_5250815 : Nat := 99858960105110329476461

theorem tailTrace_5250815 : CollatzResearch.WordTrace tailWord_5250815 prefixEnd_5250815 99858960105110329476461 := by
  unfold tailWord_5250815
  simp only [CollatzResearch.WordTrace]
  refine ⟨191512956472201497651777899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127675304314800998434518599 191512956472201497651777899)
  ·
    refine ⟨287269434708302246477666849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191512956472201497651777899 287269434708302246477666849)
    ·
      refine ⟨215452076031226684858250137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287269434708302246477666849 215452076031226684858250137)
      ·
        refine ⟨161589057023420013643687603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215452076031226684858250137 161589057023420013643687603)
        ·
          refine ⟨242383585535130020465531405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161589057023420013643687603 242383585535130020465531405)
          ·
            refine ⟨90893844575673757674574277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242383585535130020465531405 90893844575673757674574277)
            ·
              refine ⟨17042595857938829563982677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90893844575673757674574277 17042595857938829563982677)
              ·
                refine ⟨99858960105110329476461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17042595857938829563982677 99858960105110329476461)
                ·
                  rfl

theorem cell23_5250815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 9].length) (baseStart_5250815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250815 prefixEnd_5250815 := by exact prefixLift 5250815
  have htrace : WordTrace (prefixWord ++ tailWord_5250815) baseStart_5250815 baseEnd_5250815 := by
    simpa [prefixWord, tailWord_5250815, baseEnd_5250815] using wordTrace_append hprefix tailTrace_5250815
  have hstable : (prefixWord ++ tailWord_5250815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250815).length < 2 ^ (prefixWord ++ tailWord_5250815).sum := by decide
  have hdescent : baseEnd_5250815 < baseStart_5250815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250826 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_5250826 : Nat := 118140960795 + 5250826 * 2 ^ 59
def prefixEnd_5250826 : Nat := 4983230072969 + 3 ^ 40 * 5250826 * 2
def baseEnd_5250826 : Nat := 2696197571125178352826897

theorem tailTrace_5250826 : CollatzResearch.WordTrace tailWord_5250826 prefixEnd_5250826 2696197571125178352826897 := by
  unfold tailWord_5250826
  simp only [CollatzResearch.WordTrace]
  refine ⟨47878339418790411632607083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127675571783441097686952221 47878339418790411632607083)
  ·
    refine ⟨71817509128185617448910625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47878339418790411632607083 71817509128185617448910625)
    ·
      refine ⟨53863131846139213086682969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71817509128185617448910625 53863131846139213086682969)
      ·
        refine ⟨40397348884604409815012227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53863131846139213086682969 40397348884604409815012227)
        ·
          refine ⟨60596023326906614722518341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40397348884604409815012227 60596023326906614722518341)
          ·
            refine ⟨11361754373794990260472189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60596023326906614722518341 11361754373794990260472189)
            ·
              refine ⟨4260657890173121347677071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11361754373794990260472189 4260657890173121347677071)
              ·
                refine ⟨6390986835259682021515607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260657890173121347677071 6390986835259682021515607)
                ·
                  refine ⟨9586480252889523032273411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6390986835259682021515607 9586480252889523032273411)
                  ·
                    refine ⟨14379720379334284548410117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9586480252889523032273411 14379720379334284548410117)
                    ·
                      refine ⟨2696197571125178352826897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14379720379334284548410117 2696197571125178352826897)
                      ·
                        rfl

theorem cell23_5250826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_5250826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250826 prefixEnd_5250826 := by exact prefixLift 5250826
  have htrace : WordTrace (prefixWord ++ tailWord_5250826) baseStart_5250826 baseEnd_5250826 := by
    simpa [prefixWord, tailWord_5250826, baseEnd_5250826] using wordTrace_append hprefix tailTrace_5250826
  have hstable : (prefixWord ++ tailWord_5250826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250826).length < 2 ^ (prefixWord ++ tailWord_5250826).sum := by decide
  have hdescent : baseEnd_5250826 < baseStart_5250826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250835 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_5250835 : Nat := 118140960795 + 5250835 * 2 ^ 59
def prefixEnd_5250835 : Nat := 4983230072969 + 3 ^ 40 * 5250835 * 2
def baseEnd_5250835 : Nat := 2696202192451068817614355

theorem tailTrace_5250835 : CollatzResearch.WordTrace tailWord_5250835 prefixEnd_5250835 2696202192451068817614355 := by
  unfold tailWord_5250835
  simp only [CollatzResearch.WordTrace]
  refine ⟨191513685932129041067505959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127675790621419360711670639 191513685932129041067505959)
  ·
    refine ⟨287270528898193561601258939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191513685932129041067505959 287270528898193561601258939)
    ·
      refine ⟨430905793347290342401888409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287270528898193561601258939 430905793347290342401888409)
      ·
        refine ⟨323179345010467756801416307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430905793347290342401888409 323179345010467756801416307)
        ·
          refine ⟨484769017515701635202124461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323179345010467756801416307 484769017515701635202124461)
          ·
            refine ⟨181788381568388113200796673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484769017515701635202124461 181788381568388113200796673)
            ·
              refine ⟨136341286176291084900597505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181788381568388113200796673 136341286176291084900597505)
              ·
                refine ⟨102255964632218313675448129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136341286176291084900597505 102255964632218313675448129)
                ·
                  refine ⟨76691973474163735256586097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102255964632218313675448129 76691973474163735256586097)
                  ·
                    refine ⟨57518980105622801442439573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76691973474163735256586097 57518980105622801442439573)
                    ·
                      refine ⟨2696202192451068817614355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57518980105622801442439573 2696202192451068817614355)
                      ·
                        rfl

theorem cell23_5250835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_5250835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250835 prefixEnd_5250835 := by exact prefixLift 5250835
  have htrace : WordTrace (prefixWord ++ tailWord_5250835) baseStart_5250835 baseEnd_5250835 := by
    simpa [prefixWord, tailWord_5250835, baseEnd_5250835] using wordTrace_append hprefix tailTrace_5250835
  have hstable : (prefixWord ++ tailWord_5250835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250835).length < 2 ^ (prefixWord ++ tailWord_5250835).sum := by decide
  have hdescent : baseEnd_5250835 < baseStart_5250835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5250893 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5250893 : Nat := 118140960795 + 5250893 * 2 ^ 59
def prefixEnd_5250893 : Nat := 4983230072969 + 3 ^ 40 * 5250893 * 2
def baseEnd_5250893 : Nat := 2696231974329029590689089

theorem tailTrace_5250893 : CollatzResearch.WordTrace tailWord_5250893 prefixEnd_5250893 2696231974329029590689089 := by
  unfold tailWord_5250893
  simp only [CollatzResearch.WordTrace]
  refine ⟨191515801365918916973117333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127677200910612611315411555 191515801365918916973117333)
  ·
    refine ⟨8977303189027449233114875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191515801365918916973117333 8977303189027449233114875)
    ·
      refine ⟨13465954783541173849672313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8977303189027449233114875 13465954783541173849672313)
      ·
        refine ⟨10099466087655880387254235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13465954783541173849672313 10099466087655880387254235)
        ·
          refine ⟨15149199131483820580881353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10099466087655880387254235 15149199131483820580881353)
          ·
            refine ⟨11361899348612865435661015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15149199131483820580881353 11361899348612865435661015)
            ·
              refine ⟨17042849022919298153491523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11361899348612865435661015 17042849022919298153491523)
              ·
                refine ⟨25564273534378947230237285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17042849022919298153491523 25564273534378947230237285)
                ·
                  refine ⟨4793301287696052605669491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25564273534378947230237285 4793301287696052605669491)
                  ·
                    refine ⟨7189951931544078908504237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4793301287696052605669491 7189951931544078908504237)
                    ·
                      refine ⟨2696231974329029590689089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7189951931544078908504237 2696231974329029590689089)
                      ·
                        rfl

theorem cell23_5250893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5250893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5250893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5250893 prefixEnd_5250893 := by exact prefixLift 5250893
  have htrace : WordTrace (prefixWord ++ tailWord_5250893) baseStart_5250893 baseEnd_5250893 := by
    simpa [prefixWord, tailWord_5250893, baseEnd_5250893] using wordTrace_append hprefix tailTrace_5250893
  have hstable : (prefixWord ++ tailWord_5250893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5250893).length < 2 ^ (prefixWord ++ tailWord_5250893).sum := by decide
  have hdescent : baseEnd_5250893 < baseStart_5250893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5250893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251006 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_5251006 : Nat := 118140960795 + 5251006 * 2 ^ 59
def prefixEnd_5251006 : Nat := 4983230072969 + 3 ^ 40 * 5251006 * 2
def baseEnd_5251006 : Nat := 2696289997642987648576069

theorem tailTrace_5251006 : CollatzResearch.WordTrace tailWord_5251006 prefixEnd_5251006 2696289997642987648576069 := by
  unfold tailWord_5251006
  simp only [CollatzResearch.WordTrace]
  refine ⟨23939990351813692158997609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127679948543006358181320581 23939990351813692158997609)
  ·
    refine ⟨17954992763860269119248207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23939990351813692158997609 17954992763860269119248207)
    ·
      refine ⟨26932489145790403678872311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17954992763860269119248207 26932489145790403678872311)
      ·
        refine ⟨40398733718685605518308467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26932489145790403678872311 40398733718685605518308467)
        ·
          refine ⟨60598100578028408277462701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40398733718685605518308467 60598100578028408277462701)
          ·
            refine ⟨22724287716760653104048513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60598100578028408277462701 22724287716760653104048513)
            ·
              refine ⟨17043215787570489828036385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22724287716760653104048513 17043215787570489828036385)
              ·
                refine ⟨12782411840677867371027289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17043215787570489828036385 12782411840677867371027289)
                ·
                  refine ⟨9586808880508400528270467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12782411840677867371027289 9586808880508400528270467)
                  ·
                    refine ⟨14380213320762600792405701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9586808880508400528270467 14380213320762600792405701)
                    ·
                      refine ⟨2696289997642987648576069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14380213320762600792405701 2696289997642987648576069)
                      ·
                        rfl

theorem cell23_5251006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_5251006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251006 prefixEnd_5251006 := by exact prefixLift 5251006
  have htrace : WordTrace (prefixWord ++ tailWord_5251006) baseStart_5251006 baseEnd_5251006 := by
    simpa [prefixWord, tailWord_5251006, baseEnd_5251006] using wordTrace_append hprefix tailTrace_5251006
  have hstable : (prefixWord ++ tailWord_5251006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251006).length < 2 ^ (prefixWord ++ tailWord_5251006).sum := by decide
  have hdescent : baseEnd_5251006 < baseStart_5251006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251043 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 3]
def baseStart_5251043 : Nat := 118140960795 + 5251043 * 2 ^ 59
def prefixEnd_5251043 : Nat := 4983230072969 + 3 ^ 40 * 5251043 * 2
def baseEnd_5251043 : Nat := 2696308996427204003813399

theorem tailTrace_5251043 : CollatzResearch.WordTrace tailWord_5251043 prefixEnd_5251043 2696308996427204003813399 := by
  unfold tailWord_5251043
  simp only [CollatzResearch.WordTrace]
  refine ⟨191521272315375492591077783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127680848210250328394051855 191521272315375492591077783)
  ·
    refine ⟨287281908473063238886616675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191521272315375492591077783 287281908473063238886616675)
    ·
      refine ⟨430922862709594858329925013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287281908473063238886616675 430922862709594858329925013)
      ·
        refine ⟨20199509189512258984215235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 430922862709594858329925013 20199509189512258984215235)
        ·
          refine ⟨30299263784268388476322853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20199509189512258984215235 30299263784268388476322853)
          ·
            refine ⟨5681111959550322839310535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30299263784268388476322853 5681111959550322839310535)
            ·
              refine ⟨8521667939325484258965803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681111959550322839310535 8521667939325484258965803)
              ·
                refine ⟨12782501908988226388448705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8521667939325484258965803 12782501908988226388448705)
                ·
                  refine ⟨9586876431741169791336529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12782501908988226388448705 9586876431741169791336529)
                  ·
                    refine ⟨7190157323805877343502397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9586876431741169791336529 7190157323805877343502397)
                    ·
                      refine ⟨2696308996427204003813399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190157323805877343502397 2696308996427204003813399)
                      ·
                        rfl

theorem cell23_5251043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_5251043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251043 prefixEnd_5251043 := by exact prefixLift 5251043
  have htrace : WordTrace (prefixWord ++ tailWord_5251043) baseStart_5251043 baseEnd_5251043 := by
    simpa [prefixWord, tailWord_5251043, baseEnd_5251043] using wordTrace_append hprefix tailTrace_5251043
  have hstable : (prefixWord ++ tailWord_5251043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251043).length < 2 ^ (prefixWord ++ tailWord_5251043).sum := by decide
  have hdescent : baseEnd_5251043 < baseStart_5251043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251073 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_5251073 : Nat := 118140960795 + 5251073 * 2 ^ 59
def prefixEnd_5251073 : Nat := 4983230072969 + 3 ^ 40 * 5251073 * 2
def baseEnd_5251073 : Nat := 2696324400846838886438261

theorem tailTrace_5251073 : CollatzResearch.WordTrace tailWord_5251073 prefixEnd_5251073 2696324400846838886438261 := by
  unfold tailWord_5251073
  simp only [CollatzResearch.WordTrace]
  refine ⟨191522366505266807714669873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127681577670177871809779915 191522366505266807714669873)
  ·
    refine ⟨143641774878950105786002405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191522366505266807714669873 143641774878950105786002405)
    ·
      refine ⟨26932832789803144834875451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143641774878950105786002405 26932832789803144834875451)
      ·
        refine ⟨40399249184704717252313177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26932832789803144834875451 40399249184704717252313177)
        ·
          refine ⟨30299436888528537939234883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40399249184704717252313177 30299436888528537939234883)
          ·
            refine ⟨45449155332792806908852325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30299436888528537939234883 45449155332792806908852325)
            ·
              refine ⟨8521716624898651295409811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45449155332792806908852325 8521716624898651295409811)
              ·
                refine ⟨12782574937347976943114717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8521716624898651295409811 12782574937347976943114717)
                ·
                  refine ⟨4793465601505491353668019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12782574937347976943114717 4793465601505491353668019)
                  ·
                    refine ⟨7190198402258237030502029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4793465601505491353668019 7190198402258237030502029)
                    ·
                      refine ⟨2696324400846838886438261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190198402258237030502029 2696324400846838886438261)
                      ·
                        rfl

theorem cell23_5251073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_5251073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251073 prefixEnd_5251073 := by exact prefixLift 5251073
  have htrace : WordTrace (prefixWord ++ tailWord_5251073) baseStart_5251073 baseEnd_5251073 := by
    simpa [prefixWord, tailWord_5251073, baseEnd_5251073] using wordTrace_append hprefix tailTrace_5251073
  have hstable : (prefixWord ++ tailWord_5251073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251073).length < 2 ^ (prefixWord ++ tailWord_5251073).sum := by decide
  have hdescent : baseEnd_5251073 < baseStart_5251073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251093 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_5251093 : Nat := 118140960795 + 5251093 * 2 ^ 59
def prefixEnd_5251093 : Nat := 4983230072969 + 3 ^ 40 * 5251093 * 2
def baseEnd_5251093 : Nat := 898778223486642936062723

theorem tailTrace_5251093 : CollatzResearch.WordTrace tailWord_5251093 prefixEnd_5251093 898778223486642936062723 := by
  unfold tailWord_5251093
  simp only [CollatzResearch.WordTrace]
  refine ⟨191523095965194351130397933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127682063976796234086931955 191523095965194351130397933)
  ·
    refine ⟨71821160986947881673899225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191523095965194351130397933 71821160986947881673899225)
    ·
      refine ⟨53865870740210911255424419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71821160986947881673899225 53865870740210911255424419)
      ·
        refine ⟨80798806110316366883136629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53865870740210911255424419 80798806110316366883136629)
        ·
          refine ⟨7574888072842159395294059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80798806110316366883136629 7574888072842159395294059)
          ·
            refine ⟨11362332109263239092941089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574888072842159395294059 11362332109263239092941089)
            ·
              refine ⟨8521749081947429319705817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11362332109263239092941089 8521749081947429319705817)
              ·
                refine ⟨6391311811460571989779363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8521749081947429319705817 6391311811460571989779363)
                ·
                  refine ⟨9586967717190857984669045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6391311811460571989779363 9586967717190857984669045)
                  ·
                    refine ⟨898778223486642936062723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9586967717190857984669045 898778223486642936062723)
                    ·
                      rfl

theorem cell23_5251093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_5251093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251093 prefixEnd_5251093 := by exact prefixLift 5251093
  have htrace : WordTrace (prefixWord ++ tailWord_5251093) baseStart_5251093 baseEnd_5251093 := by
    simpa [prefixWord, tailWord_5251093, baseEnd_5251093] using wordTrace_append hprefix tailTrace_5251093
  have hstable : (prefixWord ++ tailWord_5251093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251093).length < 2 ^ (prefixWord ++ tailWord_5251093).sum := by decide
  have hdescent : baseEnd_5251093 < baseStart_5251093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251096 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 6, 2]
def baseStart_5251096 : Nat := 118140960795 + 5251096 * 2 ^ 59
def prefixEnd_5251096 : Nat := 4983230072969 + 3 ^ 40 * 5251096 * 2
def baseEnd_5251096 : Nat := 2696336210901892296450655

theorem tailTrace_5251096 : CollatzResearch.WordTrace tailWord_5251096 prefixEnd_5251096 2696336210901892296450655 := by
  unfold tailWord_5251096
  simp only [CollatzResearch.WordTrace]
  refine ⟨95761602692091741321378571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127682136922788988428504761 95761602692091741321378571)
  ·
    refine ⟨143642404038137611982067857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95761602692091741321378571 143642404038137611982067857)
    ·
      refine ⟨107731803028603208986550893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143642404038137611982067857 107731803028603208986550893)
      ·
        refine ⟨40399426135726203369956585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107731803028603208986550893 40399426135726203369956585)
        ·
          refine ⟨30299569601794652527467439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40399426135726203369956585 30299569601794652527467439)
          ·
            refine ⟨45449354402691978791201159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30299569601794652527467439 45449354402691978791201159)
            ·
              refine ⟨68174031604037968186801739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45449354402691978791201159 68174031604037968186801739)
              ·
                refine ⟨102261047406056952280202609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68174031604037968186801739 102261047406056952280202609)
                ·
                  refine ⟨76695785554542714210151957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102261047406056952280202609 76695785554542714210151957)
                  ·
                    refine ⟨3595114947869189728600873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76695785554542714210151957 3595114947869189728600873)
                    ·
                      refine ⟨2696336210901892296450655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595114947869189728600873 2696336210901892296450655)
                      ·
                        rfl

theorem cell23_5251096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_5251096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251096 prefixEnd_5251096 := by exact prefixLift 5251096
  have htrace : WordTrace (prefixWord ++ tailWord_5251096) baseStart_5251096 baseEnd_5251096 := by
    simpa [prefixWord, tailWord_5251096, baseEnd_5251096] using wordTrace_append hprefix tailTrace_5251096
  have hstable : (prefixWord ++ tailWord_5251096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251096).length < 2 ^ (prefixWord ++ tailWord_5251096).sum := by decide
  have hdescent : baseEnd_5251096 < baseStart_5251096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251106 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_5251106 : Nat := 118140960795 + 5251106 * 2 ^ 59
def prefixEnd_5251106 : Nat := 4983230072969 + 3 ^ 40 * 5251106 * 2
def baseEnd_5251106 : Nat := 898780448569479085775203

theorem tailTrace_5251106 : CollatzResearch.WordTrace tailWord_5251106 prefixEnd_5251106 898780448569479085775203 := by
  unfold tailWord_5251106
  simp only [CollatzResearch.WordTrace]
  refine ⟨47880892528536813587655293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127682380076098169567080781 47880892528536813587655293)
  ·
    refine ⟨17955334698201305095370735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47880892528536813587655293 17955334698201305095370735)
    ·
      refine ⟨26933002047301957643056103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17955334698201305095370735 26933002047301957643056103)
      ·
        refine ⟨40399503070952936464584155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26933002047301957643056103 40399503070952936464584155)
        ·
          refine ⟨60599254606429404696876233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40399503070952936464584155 60599254606429404696876233)
          ·
            refine ⟨45449440954822053522657175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60599254606429404696876233 45449440954822053522657175)
            ·
              refine ⟨68174161432233080283985763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45449440954822053522657175 68174161432233080283985763)
              ·
                refine ⟨102261242148349620425978645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68174161432233080283985763 102261242148349620425978645)
                ·
                  refine ⟨4793495725703888457467749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102261242148349620425978645 4793495725703888457467749)
                  ·
                    refine ⟨898780448569479085775203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793495725703888457467749 898780448569479085775203)
                    ·
                      rfl

theorem cell23_5251106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_5251106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251106 prefixEnd_5251106 := by exact prefixLift 5251106
  have htrace : WordTrace (prefixWord ++ tailWord_5251106) baseStart_5251106 baseEnd_5251106 := by
    simpa [prefixWord, tailWord_5251106, baseEnd_5251106] using wordTrace_append hprefix tailTrace_5251106
  have hstable : (prefixWord ++ tailWord_5251106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251106).length < 2 ^ (prefixWord ++ tailWord_5251106).sum := by decide
  have hdescent : baseEnd_5251106 < baseStart_5251106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251124 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5251124 : Nat := 118140960795 + 5251124 * 2 ^ 59
def prefixEnd_5251124 : Nat := 4983230072969 + 3 ^ 40 * 5251124 * 2
def baseEnd_5251124 : Nat := 2696350588360218186900527

theorem tailTrace_5251124 : CollatzResearch.WordTrace tailWord_5251124 prefixEnd_5251124 2696350588360218186900527 := by
  unfold tailWord_5251124
  simp only [CollatzResearch.WordTrace]
  refine ⟨95762113314041021712388213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127682817752054695616517617 95762113314041021712388213)
  ·
    refine ⟨8977698123191345785536395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95762113314041021712388213 8977698123191345785536395)
    ·
      refine ⟨13466547184787018678304593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8977698123191345785536395 13466547184787018678304593)
      ·
        refine ⟨10099910388590264008728445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13466547184787018678304593 10099910388590264008728445)
        ·
          refine ⟨3787466395721349003273167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10099910388590264008728445 3787466395721349003273167)
          ·
            refine ⟨5681199593582023504909751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787466395721349003273167 5681199593582023504909751)
            ·
              refine ⟨8521799390373035257364627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681199593582023504909751 8521799390373035257364627)
              ·
                refine ⟨12782699085559552886046941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8521799390373035257364627 12782699085559552886046941)
                ·
                  refine ⟨4793512157084832332267603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12782699085559552886046941 4793512157084832332267603)
                  ·
                    refine ⟨7190268235627248498401405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4793512157084832332267603 7190268235627248498401405)
                    ·
                      refine ⟨2696350588360218186900527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190268235627248498401405 2696350588360218186900527)
                      ·
                        rfl

theorem cell23_5251124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5251124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251124 prefixEnd_5251124 := by exact prefixLift 5251124
  have htrace : WordTrace (prefixWord ++ tailWord_5251124) baseStart_5251124 baseEnd_5251124 := by
    simpa [prefixWord, tailWord_5251124, baseEnd_5251124] using wordTrace_append hprefix tailTrace_5251124
  have hstable : (prefixWord ++ tailWord_5251124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251124).length < 2 ^ (prefixWord ++ tailWord_5251124).sum := by decide
  have hdescent : baseEnd_5251124 < baseStart_5251124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251126 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5251126 : Nat := 118140960795 + 5251126 * 2 ^ 59
def prefixEnd_5251126 : Nat := 4983230072969 + 3 ^ 40 * 5251126 * 2
def baseEnd_5251126 : Nat := 2696351615321527179075517

theorem tailTrace_5251126 : CollatzResearch.WordTrace tailWord_5251126 prefixEnd_5251126 2696351615321527179075517 := by
  unfold tailWord_5251126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11970268723379674860396827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127682866382716531844232821 11970268723379674860396827)
  ·
    refine ⟨17955403085069512290595241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11970268723379674860396827 17955403085069512290595241)
    ·
      refine ⟨13466552313802134217946431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17955403085069512290595241 13466552313802134217946431)
      ·
        refine ⟨20199828470703201326919647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13466552313802134217946431 20199828470703201326919647)
        ·
          refine ⟨30299742706054801990379471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20199828470703201326919647 30299742706054801990379471)
          ·
            refine ⟨45449614059082202985569207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30299742706054801990379471 45449614059082202985569207)
            ·
              refine ⟨68174421088623304478353811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45449614059082202985569207 68174421088623304478353811)
              ·
                refine ⟨102261631632934956717530717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68174421088623304478353811 102261631632934956717530717)
                ·
                  refine ⟨38348111862350608769074019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102261631632934956717530717 38348111862350608769074019)
                  ·
                    refine ⟨57522167793525913153611029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38348111862350608769074019 57522167793525913153611029)
                    ·
                      refine ⟨2696351615321527179075517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57522167793525913153611029 2696351615321527179075517)
                      ·
                        rfl

theorem cell23_5251126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5251126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251126 prefixEnd_5251126 := by exact prefixLift 5251126
  have htrace : WordTrace (prefixWord ++ tailWord_5251126) baseStart_5251126 baseEnd_5251126 := by
    simpa [prefixWord, tailWord_5251126, baseEnd_5251126] using wordTrace_append hprefix tailTrace_5251126
  have hstable : (prefixWord ++ tailWord_5251126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251126).length < 2 ^ (prefixWord ++ tailWord_5251126).sum := by decide
  have hdescent : baseEnd_5251126 < baseStart_5251126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251146 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_5251146 : Nat := 118140960795 + 5251146 * 2 ^ 59
def prefixEnd_5251146 : Nat := 4983230072969 + 3 ^ 40 * 5251146 * 2
def baseEnd_5251146 : Nat := 2696361884934617100825425

theorem tailTrace_5251146 : CollatzResearch.WordTrace tailWord_5251146 prefixEnd_5251146 2696361884934617100825425 := by
  unfold tailWord_5251146
  simp only [CollatzResearch.WordTrace]
  refine ⟨47881257258500585295519323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127683352689334894121384861 47881257258500585295519323)
  ·
    refine ⟨71821885887750877943278985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47881257258500585295519323 71821885887750877943278985)
    ·
      refine ⟨53866414415813158457459239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71821885887750877943278985 53866414415813158457459239)
      ·
        refine ⟨80799621623719737686188859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53866414415813158457459239 80799621623719737686188859)
        ·
          refine ⟨121199432435579606529283289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80799621623719737686188859 121199432435579606529283289)
          ·
            refine ⟨90899574326684704896962467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121199432435579606529283289 90899574326684704896962467)
            ·
              refine ⟨136349361490027057345443701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90899574326684704896962467 136349361490027057345443701)
              ·
                refine ⟨12782752639690036626135347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136349361490027057345443701 12782752639690036626135347)
                ·
                  refine ⟨19174128959535054939203021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12782752639690036626135347 19174128959535054939203021)
                  ·
                    refine ⟨7190298359825645602201133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19174128959535054939203021 7190298359825645602201133)
                    ·
                      refine ⟨2696361884934617100825425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190298359825645602201133 2696361884934617100825425)
                      ·
                        rfl

theorem cell23_5251146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_5251146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251146 prefixEnd_5251146 := by exact prefixLift 5251146
  have htrace : WordTrace (prefixWord ++ tailWord_5251146) baseStart_5251146 baseEnd_5251146 := by
    simpa [prefixWord, tailWord_5251146, baseEnd_5251146] using wordTrace_append hprefix tailTrace_5251146
  have hstable : (prefixWord ++ tailWord_5251146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251146).length < 2 ^ (prefixWord ++ tailWord_5251146).sum := by decide
  have hdescent : baseEnd_5251146 < baseStart_5251146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251150 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_5251150 : Nat := 118140960795 + 5251150 * 2 ^ 59
def prefixEnd_5251150 : Nat := 4983230072969 + 3 ^ 40 * 5251150 * 2
def baseEnd_5251150 : Nat := 2696363938857235085175407

theorem tailTrace_5251150 : CollatzResearch.WordTrace tailWord_5251150 prefixEnd_5251150 2696363938857235085175407 := by
  unfold tailWord_5251150
  simp only [CollatzResearch.WordTrace]
  refine ⟨23940646865748481233152863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127683449950658566576815269 23940646865748481233152863)
  ·
    refine ⟨35910970298622721849729295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23940646865748481233152863 35910970298622721849729295)
    ·
      refine ⟨53866455447934082774593943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35910970298622721849729295 53866455447934082774593943)
      ·
        refine ⟨80799683171901124161890915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53866455447934082774593943 80799683171901124161890915)
        ·
          refine ⟨121199524757851686242836373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80799683171901124161890915 121199524757851686242836373)
          ·
            refine ⟨5681227723024297792632955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121199524757851686242836373 5681227723024297792632955)
            ·
              refine ⟨8521841584536446688949433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681227723024297792632955 8521841584536446688949433)
              ·
                refine ⟨6391381188402335016712075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8521841584536446688949433 6391381188402335016712075)
                ·
                  refine ⟨9587071782603502525068113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6391381188402335016712075 9587071782603502525068113)
                  ·
                    refine ⟨7190303836952626893801085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9587071782603502525068113 7190303836952626893801085)
                    ·
                      refine ⟨2696363938857235085175407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190303836952626893801085 2696363938857235085175407)
                      ·
                        rfl

theorem cell23_5251150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_5251150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251150 prefixEnd_5251150 := by exact prefixLift 5251150
  have htrace : WordTrace (prefixWord ++ tailWord_5251150) baseStart_5251150 baseEnd_5251150 := by
    simpa [prefixWord, tailWord_5251150, baseEnd_5251150] using wordTrace_append hprefix tailTrace_5251150
  have hstable : (prefixWord ++ tailWord_5251150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251150).length < 2 ^ (prefixWord ++ tailWord_5251150).sum := by decide
  have hdescent : baseEnd_5251150 < baseStart_5251150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251159 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5251159 : Nat := 118140960795 + 5251159 * 2 ^ 59
def prefixEnd_5251159 : Nat := 4983230072969 + 3 ^ 40 * 5251159 * 2
def baseEnd_5251159 : Nat := 2696368560183125549962865

theorem tailTrace_5251159 : CollatzResearch.WordTrace tailWord_5251159 prefixEnd_5251159 2696368560183125549962865 := by
  unfold tailWord_5251159
  simp only [CollatzResearch.WordTrace]
  refine ⟨191525503182955244402300531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127683668788636829601533687 191525503182955244402300531)
  ·
    refine ⟨287288254774432866603450797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191525503182955244402300531 287288254774432866603450797)
    ·
      refine ⟨107733095540412324976294049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287288254774432866603450797 107733095540412324976294049)
      ·
        refine ⟨80799821655309243732220537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107733095540412324976294049 80799821655309243732220537)
        ·
          refine ⟨60599866241481932799165403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80799821655309243732220537 60599866241481932799165403)
          ·
            refine ⟨90899799362222899198748105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60599866241481932799165403 90899799362222899198748105)
            ·
              refine ⟨68174849521667174399061079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90899799362222899198748105 68174849521667174399061079)
              ·
                refine ⟨102262274282500761598591619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68174849521667174399061079 102262274282500761598591619)
                ·
                  refine ⟨153393411423751142397887429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102262274282500761598591619 153393411423751142397887429)
                  ·
                    refine ⟨28761264641953339199603893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153393411423751142397887429 28761264641953339199603893)
                    ·
                      refine ⟨2696368560183125549962865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28761264641953339199603893 2696368560183125549962865)
                      ·
                        rfl

theorem cell23_5251159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5251159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251159 prefixEnd_5251159 := by exact prefixLift 5251159
  have htrace : WordTrace (prefixWord ++ tailWord_5251159) baseStart_5251159 baseEnd_5251159 := by
    simpa [prefixWord, tailWord_5251159, baseEnd_5251159] using wordTrace_append hprefix tailTrace_5251159
  have hstable : (prefixWord ++ tailWord_5251159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251159).length < 2 ^ (prefixWord ++ tailWord_5251159).sum := by decide
  have hdescent : baseEnd_5251159 < baseStart_5251159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251180 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_5251180 : Nat := 118140960795 + 5251180 * 2 ^ 59
def prefixEnd_5251180 : Nat := 4983230072969 + 3 ^ 40 * 5251180 * 2
def baseEnd_5251180 : Nat := 2696379343276869967800269

theorem tailTrace_5251180 : CollatzResearch.WordTrace tailWord_5251180 prefixEnd_5251180 2696379343276869967800269 := by
  unfold tailWord_5251180
  simp only [CollatzResearch.WordTrace]
  refine ⟨95763134557939582494407497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127684179410586109992543329 95763134557939582494407497)
  ·
    refine ⟨71822350918454686870805623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95763134557939582494407497 71822350918454686870805623)
    ·
      refine ⟨107733526377682030306208435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71822350918454686870805623 107733526377682030306208435)
      ·
        refine ⟨161600289566523045459312653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107733526377682030306208435 161600289566523045459312653)
        ·
          refine ⟨60600108587446142047242245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161600289566523045459312653 60600108587446142047242245)
          ·
            refine ⟨11362520360146151633857921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60600108587446142047242245 11362520360146151633857921)
            ·
              refine ⟨8521890270109613725393441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11362520360146151633857921 8521890270109613725393441)
              ·
                refine ⟨6391417702582210294045081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8521890270109613725393441 6391417702582210294045081)
                ·
                  refine ⟨4793563276936657720533811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391417702582210294045081 4793563276936657720533811)
                  ·
                    refine ⟨7190344915404986580800717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4793563276936657720533811 7190344915404986580800717)
                    ·
                      refine ⟨2696379343276869967800269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190344915404986580800717 2696379343276869967800269)
                      ·
                        rfl

theorem cell23_5251180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_5251180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251180 prefixEnd_5251180 := by exact prefixLift 5251180
  have htrace : WordTrace (prefixWord ++ tailWord_5251180) baseStart_5251180 baseEnd_5251180 := by
    simpa [prefixWord, tailWord_5251180, baseEnd_5251180] using wordTrace_append hprefix tailTrace_5251180
  have hstable : (prefixWord ++ tailWord_5251180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251180).length < 2 ^ (prefixWord ++ tailWord_5251180).sum := by decide
  have hdescent : baseEnd_5251180 < baseStart_5251180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251186 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5251186 : Nat := 118140960795 + 5251186 * 2 ^ 59
def prefixEnd_5251186 : Nat := 4983230072969 + 3 ^ 40 * 5251186 * 2
def baseEnd_5251186 : Nat := 2696382424160796944325241

theorem tailTrace_5251186 : CollatzResearch.WordTrace tailWord_5251186 prefixEnd_5251186 2696382424160796944325241 := by
  unfold tailWord_5251186
  simp only [CollatzResearch.WordTrace]
  refine ⟨47881621988464357003383353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127684325302571618675688941 47881621988464357003383353)
  ·
    refine ⟨35911216491348267752537515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47881621988464357003383353 35911216491348267752537515)
    ·
      refine ⟨53866824737022401628806273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35911216491348267752537515 53866824737022401628806273)
      ·
        refine ⟨40400118552766801221604705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53866824737022401628806273 40400118552766801221604705)
        ·
          refine ⟨30300088914575100916203529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40400118552766801221604705 30300088914575100916203529)
          ·
            refine ⟨22725066685931325687152647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30300088914575100916203529 22725066685931325687152647)
            ·
              refine ⟨34087600028896988530728971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22725066685931325687152647 34087600028896988530728971)
              ·
                refine ⟨51131400043345482796093457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34087600028896988530728971 51131400043345482796093457)
                ·
                  refine ⟨38348550032509112097070093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51131400043345482796093457 38348550032509112097070093)
                  ·
                    refine ⟨14380706262190917036401285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38348550032509112097070093 14380706262190917036401285)
                    ·
                      refine ⟨2696382424160796944325241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14380706262190917036401285 2696382424160796944325241)
                      ·
                        rfl

theorem cell23_5251186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5251186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251186 prefixEnd_5251186 := by exact prefixLift 5251186
  have htrace : WordTrace (prefixWord ++ tailWord_5251186) baseStart_5251186 baseEnd_5251186 := by
    simpa [prefixWord, tailWord_5251186, baseEnd_5251186] using wordTrace_append hprefix tailTrace_5251186
  have hstable : (prefixWord ++ tailWord_5251186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251186).length < 2 ^ (prefixWord ++ tailWord_5251186).sum := by decide
  have hdescent : baseEnd_5251186 < baseStart_5251186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251190 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5251190 : Nat := 118140960795 + 5251190 * 2 ^ 59
def prefixEnd_5251190 : Nat := 4983230072969 + 3 ^ 40 * 5251190 * 2
def baseEnd_5251190 : Nat := 2696384478083414928675223

theorem tailTrace_5251190 : CollatzResearch.WordTrace tailWord_5251190 prefixEnd_5251190 2696384478083414928675223 := by
  unfold tailWord_5251190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11970414615365183543542439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127684422563895291131119349 11970414615365183543542439)
  ·
    refine ⟨17955621923047775315313659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11970414615365183543542439 17955621923047775315313659)
    ·
      refine ⟨26933432884571662972970489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17955621923047775315313659 26933432884571662972970489)
      ·
        refine ⟨20200074663428747229727867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26933432884571662972970489 20200074663428747229727867)
        ·
          refine ⟨30300111995143120844591801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20200074663428747229727867 30300111995143120844591801)
          ·
            refine ⟨22725083996357340633443851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30300111995143120844591801 22725083996357340633443851)
            ·
              refine ⟨34087625994536010950165777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22725083996357340633443851 34087625994536010950165777)
              ·
                refine ⟨25565719495902008212624333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34087625994536010950165777 25565719495902008212624333)
                ·
                  refine ⟨9587144810963253079734125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25565719495902008212624333 9587144810963253079734125)
                  ·
                    refine ⟨3595179304111219904900297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9587144810963253079734125 3595179304111219904900297)
                    ·
                      refine ⟨2696384478083414928675223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595179304111219904900297 2696384478083414928675223)
                      ·
                        rfl

theorem cell23_5251190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5251190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251190 prefixEnd_5251190 := by exact prefixLift 5251190
  have htrace : WordTrace (prefixWord ++ tailWord_5251190) baseStart_5251190 baseEnd_5251190 := by
    simpa [prefixWord, tailWord_5251190, baseEnd_5251190] using wordTrace_append hprefix tailTrace_5251190
  have hstable : (prefixWord ++ tailWord_5251190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251190).length < 2 ^ (prefixWord ++ tailWord_5251190).sum := by decide
  have hdescent : baseEnd_5251190 < baseStart_5251190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251196 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_5251196 : Nat := 118140960795 + 5251196 * 2 ^ 59
def prefixEnd_5251196 : Nat := 4983230072969 + 3 ^ 40 * 5251196 * 2
def baseEnd_5251196 : Nat := 898795852989113968400065

theorem tailTrace_5251196 : CollatzResearch.WordTrace tailWord_5251196 prefixEnd_5251196 898795852989113968400065 := by
  unfold tailWord_5251196
  simp only [CollatzResearch.WordTrace]
  refine ⟨95763426341910599860698721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127684568455880799814264961 95763426341910599860698721)
  ·
    refine ⟨71822569756432949895524041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95763426341910599860698721 71822569756432949895524041)
    ·
      refine ⟨53866927317324712421643031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71822569756432949895524041 53866927317324712421643031)
      ·
        refine ⟨80800390975987068632464547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53866927317324712421643031 80800390975987068632464547)
        ·
          refine ⟨121200586463980602948696821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80800390975987068632464547 121200586463980602948696821)
          ·
            refine ⟨11362554980998181526440327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121200586463980602948696821 11362554980998181526440327)
            ·
              refine ⟨17043832471497272289660491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11362554980998181526440327 17043832471497272289660491)
              ·
                refine ⟨25565748707245908434490737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17043832471497272289660491 25565748707245908434490737)
                ·
                  refine ⟨19174311530434431325868053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25565748707245908434490737 19174311530434431325868053)
                  ·
                    refine ⟨898795852989113968400065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19174311530434431325868053 898795852989113968400065)
                    ·
                      rfl

theorem cell23_5251196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_5251196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251196 prefixEnd_5251196 := by exact prefixLift 5251196
  have htrace : WordTrace (prefixWord ++ tailWord_5251196) baseStart_5251196 baseEnd_5251196 := by
    simpa [prefixWord, tailWord_5251196, baseEnd_5251196] using wordTrace_append hprefix tailTrace_5251196
  have hstable : (prefixWord ++ tailWord_5251196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251196).length < 2 ^ (prefixWord ++ tailWord_5251196).sum := by decide
  have hdescent : baseEnd_5251196 < baseStart_5251196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251203 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 1, 4, 2]
def baseStart_5251203 : Nat := 118140960795 + 5251203 * 2 ^ 59
def prefixEnd_5251203 : Nat := 4983230072969 + 3 ^ 40 * 5251203 * 2
def baseEnd_5251203 : Nat := 2696391153331923377812663

theorem tailTrace_5251203 : CollatzResearch.WordTrace tailWord_5251203 prefixEnd_5251203 2696391153331923377812663 := by
  unfold tailWord_5251203
  simp only [CollatzResearch.WordTrace]
  refine ⟨191527107994795839916902263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127684738663197226611268175 191527107994795839916902263)
  ·
    refine ⟨287290661992193759875353395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191527107994795839916902263 287290661992193759875353395)
    ·
      refine ⟨430935992988290639813030093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287290661992193759875353395 430935992988290639813030093)
      ·
        refine ⟨161600997370608989929886285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430935992988290639813030093 161600997370608989929886285)
        ·
          refine ⟨60600374013978371223707357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161600997370608989929886285 60600374013978371223707357)
          ·
            refine ⟨22725140255241889208890259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60600374013978371223707357 22725140255241889208890259)
            ·
              refine ⟨34087710382862833813335389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22725140255241889208890259 34087710382862833813335389)
              ·
                refine ⟨12782891393573562680000771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34087710382862833813335389 12782891393573562680000771)
                ·
                  refine ⟨19174337090360344020001157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12782891393573562680000771 19174337090360344020001157)
                  ·
                    refine ⟨3595188204442564503750217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19174337090360344020001157 3595188204442564503750217)
                    ·
                      refine ⟨2696391153331923377812663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595188204442564503750217 2696391153331923377812663)
                      ·
                        rfl

theorem cell23_5251203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_5251203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251203 prefixEnd_5251203 := by exact prefixLift 5251203
  have htrace : WordTrace (prefixWord ++ tailWord_5251203) baseStart_5251203 baseEnd_5251203 := by
    simpa [prefixWord, tailWord_5251203, baseEnd_5251203] using wordTrace_append hprefix tailTrace_5251203
  have hstable : (prefixWord ++ tailWord_5251203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251203).length < 2 ^ (prefixWord ++ tailWord_5251203).sum := by decide
  have hdescent : baseEnd_5251203 < baseStart_5251203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251219 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_5251219 : Nat := 118140960795 + 5251219 * 2 ^ 59
def prefixEnd_5251219 : Nat := 4983230072969 + 3 ^ 40 * 5251219 * 2
def baseEnd_5251219 : Nat := 2696399369022395315212589

theorem tailTrace_5251219 : CollatzResearch.WordTrace tailWord_5251219 prefixEnd_5251219 2696399369022395315212589 := by
  unfold tailWord_5251219
  simp only [CollatzResearch.WordTrace]
  refine ⟨191527691562737874649484711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127685127708491916432989807 191527691562737874649484711)
  ·
    refine ⟨287291537344106811974227067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191527691562737874649484711 287291537344106811974227067)
    ·
      refine ⟨430937306016160217961340601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287291537344106811974227067 430937306016160217961340601)
      ·
        refine ⟨323202979512120163471005451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430937306016160217961340601 323202979512120163471005451)
        ·
          refine ⟨484804469268180245206508177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323202979512120163471005451 484804469268180245206508177)
          ·
            refine ⟨363603351951135183904881133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484804469268180245206508177 363603351951135183904881133)
            ·
              refine ⟨136351256981675693964330425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363603351951135183904881133 136351256981675693964330425)
              ·
                refine ⟨102263442736256770473247819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136351256981675693964330425 102263442736256770473247819)
                ·
                  refine ⟨153395164104385155709871729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102263442736256770473247819 153395164104385155709871729)
                  ·
                    refine ⟨115046373078288866782403797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153395164104385155709871729 115046373078288866782403797)
                    ·
                      refine ⟨2696399369022395315212589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115046373078288866782403797 2696399369022395315212589)
                      ·
                        rfl

theorem cell23_5251219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_5251219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251219 prefixEnd_5251219 := by exact prefixLift 5251219
  have htrace : WordTrace (prefixWord ++ tailWord_5251219) baseStart_5251219 baseEnd_5251219 := by
    simpa [prefixWord, tailWord_5251219, baseEnd_5251219] using wordTrace_append hprefix tailTrace_5251219
  have hstable : (prefixWord ++ tailWord_5251219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251219).length < 2 ^ (prefixWord ++ tailWord_5251219).sum := by decide
  have hdescent : baseEnd_5251219 < baseStart_5251219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251224 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5251224 : Nat := 118140960795 + 5251224 * 2 ^ 59
def prefixEnd_5251224 : Nat := 4983230072969 + 3 ^ 40 * 5251224 * 2
def baseEnd_5251224 : Nat := 2696401936425667795650067

theorem tailTrace_5251224 : CollatzResearch.WordTrace tailWord_5251224 prefixEnd_5251224 2696401936425667795650067 := by
  unfold tailWord_5251224
  simp only [CollatzResearch.WordTrace]
  refine ⟨95763936963859880251708363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127685249285146507002277817 95763936963859880251708363)
  ·
    refine ⟨143645905445789820377562545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95763936963859880251708363 143645905445789820377562545)
    ·
      refine ⟨107734429084342365283171909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143645905445789820377562545 107734429084342365283171909)
      ·
        refine ⟨20200205453314193490594733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107734429084342365283171909 20200205453314193490594733)
        ·
          refine ⟨7575077044992822558973025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20200205453314193490594733 7575077044992822558973025)
          ·
            refine ⟨5681307783744616919229769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7575077044992822558973025 5681307783744616919229769)
            ·
              refine ⟨4260980837808462689422327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5681307783744616919229769 4260980837808462689422327)
              ·
                refine ⟨6391471256712694034133491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260980837808462689422327 6391471256712694034133491)
                ·
                  refine ⟨9587206885069041051200237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6391471256712694034133491 9587206885069041051200237)
                  ·
                    refine ⟨3595202581900890394200089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9587206885069041051200237 3595202581900890394200089)
                    ·
                      refine ⟨2696401936425667795650067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595202581900890394200089 2696401936425667795650067)
                      ·
                        rfl

theorem cell23_5251224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5251224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251224 prefixEnd_5251224 := by exact prefixLift 5251224
  have htrace : WordTrace (prefixWord ++ tailWord_5251224) baseStart_5251224 baseEnd_5251224 := by
    simpa [prefixWord, tailWord_5251224, baseEnd_5251224] using wordTrace_append hprefix tailTrace_5251224
  have hstable : (prefixWord ++ tailWord_5251224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251224).length < 2 ^ (prefixWord ++ tailWord_5251224).sum := by decide
  have hdescent : baseEnd_5251224 < baseStart_5251224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251377 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_5251377 : Nat := 118140960795 + 5251377 * 2 ^ 59
def prefixEnd_5251377 : Nat := 4983230072969 + 3 ^ 40 * 5251377 * 2
def baseEnd_5251377 : Nat := 2696480498965805697036863

theorem tailTrace_5251377 : CollatzResearch.WordTrace tailWord_5251377 prefixEnd_5251377 2696480498965805697036863 := by
  unfold tailWord_5251377
  simp only [CollatzResearch.WordTrace]
  refine ⟨191533454296165467633736385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127688969530776978422490923 191533454296165467633736385)
  ·
    refine ⟨143650090722124100725302289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191533454296165467633736385 143650090722124100725302289)
    ·
      refine ⟨107737568041593075543976717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143650090722124100725302289 107737568041593075543976717)
      ·
        refine ⟨40401588015597403328991269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107737568041593075543976717 40401588015597403328991269)
        ·
          refine ⟨7575297752924513124185863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40401588015597403328991269 7575297752924513124185863)
          ·
            refine ⟨11362946629386769686278795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7575297752924513124185863 11362946629386769686278795)
            ·
              refine ⟨17044419944080154529418193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11362946629386769686278795 17044419944080154529418193)
              ·
                refine ⟨12783314958060115897063645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17044419944080154529418193 12783314958060115897063645)
                ·
                  refine ⟨4793743109272543461398867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12783314958060115897063645 4793743109272543461398867)
                  ·
                    refine ⟨7190614663908815192098301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4793743109272543461398867 7190614663908815192098301)
                    ·
                      refine ⟨2696480498965805697036863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190614663908815192098301 2696480498965805697036863)
                      ·
                        rfl

theorem cell23_5251377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_5251377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251377 prefixEnd_5251377 := by exact prefixLift 5251377
  have htrace : WordTrace (prefixWord ++ tailWord_5251377) baseStart_5251377 baseEnd_5251377 := by
    simpa [prefixWord, tailWord_5251377, baseEnd_5251377] using wordTrace_append hprefix tailTrace_5251377
  have hstable : (prefixWord ++ tailWord_5251377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251377).length < 2 ^ (prefixWord ++ tailWord_5251377).sum := by decide
  have hdescent : baseEnd_5251377 < baseStart_5251377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251380 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_5251380 : Nat := 118140960795 + 5251380 * 2 ^ 59
def prefixEnd_5251380 : Nat := 4983230072969 + 3 ^ 40 * 5251380 * 2
def baseEnd_5251380 : Nat := 898827346469256395099783

theorem tailTrace_5251380 : CollatzResearch.WordTrace tailWord_5251380 prefixEnd_5251380 898827346469256395099783 := by
  unfold tailWord_5251380
  simp only [CollatzResearch.WordTrace]
  refine ⟨95766781857577299573047797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127689042476769732764063729 95766781857577299573047797)
  ·
    refine ⟨8978135799147871834973231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95766781857577299573047797 8978135799147871834973231)
    ·
      refine ⟨13467203698721807752459847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8978135799147871834973231 13467203698721807752459847)
      ·
        refine ⟨20200805548082711628689771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13467203698721807752459847 20200805548082711628689771)
        ·
          refine ⟨30301208322124067443034657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20200805548082711628689771 30301208322124067443034657)
          ·
            refine ⟨22725906241593050582275993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30301208322124067443034657 22725906241593050582275993)
            ·
              refine ⟨17044429681194787936706995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22725906241593050582275993 17044429681194787936706995)
              ·
                refine ⟨25566644521792181905060493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17044429681194787936706995 25566644521792181905060493)
                ·
                  refine ⟨9587491695672068214397685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25566644521792181905060493 9587491695672068214397685)
                  ·
                    refine ⟨898827346469256395099783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9587491695672068214397685 898827346469256395099783)
                    ·
                      rfl

theorem cell23_5251380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_5251380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251380 prefixEnd_5251380 := by exact prefixLift 5251380
  have htrace : WordTrace (prefixWord ++ tailWord_5251380) baseStart_5251380 baseEnd_5251380 := by
    simpa [prefixWord, tailWord_5251380, baseEnd_5251380] using wordTrace_append hprefix tailTrace_5251380
  have hstable : (prefixWord ++ tailWord_5251380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251380).length < 2 ^ (prefixWord ++ tailWord_5251380).sum := by decide
  have hdescent : baseEnd_5251380 < baseStart_5251380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251403 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 3]
def baseStart_5251403 : Nat := 118140960795 + 5251403 * 2 ^ 59
def prefixEnd_5251403 : Nat := 4983230072969 + 3 ^ 40 * 5251403 * 2
def baseEnd_5251403 : Nat := 2696493849462822595311743

theorem tailTrace_5251403 : CollatzResearch.WordTrace tailWord_5251403 prefixEnd_5251403 2696493849462822595311743 := by
  unfold tailWord_5251403
  simp only [CollatzResearch.WordTrace]
  refine ⟨191534402594071274074182863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127689601729380849382788575 191534402594071274074182863)
  ·
    refine ⟨287301603891106911111274295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191534402594071274074182863 287301603891106911111274295)
    ·
      refine ⟨430952405836660366666911443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287301603891106911111274295 430952405836660366666911443)
      ·
        refine ⟨646428608754990550000367165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430952405836660366666911443 646428608754990550000367165)
        ·
          refine ⟨242410728283121456250137687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 646428608754990550000367165 242410728283121456250137687)
          ·
            refine ⟨363616092424682184375206531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242410728283121456250137687 363616092424682184375206531)
            ·
              refine ⟨545424138637023276562809797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363616092424682184375206531 545424138637023276562809797)
              ·
                refine ⟨102267025994441864355526837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545424138637023276562809797 102267025994441864355526837)
                ·
                  refine ⟨9587533686978924783330641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102267025994441864355526837 9587533686978924783330641)
                  ·
                    refine ⟨7190650265234193587497981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9587533686978924783330641 7190650265234193587497981)
                    ·
                      refine ⟨2696493849462822595311743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190650265234193587497981 2696493849462822595311743)
                      ·
                        rfl

theorem cell23_5251403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 3].length) (baseStart_5251403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251403 prefixEnd_5251403 := by exact prefixLift 5251403
  have htrace : WordTrace (prefixWord ++ tailWord_5251403) baseStart_5251403 baseEnd_5251403 := by
    simpa [prefixWord, tailWord_5251403, baseEnd_5251403] using wordTrace_append hprefix tailTrace_5251403
  have hstable : (prefixWord ++ tailWord_5251403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251403).length < 2 ^ (prefixWord ++ tailWord_5251403).sum := by decide
  have hdescent : baseEnd_5251403 < baseStart_5251403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251427 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 2, 4]
def baseStart_5251427 : Nat := 118140960795 + 5251427 * 2 ^ 59
def prefixEnd_5251427 : Nat := 4983230072969 + 3 ^ 40 * 5251427 * 2
def baseEnd_5251427 : Nat := 898835390999510167137211

theorem tailTrace_5251427 : CollatzResearch.WordTrace tailWord_5251427 prefixEnd_5251427 898835390999510167137211 := by
  unfold tailWord_5251427
  simp only [CollatzResearch.WordTrace]
  refine ⟨191535277945984326173056535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127690185297322884115371023 191535277945984326173056535)
  ·
    refine ⟨287302916918976489259584803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191535277945984326173056535 287302916918976489259584803)
    ·
      refine ⟨430954375378464733889377205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287302916918976489259584803 430954375378464733889377205)
      ·
        refine ⟨40401972691731068802129113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 430954375378464733889377205 40401972691731068802129113)
        ·
          refine ⟨30301479518798301601596835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40401972691731068802129113 30301479518798301601596835)
          ·
            refine ⟨45452219278197452402395253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30301479518798301601596835 45452219278197452402395253)
            ·
              refine ⟨4261145557331011162724555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45452219278197452402395253 4261145557331011162724555)
              ·
                refine ⟨6391718335996516744086833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261145557331011162724555 6391718335996516744086833)
                ·
                  refine ⟨4793788751997387558065125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391718335996516744086833 4793788751997387558065125)
                  ·
                    refine ⟨898835390999510167137211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793788751997387558065125 898835390999510167137211)
                    ·
                      rfl

theorem cell23_5251427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 4].length) (baseStart_5251427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251427 prefixEnd_5251427 := by exact prefixLift 5251427
  have htrace : WordTrace (prefixWord ++ tailWord_5251427) baseStart_5251427 baseEnd_5251427 := by
    simpa [prefixWord, tailWord_5251427, baseEnd_5251427] using wordTrace_append hprefix tailTrace_5251427
  have hstable : (prefixWord ++ tailWord_5251427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251427).length < 2 ^ (prefixWord ++ tailWord_5251427).sum := by decide
  have hdescent : baseEnd_5251427 < baseStart_5251427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251434 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5251434 : Nat := 118140960795 + 5251434 * 2 ^ 59
def prefixEnd_5251434 : Nat := 4983230072969 + 3 ^ 40 * 5251434 * 2
def baseEnd_5251434 : Nat := 2696509767363111974024101

theorem tailTrace_5251434 : CollatzResearch.WordTrace tailWord_5251434 prefixEnd_5251434 2696509767363111974024101 := by
  unfold tailWord_5251434
  simp only [CollatzResearch.WordTrace]
  refine ⟨47883883314239741592140339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127690355504639310912374237 47883883314239741592140339)
  ·
    refine ⟨71825824971359612388210509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47883883314239741592140339 71825824971359612388210509)
    ·
      refine ⟨26934684364259854645578941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71825824971359612388210509 26934684364259854645578941)
      ·
        refine ⟨10100506636597445492092103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26934684364259854645578941 10100506636597445492092103)
        ·
          refine ⟨15150759954896168238138155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10100506636597445492092103 15150759954896168238138155)
          ·
            refine ⟨22726139932344252357207233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15150759954896168238138155 22726139932344252357207233)
            ·
              refine ⟨17044604949258189267905425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22726139932344252357207233 17044604949258189267905425)
              ·
                refine ⟨12783453711943641950929069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17044604949258189267905425 12783453711943641950929069)
                ·
                  refine ⟨4793795141978865731598401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12783453711943641950929069 4793795141978865731598401)
                  ·
                    refine ⟨3595346356484149298698801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4793795141978865731598401 3595346356484149298698801)
                    ·
                      refine ⟨2696509767363111974024101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595346356484149298698801 2696509767363111974024101)
                      ·
                        rfl

theorem cell23_5251434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5251434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251434 prefixEnd_5251434 := by exact prefixLift 5251434
  have htrace : WordTrace (prefixWord ++ tailWord_5251434) baseStart_5251434 baseEnd_5251434 := by
    simpa [prefixWord, tailWord_5251434, baseEnd_5251434] using wordTrace_append hprefix tailTrace_5251434
  have hstable : (prefixWord ++ tailWord_5251434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251434).length < 2 ^ (prefixWord ++ tailWord_5251434).sum := by decide
  have hdescent : baseEnd_5251434 < baseStart_5251434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251437 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5251437 : Nat := 118140960795 + 5251437 * 2 ^ 59
def prefixEnd_5251437 : Nat := 4983230072969 + 3 ^ 40 * 5251437 * 2
def baseEnd_5251437 : Nat := 2696511307805075462286587

theorem tailTrace_5251437 : CollatzResearch.WordTrace tailWord_5251437 prefixEnd_5251437 2696511307805075462286587 := by
  unfold tailWord_5251437
  simp only [CollatzResearch.WordTrace]
  refine ⟨191535642675948097880920565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127690428450632065253947043 191535642675948097880920565)
  ·
    refine ⟨17956466500870134176336303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191535642675948097880920565 17956466500870134176336303)
    ·
      refine ⟨26934699751305201264504455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17956466500870134176336303 26934699751305201264504455)
      ·
        refine ⟨40402049626957801896756683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26934699751305201264504455 40402049626957801896756683)
        ·
          refine ⟨60603074440436702845135025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40402049626957801896756683 60603074440436702845135025)
          ·
            refine ⟨45452305830327527133851269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60603074440436702845135025 45452305830327527133851269)
            ·
              refine ⟨8522307343186411337597113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45452305830327527133851269 8522307343186411337597113)
              ·
                refine ⟨6391730507389808503197835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8522307343186411337597113 6391730507389808503197835)
                ·
                  refine ⟨9587595761084712754796753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6391730507389808503197835 9587595761084712754796753)
                  ·
                    refine ⟨7190696820813534566097565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9587595761084712754796753 7190696820813534566097565)
                    ·
                      refine ⟨2696511307805075462286587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190696820813534566097565 2696511307805075462286587)
                      ·
                        rfl

theorem cell23_5251437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5251437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251437 prefixEnd_5251437 := by exact prefixLift 5251437
  have htrace : WordTrace (prefixWord ++ tailWord_5251437) baseStart_5251437 baseEnd_5251437 := by
    simpa [prefixWord, tailWord_5251437, baseEnd_5251437] using wordTrace_append hprefix tailTrace_5251437
  have hstable : (prefixWord ++ tailWord_5251437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251437).length < 2 ^ (prefixWord ++ tailWord_5251437).sum := by decide
  have hdescent : baseEnd_5251437 < baseStart_5251437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251440 : List Nat := [2, 1, 1, 1, 4, 5, 2, 7]
def baseStart_5251440 : Nat := 118140960795 + 5251440 * 2 ^ 59
def prefixEnd_5251440 : Nat := 4983230072969 + 3 ^ 40 * 5251440 * 2
def baseEnd_5251440 : Nat := 99870846231371812983299

theorem tailTrace_5251440 : CollatzResearch.WordTrace tailWord_5251440 prefixEnd_5251440 99870846231371812983299 := by
  unfold tailWord_5251440
  simp only [CollatzResearch.WordTrace]
  refine ⟨95767876047468614696639887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127690501396624819595519849 95767876047468614696639887)
  ·
    refine ⟨143651814071202922044959831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95767876047468614696639887 143651814071202922044959831)
    ·
      refine ⟨215477721106804383067439747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143651814071202922044959831 215477721106804383067439747)
      ·
        refine ⟨323216581660206574601159621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215477721106804383067439747 323216581660206574601159621)
        ·
          refine ⟨60603109061288732737717429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323216581660206574601159621 60603109061288732737717429)
          ·
            refine ⟨5681541474495818694161009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60603109061288732737717429 5681541474495818694161009)
            ·
              refine ⟨4261156105871864020620757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5681541474495818694161009 4261156105871864020620757)
              ·
                refine ⟨99870846231371812983299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4261156105871864020620757 99870846231371812983299)
                ·
                  rfl

theorem cell23_5251440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 7].length) (baseStart_5251440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251440 prefixEnd_5251440 := by exact prefixLift 5251440
  have htrace : WordTrace (prefixWord ++ tailWord_5251440) baseStart_5251440 baseEnd_5251440 := by
    simpa [prefixWord, tailWord_5251440, baseEnd_5251440] using wordTrace_append hprefix tailTrace_5251440
  have hstable : (prefixWord ++ tailWord_5251440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251440).length < 2 ^ (prefixWord ++ tailWord_5251440).sum := by decide
  have hdescent : baseEnd_5251440 < baseStart_5251440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251451 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 1, 2, 2]
def baseStart_5251451 : Nat := 118140960795 + 5251451 * 2 ^ 59
def prefixEnd_5251451 : Nat := 4983230072969 + 3 ^ 40 * 5251451 * 2
def baseEnd_5251451 : Nat := 2696518496534238407511523

theorem tailTrace_5251451 : CollatzResearch.WordTrace tailWord_5251451 prefixEnd_5251451 2696518496534238407511523 := by
  unfold tailWord_5251451
  simp only [CollatzResearch.WordTrace]
  refine ⟨191536153297897378271930207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127690768865264918847953471 191536153297897378271930207)
  ·
    refine ⟨287304229946846067407895311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191536153297897378271930207 287304229946846067407895311)
    ·
      refine ⟨430956344920269101111842967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287304229946846067407895311 430956344920269101111842967)
      ·
        refine ⟨646434517380403651667764451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430956344920269101111842967 646434517380403651667764451)
        ·
          refine ⟨969651776070605477501646677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646434517380403651667764451 969651776070605477501646677)
          ·
            refine ⟨5681553375413703969736211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 969651776070605477501646677 5681553375413703969736211)
            ·
              refine ⟨8522330063120555954604317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681553375413703969736211 8522330063120555954604317)
              ·
                refine ⟨3195873773670208482976619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8522330063120555954604317 3195873773670208482976619)
                ·
                  refine ⟨4793810660505312724464929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195873773670208482976619 4793810660505312724464929)
                  ·
                    refine ⟨3595357995378984543348697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4793810660505312724464929 3595357995378984543348697)
                    ·
                      refine ⟨2696518496534238407511523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595357995378984543348697 2696518496534238407511523)
                      ·
                        rfl

theorem cell23_5251451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 2, 2].length) (baseStart_5251451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251451 prefixEnd_5251451 := by exact prefixLift 5251451
  have htrace : WordTrace (prefixWord ++ tailWord_5251451) baseStart_5251451 baseEnd_5251451 := by
    simpa [prefixWord, tailWord_5251451, baseEnd_5251451] using wordTrace_append hprefix tailTrace_5251451
  have hstable : (prefixWord ++ tailWord_5251451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251451).length < 2 ^ (prefixWord ++ tailWord_5251451).sum := by decide
  have hdescent : baseEnd_5251451 < baseStart_5251451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251463 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_5251463 : Nat := 118140960795 + 5251463 * 2 ^ 59
def prefixEnd_5251463 : Nat := 4983230072969 + 3 ^ 40 * 5251463 * 2
def baseEnd_5251463 : Nat := 2696524658302092360561467

theorem tailTrace_5251463 : CollatzResearch.WordTrace tailWord_5251463 prefixEnd_5251463 2696524658302092360561467 := by
  unfold tailWord_5251463
  simp only [CollatzResearch.WordTrace]
  refine ⟨191536590973853904321367043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127691060649235936214244695 191536590973853904321367043)
  ·
    refine ⟨287304886460780856482050565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191536590973853904321367043 287304886460780856482050565)
    ·
      refine ⟨53869666211396410590384481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287304886460780856482050565 53869666211396410590384481)
      ·
        refine ⟨40402249658547307942788361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53869666211396410590384481 40402249658547307942788361)
        ·
          refine ⟨30301687243910480957091271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40402249658547307942788361 30301687243910480957091271)
          ·
            refine ⟨45452530865865721435636907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30301687243910480957091271 45452530865865721435636907)
            ·
              refine ⟨68178796298798582153455361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45452530865865721435636907 68178796298798582153455361)
              ·
                refine ⟨51134097224098936615091521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68178796298798582153455361 51134097224098936615091521)
                ·
                  refine ⟨38350572918074202461318641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51134097224098936615091521 38350572918074202461318641)
                  ·
                    refine ⟨28762929688555651845988981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38350572918074202461318641 28762929688555651845988981)
                    ·
                      refine ⟨2696524658302092360561467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28762929688555651845988981 2696524658302092360561467)
                      ·
                        rfl

theorem cell23_5251463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_5251463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251463 prefixEnd_5251463 := by exact prefixLift 5251463
  have htrace : WordTrace (prefixWord ++ tailWord_5251463) baseStart_5251463 baseEnd_5251463 := by
    simpa [prefixWord, tailWord_5251463, baseEnd_5251463] using wordTrace_append hprefix tailTrace_5251463
  have hstable : (prefixWord ++ tailWord_5251463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251463).length < 2 ^ (prefixWord ++ tailWord_5251463).sum := by decide
  have hdescent : baseEnd_5251463 < baseStart_5251463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251478 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5251478 : Nat := 118140960795 + 5251478 * 2 ^ 59
def prefixEnd_5251478 : Nat := 4983230072969 + 3 ^ 40 * 5251478 * 2
def baseEnd_5251478 : Nat := 898844120170636600624633

theorem tailTrace_5251478 : CollatzResearch.WordTrace tailWord_5251478 prefixEnd_5251478 898844120170636600624633 := by
  unfold tailWord_5251478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11971071129299972617697693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127691425379199707922108725 11971071129299972617697693)
  ·
    refine ⟨4489151673487489731636635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11971071129299972617697693 4489151673487489731636635)
    ·
      refine ⟨6733727510231234597454953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4489151673487489731636635 6733727510231234597454953)
      ·
        refine ⟨5050295632673425948091215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6733727510231234597454953 5050295632673425948091215)
        ·
          refine ⟨7575443449010138922136823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050295632673425948091215 7575443449010138922136823)
          ·
            refine ⟨11363165173515208383205235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7575443449010138922136823 11363165173515208383205235)
            ·
              refine ⟨17044747760272812574807853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11363165173515208383205235 17044747760272812574807853)
              ·
                refine ⟨6391780410102304715552945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17044747760272812574807853 6391780410102304715552945)
                ·
                  refine ⟨4793835307576728536664709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391780410102304715552945 4793835307576728536664709)
                  ·
                    refine ⟨898844120170636600624633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793835307576728536664709 898844120170636600624633)
                    ·
                      rfl

theorem cell23_5251478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5251478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251478 prefixEnd_5251478 := by exact prefixLift 5251478
  have htrace : WordTrace (prefixWord ++ tailWord_5251478) baseStart_5251478 baseEnd_5251478 := by
    simpa [prefixWord, tailWord_5251478, baseEnd_5251478] using wordTrace_append hprefix tailTrace_5251478
  have hstable : (prefixWord ++ tailWord_5251478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251478).length < 2 ^ (prefixWord ++ tailWord_5251478).sum := by decide
  have hdescent : baseEnd_5251478 < baseStart_5251478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251493 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_5251493 : Nat := 118140960795 + 5251493 * 2 ^ 59
def prefixEnd_5251493 : Nat := 4983230072969 + 3 ^ 40 * 5251493 * 2
def baseEnd_5251493 : Nat := 2696540062721727243186329

theorem tailTrace_5251493 : CollatzResearch.WordTrace tailWord_5251493 prefixEnd_5251493 2696540062721727243186329 := by
  unfold tailWord_5251493
  simp only [CollatzResearch.WordTrace]
  refine ⟨191537685163745219444959133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127691790109163479629972755 191537685163745219444959133)
  ·
    refine ⟨71826631936404457291859675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191537685163745219444959133 71826631936404457291859675)
    ·
      refine ⟨107739947904606685937789513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71826631936404457291859675 107739947904606685937789513)
      ·
        refine ⟨80804960928455014453342135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107739947904606685937789513 80804960928455014453342135)
        ·
          refine ⟨121207441392682521680013203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80804960928455014453342135 121207441392682521680013203)
          ·
            refine ⟨181811162089023782520019805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121207441392682521680013203 181811162089023782520019805)
            ·
              refine ⟨68179185783383918445007427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181811162089023782520019805 68179185783383918445007427)
              ·
                refine ⟨102268778675075877667511141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68179185783383918445007427 102268778675075877667511141)
                ·
                  refine ⟨19175396001576727062658339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102268778675075877667511141 19175396001576727062658339)
                  ·
                    refine ⟨28763094002365090593987509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19175396001576727062658339 28763094002365090593987509)
                    ·
                      refine ⟨2696540062721727243186329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28763094002365090593987509 2696540062721727243186329)
                      ·
                        rfl

theorem cell23_5251493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_5251493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251493 prefixEnd_5251493 := by exact prefixLift 5251493
  have htrace : WordTrace (prefixWord ++ tailWord_5251493) baseStart_5251493 baseEnd_5251493 := by
    simpa [prefixWord, tailWord_5251493, baseEnd_5251493] using wordTrace_append hprefix tailTrace_5251493
  have hstable : (prefixWord ++ tailWord_5251493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251493).length < 2 ^ (prefixWord ++ tailWord_5251493).sum := by decide
  have hdescent : baseEnd_5251493 < baseStart_5251493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251503 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_5251503 : Nat := 118140960795 + 5251503 * 2 ^ 59
def prefixEnd_5251503 : Nat := 4983230072969 + 3 ^ 40 * 5251503 * 2
def baseEnd_5251503 : Nat := 2696545197528272204061283

theorem tailTrace_5251503 : CollatzResearch.WordTrace tailWord_5251503 prefixEnd_5251503 2696545197528272204061283 := by
  unfold tailWord_5251503
  simp only [CollatzResearch.WordTrace]
  refine ⟨191538049893708991152823163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127692033262472660768548775 191538049893708991152823163)
  ·
    refine ⟨287307074840563486729234745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191538049893708991152823163 287307074840563486729234745)
    ·
      refine ⟨215480306130422615046926059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287307074840563486729234745 215480306130422615046926059)
      ·
        refine ⟨323220459195633922570389089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215480306130422615046926059 323220459195633922570389089)
        ·
          refine ⟨242415344396725441927791817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323220459195633922570389089 242415344396725441927791817)
          ·
            refine ⟨181811508297544081445843863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242415344396725441927791817 181811508297544081445843863)
            ·
              refine ⟨272717262446316122168765795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181811508297544081445843863 272717262446316122168765795)
              ·
                refine ⟨409075893669474183253148693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272717262446316122168765795 409075893669474183253148693)
                ·
                  refine ⟨19175432515756602339991345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 409075893669474183253148693 19175432515756602339991345)
                  ·
                    refine ⟨14381574386817451754993509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19175432515756602339991345 14381574386817451754993509)
                    ·
                      refine ⟨2696545197528272204061283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14381574386817451754993509 2696545197528272204061283)
                      ·
                        rfl

theorem cell23_5251503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_5251503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251503 prefixEnd_5251503 := by exact prefixLift 5251503
  have htrace : WordTrace (prefixWord ++ tailWord_5251503) baseStart_5251503 baseEnd_5251503 := by
    simpa [prefixWord, tailWord_5251503, baseEnd_5251503] using wordTrace_append hprefix tailTrace_5251503
  have hstable : (prefixWord ++ tailWord_5251503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251503).length < 2 ^ (prefixWord ++ tailWord_5251503).sum := by decide
  have hdescent : baseEnd_5251503 < baseStart_5251503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251560 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_5251560 : Nat := 118140960795 + 5251560 * 2 ^ 59
def prefixEnd_5251560 : Nat := 4983230072969 + 3 ^ 40 * 5251560 * 2
def baseEnd_5251560 : Nat := 898858155308526160349507

theorem tailTrace_5251560 : CollatzResearch.WordTrace tailWord_5251560 prefixEnd_5251560 898858155308526160349507 := by
  unfold tailWord_5251560
  simp only [CollatzResearch.WordTrace]
  refine ⟨95770064427251244943824067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127693419236334993258432089 95770064427251244943824067)
  ·
    refine ⟨143655096640876867415736101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95770064427251244943824067 143655096640876867415736101)
    ·
      refine ⟨26935330620164412640450519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143655096640876867415736101 26935330620164412640450519)
      ·
        refine ⟨40402995930246618960675779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26935330620164412640450519 40402995930246618960675779)
        ·
          refine ⟨60604493895369928441013669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40402995930246618960675779 60604493895369928441013669)
          ·
            refine ⟨11363342605381861582690063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60604493895369928441013669 11363342605381861582690063)
            ·
              refine ⟨17045013908072792374035095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11363342605381861582690063 17045013908072792374035095)
              ·
                refine ⟨25567520862109188561052643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17045013908072792374035095 25567520862109188561052643)
                ·
                  refine ⟨38351281293163782841578965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25567520862109188561052643 38351281293163782841578965)
                  ·
                    refine ⟨898858155308526160349507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38351281293163782841578965 898858155308526160349507)
                    ·
                      rfl

theorem cell23_5251560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_5251560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251560 prefixEnd_5251560 := by exact prefixLift 5251560
  have htrace : WordTrace (prefixWord ++ tailWord_5251560) baseStart_5251560 baseEnd_5251560 := by
    simpa [prefixWord, tailWord_5251560, baseEnd_5251560] using wordTrace_append hprefix tailTrace_5251560
  have hstable : (prefixWord ++ tailWord_5251560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251560).length < 2 ^ (prefixWord ++ tailWord_5251560).sum := by decide
  have hdescent : baseEnd_5251560 < baseStart_5251560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251580 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_5251580 : Nat := 118140960795 + 5251580 * 2 ^ 59
def prefixEnd_5251580 : Nat := 4983230072969 + 3 ^ 40 * 5251580 * 2
def baseEnd_5251580 : Nat := 2696584735538668402798429

theorem tailTrace_5251580 : CollatzResearch.WordTrace tailWord_5251580 prefixEnd_5251580 2696584735538668402798429 := by
  unfold tailWord_5251580
  simp only [CollatzResearch.WordTrace]
  refine ⟨95770429157215016651688097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127693905542953355535584129 95770429157215016651688097)
  ·
    refine ⟨71827821867911262488766073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95770429157215016651688097 71827821867911262488766073)
    ·
      refine ⟨53870866400933446866574555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71827821867911262488766073 53870866400933446866574555)
      ·
        refine ⟨80806299601400170299861833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53870866400933446866574555 80806299601400170299861833)
        ·
          refine ⟨60604724701050127724896375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80806299601400170299861833 60604724701050127724896375)
          ·
            refine ⟨90907087051575191587344563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60604724701050127724896375 90907087051575191587344563)
            ·
              refine ⟨136360630577362787381016845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90907087051575191587344563 136360630577362787381016845)
              ·
                refine ⟨51135236466511045267881317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136360630577362787381016845 51135236466511045267881317)
                ·
                  refine ⟨9587856837470820987727747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51135236466511045267881317 9587856837470820987727747)
                  ·
                    refine ⟨14381785256206231481591621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9587856837470820987727747 14381785256206231481591621)
                    ·
                      refine ⟨2696584735538668402798429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14381785256206231481591621 2696584735538668402798429)
                      ·
                        rfl

theorem cell23_5251580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_5251580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251580 prefixEnd_5251580 := by exact prefixLift 5251580
  have htrace : WordTrace (prefixWord ++ tailWord_5251580) baseStart_5251580 baseEnd_5251580 := by
    simpa [prefixWord, tailWord_5251580, baseEnd_5251580] using wordTrace_append hprefix tailTrace_5251580
  have hstable : (prefixWord ++ tailWord_5251580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251580).length < 2 ^ (prefixWord ++ tailWord_5251580).sum := by decide
  have hdescent : baseEnd_5251580 < baseStart_5251580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251617 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_5251617 : Nat := 118140960795 + 5251617 * 2 ^ 59
def prefixEnd_5251617 : Nat := 4983230072969 + 3 ^ 40 * 5251617 * 2
def baseEnd_5251617 : Nat := 2696603734322884758035759

theorem tailTrace_5251617 : CollatzResearch.WordTrace tailWord_5251617 prefixEnd_5251617 2696603734322884758035759 := by
  unfold tailWord_5251617
  simp only [CollatzResearch.WordTrace]
  refine ⟨191542207815295988622473105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127694805210197325748315403 191542207815295988622473105)
  ·
    refine ⟨143656655861471991466854829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191542207815295988622473105 143656655861471991466854829)
    ·
      refine ⟨53871245948051996800070561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143656655861471991466854829 53871245948051996800070561)
      ·
        refine ⟨40403434461038997600052921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53871245948051996800070561 40403434461038997600052921)
        ·
          refine ⟨30302575845779248200039691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40403434461038997600052921 30302575845779248200039691)
          ·
            refine ⟨45453863768668872300059537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30302575845779248200039691 45453863768668872300059537)
            ·
              refine ⟨34090397826501654225044653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45453863768668872300059537 34090397826501654225044653)
              ·
                refine ⟨12783899184938120334391745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34090397826501654225044653 12783899184938120334391745)
                ·
                  refine ⟨9587924388703590250793809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12783899184938120334391745 9587924388703590250793809)
                  ·
                    refine ⟨7190943291527692688095357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9587924388703590250793809 7190943291527692688095357)
                    ·
                      refine ⟨2696603734322884758035759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7190943291527692688095357 2696603734322884758035759)
                      ·
                        rfl

theorem cell23_5251617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_5251617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251617 prefixEnd_5251617 := by exact prefixLift 5251617
  have htrace : WordTrace (prefixWord ++ tailWord_5251617) baseStart_5251617 baseEnd_5251617 := by
    simpa [prefixWord, tailWord_5251617, baseEnd_5251617] using wordTrace_append hprefix tailTrace_5251617
  have hstable : (prefixWord ++ tailWord_5251617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251617).length < 2 ^ (prefixWord ++ tailWord_5251617).sum := by decide
  have hdescent : baseEnd_5251617 < baseStart_5251617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251641 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 1, 4]
def baseStart_5251641 : Nat := 118140960795 + 5251641 * 2 ^ 59
def prefixEnd_5251641 : Nat := 4983230072969 + 3 ^ 40 * 5251641 * 2
def baseEnd_5251641 : Nat := 898872019286197554711883

theorem tailTrace_5251641 : CollatzResearch.WordTrace tailWord_5251641 prefixEnd_5251641 898872019286197554711883 := by
  unfold tailWord_5251641
  simp only [CollatzResearch.WordTrace]
  refine ⟨191543083167209040721346777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127695388778139360480897851 191543083167209040721346777)
  ·
    refine ⟨143657312375406780541010083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191543083167209040721346777 143657312375406780541010083)
    ·
      refine ⟨215485968563110170811515125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143657312375406780541010083 215485968563110170811515125)
      ·
        refine ⟨20201809552791578513579543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215485968563110170811515125 20201809552791578513579543)
        ·
          refine ⟨30302714329187367770369315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20201809552791578513579543 30302714329187367770369315)
          ·
            refine ⟨45454071493781051655553973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30302714329187367770369315 45454071493781051655553973)
            ·
              refine ⟨4261319202541973592708185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45454071493781051655553973 4261319202541973592708185)
              ·
                refine ⟨3195989401906480194531139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261319202541973592708185 3195989401906480194531139)
                ·
                  refine ⟨4793984102859720291796709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195989401906480194531139 4793984102859720291796709)
                  ·
                    refine ⟨898872019286197554711883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793984102859720291796709 898872019286197554711883)
                    ·
                      rfl

theorem cell23_5251641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 4].length) (baseStart_5251641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251641 prefixEnd_5251641 := by exact prefixLift 5251641
  have htrace : WordTrace (prefixWord ++ tailWord_5251641) baseStart_5251641 baseEnd_5251641 := by
    simpa [prefixWord, tailWord_5251641, baseEnd_5251641] using wordTrace_append hprefix tailTrace_5251641
  have hstable : (prefixWord ++ tailWord_5251641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251641).length < 2 ^ (prefixWord ++ tailWord_5251641).sum := by decide
  have hdescent : baseEnd_5251641 < baseStart_5251641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251680 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_5251680 : Nat := 118140960795 + 5251680 * 2 ^ 59
def prefixEnd_5251680 : Nat := 4983230072969 + 3 ^ 40 * 5251680 * 2
def baseEnd_5251680 : Nat := 898878694534706003849323

theorem tailTrace_5251680 : CollatzResearch.WordTrace tailWord_5251680 prefixEnd_5251680 898878694534706003849323 := by
  unfold tailWord_5251680
  simp only [CollatzResearch.WordTrace]
  refine ⟨95772252807033875191008247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127696337076045166921344329 95772252807033875191008247)
  ·
    refine ⟨143658379210550812786512371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95772252807033875191008247 143658379210550812786512371)
    ·
      refine ⟨215487568815826219179768557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143658379210550812786512371 215487568815826219179768557)
      ·
        refine ⟨80807838305934832192413209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215487568815826219179768557 80807838305934832192413209)
        ·
          refine ⟨60605878729451124144309907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80807838305934832192413209 60605878729451124144309907)
          ·
            refine ⟨90908818094176686216464861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60605878729451124144309907 90908818094176686216464861)
            ·
              refine ⟨34090806785316257331174323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90908818094176686216464861 34090806785316257331174323)
              ·
                refine ⟨51136210177974385996761485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34090806785316257331174323 51136210177974385996761485)
                ·
                  refine ⟨19176078816740394748785557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51136210177974385996761485 19176078816740394748785557)
                  ·
                    refine ⟨898878694534706003849323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19176078816740394748785557 898878694534706003849323)
                    ·
                      rfl

theorem cell23_5251680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_5251680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251680 prefixEnd_5251680 := by exact prefixLift 5251680
  have htrace : WordTrace (prefixWord ++ tailWord_5251680) baseStart_5251680 baseEnd_5251680 := by
    simpa [prefixWord, tailWord_5251680, baseEnd_5251680] using wordTrace_append hprefix tailTrace_5251680
  have hstable : (prefixWord ++ tailWord_5251680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251680).length < 2 ^ (prefixWord ++ tailWord_5251680).sum := by decide
  have hdescent : baseEnd_5251680 < baseStart_5251680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251684 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_5251684 : Nat := 118140960795 + 5251684 * 2 ^ 59
def prefixEnd_5251684 : Nat := 4983230072969 + 3 ^ 40 * 5251684 * 2
def baseEnd_5251684 : Nat := 898879379175578665299317

theorem tailTrace_5251684 : CollatzResearch.WordTrace tailWord_5251684 prefixEnd_5251684 898879379175578665299317 := by
  unfold tailWord_5251684
  simp only [CollatzResearch.WordTrace]
  refine ⟨95772325753026629532581053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127696434337368839376774737 95772325753026629532581053)
  ·
    refine ⟨35914622157384986074717895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95772325753026629532581053 35914622157384986074717895)
    ·
      refine ⟨53871933236077479112076843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35914622157384986074717895 53871933236077479112076843)
      ·
        refine ⟨80807899854116218668115265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53871933236077479112076843 80807899854116218668115265)
        ·
          refine ⟨60605924890587164001086449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80807899854116218668115265 60605924890587164001086449)
          ·
            refine ⟨45454443667940373000814837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60605924890587164001086449 45454443667940373000814837)
            ·
              refine ⟨4261354093869409968826391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45454443667940373000814837 4261354093869409968826391)
              ·
                refine ⟨6392031140804114953239587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261354093869409968826391 6392031140804114953239587)
                ·
                  refine ⟨9588046711206172429859381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6392031140804114953239587 9588046711206172429859381)
                  ·
                    refine ⟨898879379175578665299317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9588046711206172429859381 898879379175578665299317)
                    ·
                      rfl

theorem cell23_5251684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_5251684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251684 prefixEnd_5251684 := by exact prefixLift 5251684
  have htrace : WordTrace (prefixWord ++ tailWord_5251684) baseStart_5251684 baseEnd_5251684 := by
    simpa [prefixWord, tailWord_5251684, baseEnd_5251684] using wordTrace_append hprefix tailTrace_5251684
  have hstable : (prefixWord ++ tailWord_5251684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251684).length < 2 ^ (prefixWord ++ tailWord_5251684).sum := by decide
  have hdescent : baseEnd_5251684 < baseStart_5251684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251698 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_5251698 : Nat := 118140960795 + 5251698 * 2 ^ 59
def prefixEnd_5251698 : Nat := 4983230072969 + 3 ^ 40 * 5251698 * 2
def baseEnd_5251698 : Nat := 2696645326255898941122887

theorem tailTrace_5251698 : CollatzResearch.WordTrace tailWord_5251698 prefixEnd_5251698 2696645326255898941122887 := by
  unfold tailWord_5251698
  simp only [CollatzResearch.WordTrace]
  refine ⟨47886290532000634864042937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127696774752001692970781165 47886290532000634864042937)
  ·
    refine ⟨35914717899000476148032203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47886290532000634864042937 35914717899000476148032203)
    ·
      refine ⟨53872076848500714222048305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35914717899000476148032203 53872076848500714222048305)
      ·
        refine ⟨40404057636375535666536229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53872076848500714222048305 40404057636375535666536229)
        ·
          refine ⟨7575760806820412937475543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40404057636375535666536229 7575760806820412937475543)
          ·
            refine ⟨11363641210230619406213315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7575760806820412937475543 11363641210230619406213315)
            ·
              refine ⟨17045461815345929109319973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11363641210230619406213315 17045461815345929109319973)
              ·
                refine ⟨3196024090377361707997495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17045461815345929109319973 3196024090377361707997495)
                ·
                  refine ⟨4794036135566042561996243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196024090377361707997495 4794036135566042561996243)
                  ·
                    refine ⟨7191054203349063842994365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794036135566042561996243 7191054203349063842994365)
                    ·
                      refine ⟨2696645326255898941122887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191054203349063842994365 2696645326255898941122887)
                      ·
                        rfl

theorem cell23_5251698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_5251698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251698 prefixEnd_5251698 := by exact prefixLift 5251698
  have htrace : WordTrace (prefixWord ++ tailWord_5251698) baseStart_5251698 baseEnd_5251698 := by
    simpa [prefixWord, tailWord_5251698, baseEnd_5251698] using wordTrace_append hprefix tailTrace_5251698
  have hstable : (prefixWord ++ tailWord_5251698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251698).length < 2 ^ (prefixWord ++ tailWord_5251698).sum := by decide
  have hdescent : baseEnd_5251698 < baseStart_5251698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251717 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_5251717 : Nat := 118140960795 + 5251717 * 2 ^ 59
def prefixEnd_5251717 : Nat := 4983230072969 + 3 ^ 40 * 5251717 * 2
def baseEnd_5251717 : Nat := 2696655082388334366785299

theorem tailTrace_5251717 : CollatzResearch.WordTrace tailWord_5251717 prefixEnd_5251717 2696655082388334366785299 := by
  unfold tailWord_5251717
  simp only [CollatzResearch.WordTrace]
  refine ⟨191545855114933705701113405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127697236743289137134075603 191545855114933705701113405)
  ·
    refine ⟨71829695668100139637917527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191545855114933705701113405 71829695668100139637917527)
    ·
      refine ⟨107744543502150209456876291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71829695668100139637917527 107744543502150209456876291)
      ·
        refine ⟨161616815253225314185314437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107744543502150209456876291 161616815253225314185314437)
        ·
          refine ⟨30303152859979746409746457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161616815253225314185314437 30303152859979746409746457)
          ·
            refine ⟨22727364644984809807309843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30303152859979746409746457 22727364644984809807309843)
            ·
              refine ⟨34091046967477214710964765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22727364644984809807309843 34091046967477214710964765)
              ·
                refine ⟨12784142612803955516611787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34091046967477214710964765 12784142612803955516611787)
                ·
                  refine ⟨19176213919205933274917681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12784142612803955516611787 19176213919205933274917681)
                  ·
                    refine ⟨14382160439404449956188261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19176213919205933274917681 14382160439404449956188261)
                    ·
                      refine ⟨2696655082388334366785299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14382160439404449956188261 2696655082388334366785299)
                      ·
                        rfl

theorem cell23_5251717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_5251717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251717 prefixEnd_5251717 := by exact prefixLift 5251717
  have htrace : WordTrace (prefixWord ++ tailWord_5251717) baseStart_5251717 baseEnd_5251717 := by
    simpa [prefixWord, tailWord_5251717, baseEnd_5251717] using wordTrace_append hprefix tailTrace_5251717
  have hstable : (prefixWord ++ tailWord_5251717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251717).length < 2 ^ (prefixWord ++ tailWord_5251717).sum := by decide
  have hdescent : baseEnd_5251717 < baseStart_5251717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251737 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_5251737 : Nat := 118140960795 + 5251737 * 2 ^ 59
def prefixEnd_5251737 : Nat := 4983230072969 + 3 ^ 40 * 5251737 * 2
def baseEnd_5251737 : Nat := 2696665352001424288535207

theorem tailTrace_5251737 : CollatzResearch.WordTrace tailWord_5251737 prefixEnd_5251737 2696665352001424288535207 := by
  unfold tailWord_5251737
  simp only [CollatzResearch.WordTrace]
  refine ⟨191546584574861249116841465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127697723049907499411227643 191546584574861249116841465)
  ·
    refine ⟨143659938431145936837631099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191546584574861249116841465 143659938431145936837631099)
    ·
      refine ⟨215489907646718905256446649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143659938431145936837631099 215489907646718905256446649)
      ·
        refine ⟨161617430735039178942334987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215489907646718905256446649 161617430735039178942334987)
        ·
          refine ⟨242426146102558768413502481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161617430735039178942334987 242426146102558768413502481)
          ·
            refine ⟨181819609576919076310126861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242426146102558768413502481 181819609576919076310126861)
            ·
              refine ⟨68182353591344653616297573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181819609576919076310126861 68182353591344653616297573)
              ·
                refine ⟨12784191298377122553055795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68182353591344653616297573 12784191298377122553055795)
                ·
                  refine ⟨19176286947565683829583693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12784191298377122553055795 19176286947565683829583693)
                  ·
                    refine ⟨7191107605337131436093885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19176286947565683829583693 7191107605337131436093885)
                    ·
                      refine ⟨2696665352001424288535207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191107605337131436093885 2696665352001424288535207)
                      ·
                        rfl

theorem cell23_5251737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_5251737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251737 prefixEnd_5251737 := by exact prefixLift 5251737
  have htrace : WordTrace (prefixWord ++ tailWord_5251737) baseStart_5251737 baseEnd_5251737 := by
    simpa [prefixWord, tailWord_5251737, baseEnd_5251737] using wordTrace_append hprefix tailTrace_5251737
  have hstable : (prefixWord ++ tailWord_5251737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251737).length < 2 ^ (prefixWord ++ tailWord_5251737).sum := by decide
  have hdescent : baseEnd_5251737 < baseStart_5251737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251741 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_5251741 : Nat := 118140960795 + 5251741 * 2 ^ 59
def prefixEnd_5251741 : Nat := 4983230072969 + 3 ^ 40 * 5251741 * 2
def baseEnd_5251741 : Nat := 2696667405924042272885189

theorem tailTrace_5251741 : CollatzResearch.WordTrace tailWord_5251741 prefixEnd_5251741 2696667405924042272885189 := by
  unfold tailWord_5251741
  simp only [CollatzResearch.WordTrace]
  refine ⟨191546730466846757799987077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127697820311231171866658051 191546730466846757799987077)
  ·
    refine ⟨35915011962533767087497577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191546730466846757799987077 35915011962533767087497577)
    ·
      refine ⟨26936258971900325315623183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35915011962533767087497577 26936258971900325315623183)
      ·
        refine ⟨40404388457850487973434775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26936258971900325315623183 40404388457850487973434775)
        ·
          refine ⟨60606582686775731960152163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40404388457850487973434775 60606582686775731960152163)
          ·
            refine ⟨90909874030163597940228245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60606582686775731960152163 90909874030163597940228245)
            ·
              refine ⟨4261400345163918653448199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90909874030163597940228245 4261400345163918653448199)
              ·
                refine ⟨6392100517745877980172299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261400345163918653448199 6392100517745877980172299)
                ·
                  refine ⟨9588150776618816970258449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6392100517745877980172299 9588150776618816970258449)
                  ·
                    refine ⟨7191113082464112727693837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9588150776618816970258449 7191113082464112727693837)
                    ·
                      refine ⟨2696667405924042272885189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191113082464112727693837 2696667405924042272885189)
                      ·
                        rfl

theorem cell23_5251741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_5251741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251741 prefixEnd_5251741 := by exact prefixLift 5251741
  have htrace : WordTrace (prefixWord ++ tailWord_5251741) baseStart_5251741 baseEnd_5251741 := by
    simpa [prefixWord, tailWord_5251741, baseEnd_5251741] using wordTrace_append hprefix tailTrace_5251741
  have hstable : (prefixWord ++ tailWord_5251741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251741).length < 2 ^ (prefixWord ++ tailWord_5251741).sum := by decide
  have hdescent : baseEnd_5251741 < baseStart_5251741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251789 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_5251789 : Nat := 118140960795 + 5251789 * 2 ^ 59
def prefixEnd_5251789 : Nat := 4983230072969 + 3 ^ 40 * 5251789 * 2
def baseEnd_5251789 : Nat := 2696692052995458085084969

theorem tailTrace_5251789 : CollatzResearch.WordTrace tailWord_5251789 prefixEnd_5251789 2696692052995458085084969 := by
  unfold tailWord_5251789
  simp only [CollatzResearch.WordTrace]
  refine ⟨191548481170672861997734421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127698987447115241331822947 191548481170672861997734421)
  ·
    refine ⟨8978835054875290406143801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191548481170672861997734421 8978835054875290406143801)
    ·
      refine ⟨6734126291156467804607851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8978835054875290406143801 6734126291156467804607851)
      ·
        refine ⟨10101189436734701706911777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6734126291156467804607851 10101189436734701706911777)
        ·
          refine ⟨7575892077551026280183833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10101189436734701706911777 7575892077551026280183833)
          ·
            refine ⟨5681919058163269710137875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7575892077551026280183833 5681919058163269710137875)
            ·
              refine ⟨8522878587244904565206813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681919058163269710137875 8522878587244904565206813)
              ·
                refine ⟨3196079470216839211952555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8522878587244904565206813 3196079470216839211952555)
                ·
                  refine ⟨4794119205325258817928833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196079470216839211952555 4794119205325258817928833)
                  ·
                    refine ⟨3595589403993944113446625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4794119205325258817928833 3595589403993944113446625)
                    ·
                      refine ⟨2696692052995458085084969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595589403993944113446625 2696692052995458085084969)
                      ·
                        rfl

theorem cell23_5251789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_5251789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251789 prefixEnd_5251789 := by exact prefixLift 5251789
  have htrace : WordTrace (prefixWord ++ tailWord_5251789) baseStart_5251789 baseEnd_5251789 := by
    simpa [prefixWord, tailWord_5251789, baseEnd_5251789] using wordTrace_append hprefix tailTrace_5251789
  have hstable : (prefixWord ++ tailWord_5251789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251789).length < 2 ^ (prefixWord ++ tailWord_5251789).sum := by decide
  have hdescent : baseEnd_5251789 < baseStart_5251789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251817 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 7]
def baseStart_5251817 : Nat := 118140960795 + 5251817 * 2 ^ 59
def prefixEnd_5251817 : Nat := 4983230072969 + 3 ^ 40 * 5251817 * 2
def baseEnd_5251817 : Nat := 299634047828198219503871

theorem tailTrace_5251817 : CollatzResearch.WordTrace tailWord_5251817 prefixEnd_5251817 299634047828198219503871 := by
  unfold tailWord_5251817
  simp only [CollatzResearch.WordTrace]
  refine ⟨191549502414571422779753705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127699668276380948519835803 191549502414571422779753705)
  ·
    refine ⟨143662126810928567084815279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191549502414571422779753705 143662126810928567084815279)
    ·
      refine ⟨215493190216392850627222919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143662126810928567084815279 215493190216392850627222919)
      ·
        refine ⟨323239785324589275940834379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215493190216392850627222919 323239785324589275940834379)
        ·
          refine ⟨484859677986883913911251569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323239785324589275940834379 484859677986883913911251569)
          ·
            refine ⟨363644758490162935433438677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484859677986883913911251569 363644758490162935433438677)
            ·
              refine ⟨8522924027113193799221219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 363644758490162935433438677 8522924027113193799221219)
              ·
                refine ⟨12784386040669790698831829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8522924027113193799221219 12784386040669790698831829)
                ·
                  refine ⟨299634047828198219503871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12784386040669790698831829 299634047828198219503871)
                  ·
                    rfl

theorem cell23_5251817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_5251817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251817 prefixEnd_5251817 := by exact prefixLift 5251817
  have htrace : WordTrace (prefixWord ++ tailWord_5251817) baseStart_5251817 baseEnd_5251817 := by
    simpa [prefixWord, tailWord_5251817, baseEnd_5251817] using wordTrace_append hprefix tailTrace_5251817
  have hstable : (prefixWord ++ tailWord_5251817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251817).length < 2 ^ (prefixWord ++ tailWord_5251817).sum := by decide
  have hdescent : baseEnd_5251817 < baseStart_5251817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251827 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 3]
def baseStart_5251827 : Nat := 118140960795 + 5251827 * 2 ^ 59
def prefixEnd_5251827 : Nat := 4983230072969 + 3 ^ 40 * 5251827 * 2
def baseEnd_5251827 : Nat := 2696711565260328936409793

theorem tailTrace_5251827 : CollatzResearch.WordTrace tailWord_5251827 prefixEnd_5251827 2696711565260328936409793 := by
  unfold tailWord_5251827
  simp only [CollatzResearch.WordTrace]
  refine ⟨191549867144535194487617735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127699911429690129658411823 191549867144535194487617735)
  ·
    refine ⟨287324800716802791731426603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191549867144535194487617735 287324800716802791731426603)
    ·
      refine ⟨430987201075204187597139905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287324800716802791731426603 430987201075204187597139905)
      ·
        refine ⟨323240400806403140697854929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430987201075204187597139905 323240400806403140697854929)
        ·
          refine ⟨242430300604802355523391197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323240400806403140697854929 242430300604802355523391197)
          ·
            refine ⟨90911362726800883321271699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242430300604802355523391197 90911362726800883321271699)
            ·
              refine ⟨136367044090201324981907549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90911362726800883321271699 136367044090201324981907549)
              ·
                refine ⟨51137641533825496868215331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136367044090201324981907549 51137641533825496868215331)
                ·
                  refine ⟨76706462300738245302322997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51137641533825496868215331 76706462300738245302322997)
                  ·
                    refine ⟨7191230840694210497092781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76706462300738245302322997 7191230840694210497092781)
                    ·
                      refine ⟨2696711565260328936409793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191230840694210497092781 2696711565260328936409793)
                      ·
                        rfl

theorem cell23_5251827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_5251827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251827 prefixEnd_5251827 := by exact prefixLift 5251827
  have htrace : WordTrace (prefixWord ++ tailWord_5251827) baseStart_5251827 baseEnd_5251827 := by
    simpa [prefixWord, tailWord_5251827, baseEnd_5251827] using wordTrace_append hprefix tailTrace_5251827
  have hstable : (prefixWord ++ tailWord_5251827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251827).length < 2 ^ (prefixWord ++ tailWord_5251827).sum := by decide
  have hdescent : baseEnd_5251827 < baseStart_5251827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251857 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_5251857 : Nat := 118140960795 + 5251857 * 2 ^ 59
def prefixEnd_5251857 : Nat := 4983230072969 + 3 ^ 40 * 5251857 * 2
def baseEnd_5251857 : Nat := 2696726969679963819034655

theorem tailTrace_5251857 : CollatzResearch.WordTrace tailWord_5251857 prefixEnd_5251857 2696726969679963819034655 := by
  unfold tailWord_5251857
  simp only [CollatzResearch.WordTrace]
  refine ⟨191550961334426509611209825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127700640889617673074139883 191550961334426509611209825)
  ·
    refine ⟨143663221000819882208407369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191550961334426509611209825 143663221000819882208407369)
    ·
      refine ⟨107747415750614911656305527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143663221000819882208407369 107747415750614911656305527)
      ·
        refine ⟨161621123625922367484458291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107747415750614911656305527 161621123625922367484458291)
        ·
          refine ⟨242431685438883551226687437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161621123625922367484458291 242431685438883551226687437)
          ·
            refine ⟨90911882039581331710007789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242431685438883551226687437 90911882039581331710007789)
            ·
              refine ⟨34091955764842999391252921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90911882039581331710007789 34091955764842999391252921)
              ·
                refine ⟨25568966823632249543439691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34091955764842999391252921 25568966823632249543439691)
                ·
                  refine ⟨38353450235448374315159537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25568966823632249543439691 38353450235448374315159537)
                  ·
                    refine ⟨28765087676586280736369653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38353450235448374315159537 28765087676586280736369653)
                    ·
                      refine ⟨2696726969679963819034655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28765087676586280736369653 2696726969679963819034655)
                      ·
                        rfl

theorem cell23_5251857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_5251857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251857 prefixEnd_5251857 := by exact prefixLift 5251857
  have htrace : WordTrace (prefixWord ++ tailWord_5251857) baseStart_5251857 baseEnd_5251857 := by
    simpa [prefixWord, tailWord_5251857, baseEnd_5251857] using wordTrace_append hprefix tailTrace_5251857
  have hstable : (prefixWord ++ tailWord_5251857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251857).length < 2 ^ (prefixWord ++ tailWord_5251857).sum := by decide
  have hdescent : baseEnd_5251857 < baseStart_5251857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251868 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 5]
def baseStart_5251868 : Nat := 118140960795 + 5251868 * 2 ^ 59
def prefixEnd_5251868 : Nat := 4983230072969 + 3 ^ 40 * 5251868 * 2
def baseEnd_5251868 : Nat := 299636957551907030666345

theorem tailTrace_5251868 : CollatzResearch.WordTrace tailWord_5251868 prefixEnd_5251868 299636957551907030666345 := by
  unfold tailWord_5251868
  simp only [CollatzResearch.WordTrace]
  refine ⟨95775681268693329244930129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127700908358257772326573505 95775681268693329244930129)
  ·
    refine ⟨71831760951519996933697597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95775681268693329244930129 71831760951519996933697597)
    ·
      refine ⟨26936910356819998850136599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71831760951519996933697597 26936910356819998850136599)
      ·
        refine ⟨40405365535229998275204899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26936910356819998850136599 40405365535229998275204899)
        ·
          refine ⟨60608048302844997412807349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40405365535229998275204899 60608048302844997412807349)
          ·
            refine ⟨5682004528391718507450689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60608048302844997412807349 5682004528391718507450689)
            ·
              refine ⟨4261503396293788880588017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682004528391718507450689 4261503396293788880588017)
              ·
                refine ⟨3196127547220341660441013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261503396293788880588017 3196127547220341660441013)
                ·
                  refine ⟨299636957551907030666345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3196127547220341660441013 299636957551907030666345)
                  ·
                    rfl

theorem cell23_5251868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_5251868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251868 prefixEnd_5251868 := by exact prefixLift 5251868
  have htrace : WordTrace (prefixWord ++ tailWord_5251868) baseStart_5251868 baseEnd_5251868 := by
    simpa [prefixWord, tailWord_5251868, baseEnd_5251868] using wordTrace_append hprefix tailTrace_5251868
  have hstable : (prefixWord ++ tailWord_5251868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251868).length < 2 ^ (prefixWord ++ tailWord_5251868).sum := by decide
  have hdescent : baseEnd_5251868 < baseStart_5251868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251874 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5251874 : Nat := 118140960795 + 5251874 * 2 ^ 59
def prefixEnd_5251874 : Nat := 4983230072969 + 3 ^ 40 * 5251874 * 2
def baseEnd_5251874 : Nat := 2696735698851090252522077

theorem tailTrace_5251874 : CollatzResearch.WordTrace tailWord_5251874 prefixEnd_5251874 2696735698851090252522077 := by
  unfold tailWord_5251874
  simp only [CollatzResearch.WordTrace]
  refine ⟨47887895343841230378644669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127701054250243281009719117 47887895343841230378644669)
  ·
    refine ⟨17957960753940461391991751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47887895343841230378644669 17957960753940461391991751)
    ·
      refine ⟨26936941130910692087987627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17957960753940461391991751 26936941130910692087987627)
      ·
        refine ⟨40405411696366038131981441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26936941130910692087987627 40405411696366038131981441)
        ·
          refine ⟨30304058772274528598986081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40405411696366038131981441 30304058772274528598986081)
          ·
            refine ⟨22728044079205896449239561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30304058772274528598986081 22728044079205896449239561)
            ·
              refine ⟨17046033059404422336929671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22728044079205896449239561 17046033059404422336929671)
              ·
                refine ⟨25569049589106633505394507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17046033059404422336929671 25569049589106633505394507)
                ·
                  refine ⟨38353574383659950258091761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25569049589106633505394507 38353574383659950258091761)
                  ·
                    refine ⟨28765180787744962693568821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38353574383659950258091761 28765180787744962693568821)
                    ·
                      refine ⟨2696735698851090252522077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28765180787744962693568821 2696735698851090252522077)
                      ·
                        rfl

theorem cell23_5251874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5251874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251874 prefixEnd_5251874 := by exact prefixLift 5251874
  have htrace : WordTrace (prefixWord ++ tailWord_5251874) baseStart_5251874 baseEnd_5251874 := by
    simpa [prefixWord, tailWord_5251874, baseEnd_5251874] using wordTrace_append hprefix tailTrace_5251874
  have hstable : (prefixWord ++ tailWord_5251874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251874).length < 2 ^ (prefixWord ++ tailWord_5251874).sum := by decide
  have hdescent : baseEnd_5251874 < baseStart_5251874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251898 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_5251898 : Nat := 118140960795 + 5251898 * 2 ^ 59
def prefixEnd_5251898 : Nat := 4983230072969 + 3 ^ 40 * 5251898 * 2
def baseEnd_5251898 : Nat := 898916007462266052873989

theorem tailTrace_5251898 : CollatzResearch.WordTrace tailWord_5251898 prefixEnd_5251898 898916007462266052873989 := by
  unfold tailWord_5251898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47888114181819493403363087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127701637818185315742301565 47888114181819493403363087)
  ·
    refine ⟨71832171272729240105044631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47888114181819493403363087 71832171272729240105044631)
    ·
      refine ⟨107748256909093860157566947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71832171272729240105044631 107748256909093860157566947)
      ·
        refine ⟨161622385363640790236350421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107748256909093860157566947 161622385363640790236350421)
        ·
          refine ⟨3788024656960331021164463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 161622385363640790236350421 3788024656960331021164463)
          ·
            refine ⟨5682036985440496531746695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788024656960331021164463 5682036985440496531746695)
            ·
              refine ⟨8523055478160744797620043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682036985440496531746695 8523055478160744797620043)
              ·
                refine ⟨12784583217241117196430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8523055478160744797620043 12784583217241117196430065)
                ·
                  refine ⟨9588437412930837897322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12784583217241117196430065 9588437412930837897322549)
                  ·
                    refine ⟨898916007462266052873989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9588437412930837897322549 898916007462266052873989)
                    ·
                      rfl

theorem cell23_5251898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_5251898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251898 prefixEnd_5251898 := by exact prefixLift 5251898
  have htrace : WordTrace (prefixWord ++ tailWord_5251898) baseStart_5251898 baseEnd_5251898 := by
    simpa [prefixWord, tailWord_5251898, baseEnd_5251898] using wordTrace_append hprefix tailTrace_5251898
  have hstable : (prefixWord ++ tailWord_5251898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251898).length < 2 ^ (prefixWord ++ tailWord_5251898).sum := by decide
  have hdescent : baseEnd_5251898 < baseStart_5251898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251901 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5251901 : Nat := 118140960795 + 5251901 * 2 ^ 59
def prefixEnd_5251901 : Nat := 4983230072969 + 3 ^ 40 * 5251901 * 2
def baseEnd_5251901 : Nat := 2696749562828761646884453

theorem tailTrace_5251901 : CollatzResearch.WordTrace tailWord_5251901 prefixEnd_5251901 2696749562828761646884453 := by
  unfold tailWord_5251901
  simp only [CollatzResearch.WordTrace]
  refine ⟨191552566146267105125811557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127701710764178070083874371 191552566146267105125811557)
  ·
    refine ⟨35916106152425082211089667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191552566146267105125811557 35916106152425082211089667)
    ·
      refine ⟨53874159228637623316634501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35916106152425082211089667 53874159228637623316634501)
      ·
        refine ⟨10101404855369554371868969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53874159228637623316634501 10101404855369554371868969)
        ·
          refine ⟨7576053641527165778901727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10101404855369554371868969 7576053641527165778901727)
          ·
            refine ⟨11364080462290748668352591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7576053641527165778901727 11364080462290748668352591)
            ·
              refine ⟨17046120693436123002528887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11364080462290748668352591 17046120693436123002528887)
              ·
                refine ⟨25569181040154184503793331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17046120693436123002528887 25569181040154184503793331)
                ·
                  refine ⟨38353771560231276755689997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25569181040154184503793331 38353771560231276755689997)
                  ·
                    refine ⟨14382664335086728783383749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38353771560231276755689997 14382664335086728783383749)
                    ·
                      refine ⟨2696749562828761646884453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14382664335086728783383749 2696749562828761646884453)
                      ·
                        rfl

theorem cell23_5251901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5251901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251901 prefixEnd_5251901 := by exact prefixLift 5251901
  have htrace : WordTrace (prefixWord ++ tailWord_5251901) baseStart_5251901 baseEnd_5251901 := by
    simpa [prefixWord, tailWord_5251901, baseEnd_5251901] using wordTrace_append hprefix tailTrace_5251901
  have hstable : (prefixWord ++ tailWord_5251901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251901).length < 2 ^ (prefixWord ++ tailWord_5251901).sum := by decide
  have hdescent : baseEnd_5251901 < baseStart_5251901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251907 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 8]
def baseStart_5251907 : Nat := 118140960795 + 5251907 * 2 ^ 59
def prefixEnd_5251907 : Nat := 4983230072969 + 3 ^ 40 * 5251907 * 2
def baseEnd_5251907 : Nat := 299639182634743180378825

theorem tailTrace_5251907 : CollatzResearch.WordTrace tailWord_5251907 prefixEnd_5251907 299639182634743180378825 := by
  unfold tailWord_5251907
  simp only [CollatzResearch.WordTrace]
  refine ⟨191552784984245368150529975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127701856656163578767019983 191552784984245368150529975)
  ·
    refine ⟨287329177476368052225794963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191552784984245368150529975 287329177476368052225794963)
    ·
      refine ⟨430993766214552078338692445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287329177476368052225794963 430993766214552078338692445)
      ·
        refine ⟨161622662330457029377009667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430993766214552078338692445 161622662330457029377009667)
        ·
          refine ⟨242433993495685544065514501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161622662330457029377009667 242433993495685544065514501)
          ·
            refine ⟨45456373780441039512283969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242433993495685544065514501 45456373780441039512283969)
            ·
              refine ⟨34092280335330779634212977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45456373780441039512283969 34092280335330779634212977)
              ·
                refine ⟨25569210251498084725659733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34092280335330779634212977 25569210251498084725659733)
                ·
                  refine ⟨299639182634743180378825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25569210251498084725659733 299639182634743180378825)
                  ·
                    rfl

theorem cell23_5251907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 8].length) (baseStart_5251907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251907 prefixEnd_5251907 := by exact prefixLift 5251907
  have htrace : WordTrace (prefixWord ++ tailWord_5251907) baseStart_5251907 baseEnd_5251907 := by
    simpa [prefixWord, tailWord_5251907, baseEnd_5251907] using wordTrace_append hprefix tailTrace_5251907
  have hstable : (prefixWord ++ tailWord_5251907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251907).length < 2 ^ (prefixWord ++ tailWord_5251907).sum := by decide
  have hdescent : baseEnd_5251907 < baseStart_5251907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251937 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_5251937 : Nat := 118140960795 + 5251937 * 2 ^ 59
def prefixEnd_5251937 : Nat := 4983230072969 + 3 ^ 40 * 5251937 * 2
def baseEnd_5251937 : Nat := 898922682710774502011429

theorem tailTrace_5251937 : CollatzResearch.WordTrace tailWord_5251937 prefixEnd_5251937 898922682710774502011429 := by
  unfold tailWord_5251937
  simp only [CollatzResearch.WordTrace]
  refine ⟨191553879174136683274122065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127702586116091122182748043 191553879174136683274122065)
  ·
    refine ⟨143665409380602512455591549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191553879174136683274122065 143665409380602512455591549)
    ·
      refine ⟨53874528517725942170846831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143665409380602512455591549 53874528517725942170846831)
      ·
        refine ⟨80811792776588913256270247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53874528517725942170846831 80811792776588913256270247)
        ·
          refine ⟨121217689164883369884405371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80811792776588913256270247 121217689164883369884405371)
          ·
            refine ⟨181826533747325054826608057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121217689164883369884405371 181826533747325054826608057)
            ·
              refine ⟨136369900310493791119956043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181826533747325054826608057 136369900310493791119956043)
              ·
                refine ⟨204554850465740686679934065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136369900310493791119956043 204554850465740686679934065)
                ·
                  refine ⟨153416137849305515009950549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204554850465740686679934065 153416137849305515009950549)
                  ·
                    refine ⟨898922682710774502011429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 153416137849305515009950549 898922682710774502011429)
                    ·
                      rfl

theorem cell23_5251937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_5251937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251937 prefixEnd_5251937 := by exact prefixLift 5251937
  have htrace : WordTrace (prefixWord ++ tailWord_5251937) baseStart_5251937 baseEnd_5251937 := by
    simpa [prefixWord, tailWord_5251937, baseEnd_5251937] using wordTrace_append hprefix tailTrace_5251937
  have hstable : (prefixWord ++ tailWord_5251937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251937).length < 2 ^ (prefixWord ++ tailWord_5251937).sum := by decide
  have hdescent : baseEnd_5251937 < baseStart_5251937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251947 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_5251947 : Nat := 118140960795 + 5251947 * 2 ^ 59
def prefixEnd_5251947 : Nat := 4983230072969 + 3 ^ 40 * 5251947 * 2
def baseEnd_5251947 : Nat := 2696773182938868466909241

theorem tailTrace_5251947 : CollatzResearch.WordTrace tailWord_5251947 prefixEnd_5251947 2696773182938868466909241 := by
  unfold tailWord_5251947
  simp only [CollatzResearch.WordTrace]
  refine ⟨191554243904100454981986095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127702829269400303321324063 191554243904100454981986095)
  ·
    refine ⟨287331365856150682472979143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191554243904100454981986095 287331365856150682472979143)
    ·
      refine ⟨430997048784226023709468715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287331365856150682472979143 430997048784226023709468715)
      ·
        refine ⟨646495573176339035564203073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430997048784226023709468715 646495573176339035564203073)
        ·
          refine ⟨484871679882254276673152305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646495573176339035564203073 484871679882254276673152305)
          ·
            refine ⟨363653759911690707504864229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484871679882254276673152305 363653759911690707504864229)
            ·
              refine ⟨68185079983442007657162043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 363653759911690707504864229 68185079983442007657162043)
              ·
                refine ⟨102277619975163011485743065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68185079983442007657162043 102277619975163011485743065)
                ·
                  refine ⟨76708214981372258614307299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102277619975163011485743065 76708214981372258614307299)
                  ·
                    refine ⟨115062322472058387921460949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76708214981372258614307299 115062322472058387921460949)
                    ·
                      refine ⟨2696773182938868466909241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115062322472058387921460949 2696773182938868466909241)
                      ·
                        rfl

theorem cell23_5251947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_5251947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251947 prefixEnd_5251947 := by exact prefixLift 5251947
  have htrace : WordTrace (prefixWord ++ tailWord_5251947) baseStart_5251947 baseEnd_5251947 := by
    simpa [prefixWord, tailWord_5251947, baseEnd_5251947] using wordTrace_append hprefix tailTrace_5251947
  have hstable : (prefixWord ++ tailWord_5251947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251947).length < 2 ^ (prefixWord ++ tailWord_5251947).sum := by decide
  have hdescent : baseEnd_5251947 < baseStart_5251947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251954 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_5251954 : Nat := 118140960795 + 5251954 * 2 ^ 59
def prefixEnd_5251954 : Nat := 4983230072969 + 3 ^ 40 * 5251954 * 2
def baseEnd_5251954 : Nat := 898925592434483313173903

theorem tailTrace_5251954 : CollatzResearch.WordTrace tailWord_5251954 prefixEnd_5251954 898925592434483313173903 := by
  unfold tailWord_5251954
  simp only [CollatzResearch.WordTrace]
  refine ⟨47888624803768773794372729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127702999476716730118327277 47888624803768773794372729)
  ·
    refine ⟨35916468602826580345779547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47888624803768773794372729 35916468602826580345779547)
    ·
      refine ⟨53874702904239870518669321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35916468602826580345779547 53874702904239870518669321)
      ·
        refine ⟨40406027178179902889001991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53874702904239870518669321 40406027178179902889001991)
        ·
          refine ⟨60609040767269854333502987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40406027178179902889001991 60609040767269854333502987)
          ·
            refine ⟨90913561150904781500254481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60609040767269854333502987 90913561150904781500254481)
            ·
              refine ⟨68185170863178586125190861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90913561150904781500254481 68185170863178586125190861)
              ·
                refine ⟨25569439073691969796946573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68185170863178586125190861 25569439073691969796946573)
                ·
                  refine ⟨9588539652634488673854965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25569439073691969796946573 9588539652634488673854965)
                  ·
                    refine ⟨898925592434483313173903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9588539652634488673854965 898925592434483313173903)
                    ·
                      rfl

theorem cell23_5251954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_5251954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251954 prefixEnd_5251954 := by exact prefixLift 5251954
  have htrace : WordTrace (prefixWord ++ tailWord_5251954) baseStart_5251954 baseEnd_5251954 := by
    simpa [prefixWord, tailWord_5251954, baseEnd_5251954] using wordTrace_append hprefix tailTrace_5251954
  have hstable : (prefixWord ++ tailWord_5251954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251954).length < 2 ^ (prefixWord ++ tailWord_5251954).sum := by decide
  have hdescent : baseEnd_5251954 < baseStart_5251954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251961 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 1, 5, 2]
def baseStart_5251961 : Nat := 118140960795 + 5251961 * 2 ^ 59
def prefixEnd_5251961 : Nat := 4983230072969 + 3 ^ 40 * 5251961 * 2
def baseEnd_5251961 : Nat := 2696780371668031412134177

theorem tailTrace_5251961 : CollatzResearch.WordTrace tailWord_5251961 prefixEnd_5251961 2696780371668031412134177 := by
  unfold tailWord_5251961
  simp only [CollatzResearch.WordTrace]
  refine ⟨191554754526049735372995737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127703169684033156915330491 191554754526049735372995737)
  ·
    refine ⟨143666065894537301529746803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191554754526049735372995737 143666065894537301529746803)
    ·
      refine ⟨215499098841805952294620205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143666065894537301529746803 215499098841805952294620205)
      ·
        refine ⟨80812162065677232110482577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215499098841805952294620205 80812162065677232110482577)
        ·
          refine ⟨60609121549257924082861933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80812162065677232110482577 60609121549257924082861933)
          ·
            refine ⟨22728420580971721531073225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60609121549257924082861933 22728420580971721531073225)
            ·
              refine ⟨17046315435728791148304919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22728420580971721531073225 17046315435728791148304919)
              ·
                refine ⟨25569473153593186722457379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17046315435728791148304919 25569473153593186722457379)
                ·
                  refine ⟨38354209730389780083686069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25569473153593186722457379 38354209730389780083686069)
                  ·
                    refine ⟨3595707162224041882845569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38354209730389780083686069 3595707162224041882845569)
                    ·
                      refine ⟨2696780371668031412134177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595707162224041882845569 2696780371668031412134177)
                      ·
                        rfl

theorem cell23_5251961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_5251961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251961 prefixEnd_5251961 := by exact prefixLift 5251961
  have htrace : WordTrace (prefixWord ++ tailWord_5251961) baseStart_5251961 baseEnd_5251961 := by
    simpa [prefixWord, tailWord_5251961, baseEnd_5251961] using wordTrace_append hprefix tailTrace_5251961
  have hstable : (prefixWord ++ tailWord_5251961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251961).length < 2 ^ (prefixWord ++ tailWord_5251961).sum := by decide
  have hdescent : baseEnd_5251961 < baseStart_5251961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251968 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 1, 1, 3]
def baseStart_5251968 : Nat := 118140960795 + 5251968 * 2 ^ 59
def prefixEnd_5251968 : Nat := 4983230072969 + 3 ^ 40 * 5251968 * 2
def baseEnd_5251968 : Nat := 2696783966032612884746645

theorem tailTrace_5251968 : CollatzResearch.WordTrace tailWord_5251968 prefixEnd_5251968 2696783966032612884746645 := by
  unfold tailWord_5251968
  simp only [CollatzResearch.WordTrace]
  refine ⟨95777504918512187784250279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127703339891349583712333705 95777504918512187784250279)
  ·
    refine ⟨143666257377768281676375419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95777504918512187784250279 143666257377768281676375419)
    ·
      refine ⟨215499386066652422514563129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143666257377768281676375419 215499386066652422514563129)
      ·
        refine ⟨161624539549989316885922347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215499386066652422514563129 161624539549989316885922347)
        ·
          refine ⟨242436809324983975328883521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161624539549989316885922347 242436809324983975328883521)
          ·
            refine ⟨181827606993737981496662641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242436809324983975328883521 181827606993737981496662641)
            ·
              refine ⟨136370705245303486122496981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181827606993737981496662641 136370705245303486122496981)
              ·
                refine ⟨3196188404186800455996023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 136370705245303486122496981 3196188404186800455996023)
                ·
                  refine ⟨4794282606280200683994035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196188404186800455996023 4794282606280200683994035)
                  ·
                    refine ⟨7191423909420301025991053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794282606280200683994035 7191423909420301025991053)
                    ·
                      refine ⟨2696783966032612884746645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191423909420301025991053 2696783966032612884746645)
                      ·
                        rfl

theorem cell23_5251968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_5251968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251968 prefixEnd_5251968 := by exact prefixLift 5251968
  have htrace : WordTrace (prefixWord ++ tailWord_5251968) baseStart_5251968 baseEnd_5251968 := by
    simpa [prefixWord, tailWord_5251968, baseEnd_5251968] using wordTrace_append hprefix tailTrace_5251968
  have hstable : (prefixWord ++ tailWord_5251968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251968).length < 2 ^ (prefixWord ++ tailWord_5251968).sum := by decide
  have hdescent : baseEnd_5251968 < baseStart_5251968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251978 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5251978 : Nat := 118140960795 + 5251978 * 2 ^ 59
def prefixEnd_5251978 : Nat := 4983230072969 + 3 ^ 40 * 5251978 * 2
def baseEnd_5251978 : Nat := 2696789100839157845621599

theorem tailTrace_5251978 : CollatzResearch.WordTrace tailWord_5251978 prefixEnd_5251978 2696789100839157845621599 := by
  unfold tailWord_5251978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47888843641747036819091147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127703583044658764850909725 47888843641747036819091147)
  ·
    refine ⟨71833265462620555228636721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47888843641747036819091147 71833265462620555228636721)
    ·
      refine ⟨53874949096965416421477541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71833265462620555228636721 53874949096965416421477541)
      ·
        refine ⟨10101552955681015579027039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53874949096965416421477541 10101552955681015579027039)
        ·
          refine ⟨15152329433521523368540559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10101552955681015579027039 15152329433521523368540559)
          ·
            refine ⟨22728494150282285052810839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15152329433521523368540559 22728494150282285052810839)
            ·
              refine ⟨34092741225423427579216259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22728494150282285052810839 34092741225423427579216259)
              ·
                refine ⟨51139111838135141368824389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34092741225423427579216259 51139111838135141368824389)
                ·
                  refine ⟨9588583469650339006654573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51139111838135141368824389 9588583469650339006654573)
                  ·
                    refine ⟨3595718801118877127495465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9588583469650339006654573 3595718801118877127495465)
                    ·
                      refine ⟨2696789100839157845621599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595718801118877127495465 2696789100839157845621599)
                      ·
                        rfl

theorem cell23_5251978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5251978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251978 prefixEnd_5251978 := by exact prefixLift 5251978
  have htrace : WordTrace (prefixWord ++ tailWord_5251978) baseStart_5251978 baseEnd_5251978 := by
    simpa [prefixWord, tailWord_5251978, baseEnd_5251978] using wordTrace_append hprefix tailTrace_5251978
  have hstable : (prefixWord ++ tailWord_5251978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251978).length < 2 ^ (prefixWord ++ tailWord_5251978).sum := by decide
  have hdescent : baseEnd_5251978 < baseStart_5251978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5251984 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 8, 4]
def baseStart_5251984 : Nat := 118140960795 + 5251984 * 2 ^ 59
def prefixEnd_5251984 : Nat := 4983230072969 + 3 ^ 40 * 5251984 * 2
def baseEnd_5251984 : Nat := 898930727241028274048857

theorem tailTrace_5251984 : CollatzResearch.WordTrace tailWord_5251984 prefixEnd_5251984 898930727241028274048857 := by
  unfold tailWord_5251984
  simp only [CollatzResearch.WordTrace]
  refine ⟨95777796702483205150541503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127703728936644273534055337 95777796702483205150541503)
  ·
    refine ⟨143666695053724807725812255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95777796702483205150541503 143666695053724807725812255)
    ·
      refine ⟨215500042580587211588718383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143666695053724807725812255 215500042580587211588718383)
      ·
        refine ⟨323250063870880817383077575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215500042580587211588718383 323250063870880817383077575)
        ·
          refine ⟨484875095806321226074616363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323250063870880817383077575 484875095806321226074616363)
          ·
            refine ⟨727312643709481839111924545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484875095806321226074616363 727312643709481839111924545)
            ·
              refine ⟨545484482782111379333943409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727312643709481839111924545 545484482782111379333943409)
              ·
                refine ⟨409113362086583534500457557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545484482782111379333943409 409113362086583534500457557)
                ·
                  refine ⟨4794297211952150794927237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 409113362086583534500457557 4794297211952150794927237)
                  ·
                    refine ⟨898930727241028274048857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4794297211952150794927237 898930727241028274048857)
                    ·
                      rfl

theorem cell23_5251984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_5251984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5251984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5251984 prefixEnd_5251984 := by exact prefixLift 5251984
  have htrace : WordTrace (prefixWord ++ tailWord_5251984) baseStart_5251984 baseEnd_5251984 := by
    simpa [prefixWord, tailWord_5251984, baseEnd_5251984] using wordTrace_append hprefix tailTrace_5251984
  have hstable : (prefixWord ++ tailWord_5251984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5251984).length < 2 ^ (prefixWord ++ tailWord_5251984).sum := by decide
  have hdescent : baseEnd_5251984 < baseStart_5251984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5251984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252004 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_5252004 : Nat := 118140960795 + 5252004 * 2 ^ 59
def prefixEnd_5252004 : Nat := 4983230072969 + 3 ^ 40 * 5252004 * 2
def baseEnd_5252004 : Nat := 2696802451336174743896479

theorem tailTrace_5252004 : CollatzResearch.WordTrace tailWord_5252004 prefixEnd_5252004 2696802451336174743896479 := by
  unfold tailWord_5252004
  simp only [CollatzResearch.WordTrace]
  refine ⟨95778161432446976858405533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127704215243262635811207377 95778161432446976858405533)
  ·
    refine ⟨35916810537167616321902075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95778161432446976858405533 35916810537167616321902075)
    ·
      refine ⟨53875215805751424482853113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35916810537167616321902075 53875215805751424482853113)
      ·
        refine ⟨40406411854313568362139835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53875215805751424482853113 40406411854313568362139835)
        ·
          refine ⟨60609617781470352543209753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40406411854313568362139835 60609617781470352543209753)
          ·
            refine ⟨45457213336102764407407315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60609617781470352543209753 45457213336102764407407315)
            ·
              refine ⟨68185820004154146611110973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45457213336102764407407315 68185820004154146611110973)
              ·
                refine ⟨25569682501557804979166615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68185820004154146611110973 25569682501557804979166615)
                ·
                  refine ⟨38354523752336707468749923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25569682501557804979166615 38354523752336707468749923)
                  ·
                    refine ⟨57531785628505061203124885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38354523752336707468749923 57531785628505061203124885)
                    ·
                      refine ⟨2696802451336174743896479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57531785628505061203124885 2696802451336174743896479)
                      ·
                        rfl

theorem cell23_5252004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_5252004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252004 prefixEnd_5252004 := by exact prefixLift 5252004
  have htrace : WordTrace (prefixWord ++ tailWord_5252004) baseStart_5252004 baseEnd_5252004 := by
    simpa [prefixWord, tailWord_5252004, baseEnd_5252004] using wordTrace_append hprefix tailTrace_5252004
  have hstable : (prefixWord ++ tailWord_5252004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252004).length < 2 ^ (prefixWord ++ tailWord_5252004).sum := by decide
  have hdescent : baseEnd_5252004 < baseStart_5252004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252021 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5252021 : Nat := 118140960795 + 5252021 * 2 ^ 59
def prefixEnd_5252021 : Nat := 4983230072969 + 3 ^ 40 * 5252021 * 2
def baseEnd_5252021 : Nat := 2696811180507301177383901

theorem tailTrace_5252021 : CollatzResearch.WordTrace tailWord_5252021 prefixEnd_5252021 2696811180507301177383901 := by
  unfold tailWord_5252021
  simp only [CollatzResearch.WordTrace]
  refine ⟨191556942905832365620179917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127704628603888243746786611 191556942905832365620179917)
  ·
    refine ⟨71833853589687137107567469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191556942905832365620179917 71833853589687137107567469)
    ·
      refine ⟨26937695096132676415337801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71833853589687137107567469 26937695096132676415337801)
      ·
        refine ⟨20203271322099507311503351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26937695096132676415337801 20203271322099507311503351)
        ·
          refine ⟨30304906983149260967255027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20203271322099507311503351 30304906983149260967255027)
          ·
            refine ⟨45457360474723891450882541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30304906983149260967255027 45457360474723891450882541)
            ·
              refine ⟨17046510178021459294080953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45457360474723891450882541 17046510178021459294080953)
              ·
                refine ⟨12784882633516094470560715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17046510178021459294080953 12784882633516094470560715)
                ·
                  refine ⟨19177323950274141705841073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12784882633516094470560715 19177323950274141705841073)
                  ·
                    refine ⟨14382992962705606279380805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19177323950274141705841073 14382992962705606279380805)
                    ·
                      refine ⟨2696811180507301177383901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14382992962705606279380805 2696811180507301177383901)
                      ·
                        rfl

theorem cell23_5252021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5252021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252021 prefixEnd_5252021 := by exact prefixLift 5252021
  have htrace : WordTrace (prefixWord ++ tailWord_5252021) baseStart_5252021 baseEnd_5252021 := by
    simpa [prefixWord, tailWord_5252021, baseEnd_5252021] using wordTrace_append hprefix tailTrace_5252021
  have hstable : (prefixWord ++ tailWord_5252021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252021).length < 2 ^ (prefixWord ++ tailWord_5252021).sum := by decide
  have hdescent : baseEnd_5252021 < baseStart_5252021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252036 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5252036 : Nat := 118140960795 + 5252036 * 2 ^ 59
def prefixEnd_5252036 : Nat := 4983230072969 + 3 ^ 40 * 5252036 * 2
def baseEnd_5252036 : Nat := 2696818882717118618696333

theorem tailTrace_5252036 : CollatzResearch.WordTrace tailWord_5252036 prefixEnd_5252036 2696818882717118618696333 := by
  unfold tailWord_5252036
  simp only [CollatzResearch.WordTrace]
  refine ⟨95778745000389011590987981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127704993333852015454650641 95778745000389011590987981)
  ·
    refine ⟨35917029375145879346620493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95778745000389011590987981 35917029375145879346620493)
    ·
      refine ⟨13468886015679704754982685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35917029375145879346620493 13468886015679704754982685)
      ·
        refine ⟨5050832255879889283118507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13468886015679704754982685 5050832255879889283118507)
        ·
          refine ⟨7576248383819833924677761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050832255879889283118507 7576248383819833924677761)
          ·
            refine ⟨5682186287864875443508321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7576248383819833924677761 5682186287864875443508321)
            ·
              refine ⟨4261639715898656582631241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682186287864875443508321 4261639715898656582631241)
              ·
                refine ⟨3196229786923992436973431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261639715898656582631241 3196229786923992436973431)
                ·
                  refine ⟨4794344680385988655460147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196229786923992436973431 4794344680385988655460147)
                  ·
                    refine ⟨7191517020578982983190221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794344680385988655460147 7191517020578982983190221)
                    ·
                      refine ⟨2696818882717118618696333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191517020578982983190221 2696818882717118618696333)
                      ·
                        rfl

theorem cell23_5252036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5252036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252036 prefixEnd_5252036 := by exact prefixLift 5252036
  have htrace : WordTrace (prefixWord ++ tailWord_5252036) baseStart_5252036 baseEnd_5252036 := by
    simpa [prefixWord, tailWord_5252036, baseEnd_5252036] using wordTrace_append hprefix tailTrace_5252036
  have hstable : (prefixWord ++ tailWord_5252036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252036).length < 2 ^ (prefixWord ++ tailWord_5252036).sum := by decide
  have hdescent : baseEnd_5252036 < baseStart_5252036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252044 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_5252044 : Nat := 118140960795 + 5252044 * 2 ^ 59
def prefixEnd_5252044 : Nat := 4983230072969 + 3 ^ 40 * 5252044 * 2
def baseEnd_5252044 : Nat := 898940996854118195798765

theorem tailTrace_5252044 : CollatzResearch.WordTrace tailWord_5252044 prefixEnd_5252044 898940996854118195798765 := by
  unfold tailWord_5252044
  simp only [CollatzResearch.WordTrace]
  refine ⟨95778890892374520274133593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127705187856499360365511457 95778890892374520274133593)
  ·
    refine ⟨71834168169280890205600195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95778890892374520274133593 71834168169280890205600195)
    ·
      refine ⟨107751252253921335308400293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71834168169280890205600195 107751252253921335308400293)
      ·
        refine ⟨20203359797610250370325055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107751252253921335308400293 20203359797610250370325055)
        ·
          refine ⟨30305039696415375555487583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20203359797610250370325055 30305039696415375555487583)
          ·
            refine ⟨45457559544623063333231375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30305039696415375555487583 45457559544623063333231375)
            ·
              refine ⟨68186339316934594999847063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45457559544623063333231375 68186339316934594999847063)
              ·
                refine ⟨102279508975401892499770595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68186339316934594999847063 102279508975401892499770595)
                ·
                  refine ⟨153419263463102838749655893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102279508975401892499770595 153419263463102838749655893)
                  ·
                    refine ⟨898940996854118195798765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 153419263463102838749655893 898940996854118195798765)
                    ·
                      rfl

theorem cell23_5252044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_5252044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252044 prefixEnd_5252044 := by exact prefixLift 5252044
  have htrace : WordTrace (prefixWord ++ tailWord_5252044) baseStart_5252044 baseEnd_5252044 := by
    simpa [prefixWord, tailWord_5252044, baseEnd_5252044] using wordTrace_append hprefix tailTrace_5252044
  have hstable : (prefixWord ++ tailWord_5252044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252044).length < 2 ^ (prefixWord ++ tailWord_5252044).sum := by decide
  have hdescent : baseEnd_5252044 < baseStart_5252044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252058 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_5252058 : Nat := 118140960795 + 5252058 * 2 ^ 59
def prefixEnd_5252058 : Nat := 4983230072969 + 3 ^ 40 * 5252058 * 2
def baseEnd_5252058 : Nat := 2696830179291517532621231

theorem tailTrace_5252058 : CollatzResearch.WordTrace tailWord_5252058 prefixEnd_5252058 2696830179291517532621231 := by
  unfold tailWord_5252058
  simp only [CollatzResearch.WordTrace]
  refine ⟨47889573101674580234819207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127705528271132213959517885 47889573101674580234819207)
  ·
    refine ⟨71834359652511870352228811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47889573101674580234819207 71834359652511870352228811)
    ·
      refine ⟨107751539478767805528343217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71834359652511870352228811 107751539478767805528343217)
      ·
        refine ⟨80813654609075854146257413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107751539478767805528343217 80813654609075854146257413)
        ·
          refine ⟨15152560239201722652423265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80813654609075854146257413 15152560239201722652423265)
          ·
            refine ⟨11364420179401291989317449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15152560239201722652423265 11364420179401291989317449)
            ·
              refine ⟨8523315134550968991988087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11364420179401291989317449 8523315134550968991988087)
              ·
                refine ⟨12784972701826453487982131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8523315134550968991988087 12784972701826453487982131)
                ·
                  refine ⟨19177459052739680231973197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12784972701826453487982131 19177459052739680231973197)
                  ·
                    refine ⟨7191547144777380086989949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19177459052739680231973197 7191547144777380086989949)
                    ·
                      refine ⟨2696830179291517532621231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191547144777380086989949 2696830179291517532621231)
                      ·
                        rfl

theorem cell23_5252058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_5252058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252058 prefixEnd_5252058 := by exact prefixLift 5252058
  have htrace : WordTrace (prefixWord ++ tailWord_5252058) baseStart_5252058 baseEnd_5252058 := by
    simpa [prefixWord, tailWord_5252058, baseEnd_5252058] using wordTrace_append hprefix tailTrace_5252058
  have hstable : (prefixWord ++ tailWord_5252058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252058).length < 2 ^ (prefixWord ++ tailWord_5252058).sum := by decide
  have hdescent : baseEnd_5252058 < baseStart_5252058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252166 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5252166 : Nat := 118140960795 + 5252166 * 2 ^ 59
def prefixEnd_5252166 : Nat := 4983230072969 + 3 ^ 40 * 5252166 * 2
def baseEnd_5252166 : Nat := 2696885635202203110070735

theorem tailTrace_5252166 : CollatzResearch.WordTrace tailWord_5252166 prefixEnd_5252166 2696885635202203110070735 := by
  unfold tailWord_5252166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986319734072095480756511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127708154326871370256138901 5986319734072095480756511)
  ·
    refine ⟨8979479601108143221134767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986319734072095480756511 8979479601108143221134767)
    ·
      refine ⟨13469219401662214831702151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8979479601108143221134767 13469219401662214831702151)
      ·
        refine ⟨20203829102493322247553227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13469219401662214831702151 20203829102493322247553227)
        ·
          refine ⟨30305743653739983371329841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20203829102493322247553227 30305743653739983371329841)
          ·
            refine ⟨22729307740304987528497381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30305743653739983371329841 22729307740304987528497381)
            ·
              refine ⟨4261745201307185161593259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22729307740304987528497381 4261745201307185161593259)
              ·
                refine ⟨6392617801960777742389889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261745201307185161593259 6392617801960777742389889)
                ·
                  refine ⟨4794463351470583306792417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6392617801960777742389889 4794463351470583306792417)
                  ·
                    refine ⟨3595847513602937480094313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4794463351470583306792417 3595847513602937480094313)
                    ·
                      refine ⟨2696885635202203110070735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595847513602937480094313 2696885635202203110070735)
                      ·
                        rfl

theorem cell23_5252166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5252166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252166 prefixEnd_5252166 := by exact prefixLift 5252166
  have htrace : WordTrace (prefixWord ++ tailWord_5252166) baseStart_5252166 baseEnd_5252166 := by
    simpa [prefixWord, tailWord_5252166, baseEnd_5252166] using wordTrace_append hprefix tailTrace_5252166
  have hstable : (prefixWord ++ tailWord_5252166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252166).length < 2 ^ (prefixWord ++ tailWord_5252166).sum := by decide
  have hdescent : baseEnd_5252166 < baseStart_5252166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252208 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_5252208 : Nat := 118140960795 + 5252208 * 2 ^ 59
def prefixEnd_5252208 : Nat := 4983230072969 + 3 ^ 40 * 5252208 * 2
def baseEnd_5252208 : Nat := 2696907201389691945745541

theorem tailTrace_5252208 : CollatzResearch.WordTrace tailWord_5252208 prefixEnd_5252208 2696907201389691945745541 := by
  unfold tailWord_5252208
  simp only [CollatzResearch.WordTrace]
  refine ⟨95781881678077448278618639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127709175570769931038158185 95781881678077448278618639)
  ·
    refine ⟨143672822517116172417927959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95781881678077448278618639 143672822517116172417927959)
    ·
      refine ⟨215509233775674258626891939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143672822517116172417927959 215509233775674258626891939)
      ·
        refine ⟨323263850663511387940337909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215509233775674258626891939 323263850663511387940337909)
        ·
          refine ⟨30305985999704192619406679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 323263850663511387940337909 30305985999704192619406679)
          ·
            refine ⟨45458978999556288929110019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30305985999704192619406679 45458978999556288929110019)
            ·
              refine ⟨68188468499334433393665029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45458978999556288929110019 68188468499334433393665029)
              ·
                refine ⟨12785337843625206261312193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68188468499334433393665029 12785337843625206261312193)
                ·
                  refine ⟨9589003382718904695984145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12785337843625206261312193 9589003382718904695984145)
                  ·
                    refine ⟨7191752537039178521988109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9589003382718904695984145 7191752537039178521988109)
                    ·
                      refine ⟨2696907201389691945745541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191752537039178521988109 2696907201389691945745541)
                      ·
                        rfl

theorem cell23_5252208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_5252208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252208 prefixEnd_5252208 := by exact prefixLift 5252208
  have htrace : WordTrace (prefixWord ++ tailWord_5252208) baseStart_5252208 baseEnd_5252208 := by
    simpa [prefixWord, tailWord_5252208, baseEnd_5252208] using wordTrace_append hprefix tailTrace_5252208
  have hstable : (prefixWord ++ tailWord_5252208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252208).length < 2 ^ (prefixWord ++ tailWord_5252208).sum := by decide
  have hdescent : baseEnd_5252208 < baseStart_5252208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252215 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 1, 4]
def baseStart_5252215 : Nat := 118140960795 + 5252215 * 2 ^ 59
def prefixEnd_5252215 : Nat := 4983230072969 + 3 ^ 40 * 5252215 * 2
def baseEnd_5252215 : Nat := 898970265251424472786003

theorem tailTrace_5252215 : CollatzResearch.WordTrace tailWord_5252215 prefixEnd_5252215 898970265251424472786003 := by
  unfold tailWord_5252215
  simp only [CollatzResearch.WordTrace]
  refine ⟨191564018667129536752742099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127709345778086357835161399 191564018667129536752742099)
  ·
    refine ⟨287346028000694305129113149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191564018667129536752742099 287346028000694305129113149)
    ·
      refine ⟨107754760500260364423417431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287346028000694305129113149 107754760500260364423417431)
      ·
        refine ⟨161632140750390546635126147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107754760500260364423417431 161632140750390546635126147)
        ·
          refine ⟨242448211125585819952689221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161632140750390546635126147 242448211125585819952689221)
          ·
            refine ⟨45459039586047341241129229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242448211125585819952689221 45459039586047341241129229)
            ·
              refine ⟨17047139844767752965423461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45459039586047341241129229 17047139844767752965423461)
              ·
                refine ⟨3196338720893953681016899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17047139844767752965423461 3196338720893953681016899)
                ·
                  refine ⟨4794508081340930521525349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196338720893953681016899 4794508081340930521525349)
                  ·
                    refine ⟨898970265251424472786003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4794508081340930521525349 898970265251424472786003)
                    ·
                      rfl

theorem cell23_5252215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_5252215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252215 prefixEnd_5252215 := by exact prefixLift 5252215
  have htrace : WordTrace (prefixWord ++ tailWord_5252215) baseStart_5252215 baseEnd_5252215 := by
    simpa [prefixWord, tailWord_5252215, baseEnd_5252215] using wordTrace_append hprefix tailTrace_5252215
  have hstable : (prefixWord ++ tailWord_5252215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252215).length < 2 ^ (prefixWord ++ tailWord_5252215).sum := by decide
  have hdescent : baseEnd_5252215 < baseStart_5252215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252228 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 6]
def baseStart_5252228 : Nat := 118140960795 + 5252228 * 2 ^ 59
def prefixEnd_5252228 : Nat := 4983230072969 + 3 ^ 40 * 5252228 * 2
def baseEnd_5252228 : Nat := 299657496778086874166161

theorem tailTrace_5252228 : CollatzResearch.WordTrace tailWord_5252228 prefixEnd_5252228 299657496778086874166161 := by
  unfold tailWord_5252228
  simp only [CollatzResearch.WordTrace]
  refine ⟨95782246408041219986482669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127709661877388293315310225 95782246408041219986482669)
  ·
    refine ⟨35918342403015457494931001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95782246408041219986482669 35918342403015457494931001)
    ·
      refine ⟨26938756802261593121198251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35918342403015457494931001 26938756802261593121198251)
      ·
        refine ⟨40408135203392389681797377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26938756802261593121198251 40408135203392389681797377)
        ·
          refine ⟨30306101402544292261348033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40408135203392389681797377 30306101402544292261348033)
          ·
            refine ⟨22729576051908219196011025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30306101402544292261348033 22729576051908219196011025)
            ·
              refine ⟨17047182038931164397008269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22729576051908219196011025 17047182038931164397008269)
              ·
                refine ⟨6392693264599186648878101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17047182038931164397008269 6392693264599186648878101)
                ·
                  refine ⟨299657496778086874166161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6392693264599186648878101 299657496778086874166161)
                  ·
                    rfl

theorem cell23_5252228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_5252228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252228 prefixEnd_5252228 := by exact prefixLift 5252228
  have htrace : WordTrace (prefixWord ++ tailWord_5252228) baseStart_5252228 baseEnd_5252228 := by
    simpa [prefixWord, tailWord_5252228, baseEnd_5252228] using wordTrace_append hprefix tailTrace_5252228
  have hstable : (prefixWord ++ tailWord_5252228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252228).length < 2 ^ (prefixWord ++ tailWord_5252228).sum := by decide
  have hdescent : baseEnd_5252228 < baseStart_5252228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252242 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_5252242 : Nat := 118140960795 + 5252242 * 2 ^ 59
def prefixEnd_5252242 : Nat := 4983230072969 + 3 ^ 40 * 5252242 * 2
def baseEnd_5252242 : Nat := 2696924659731944812720385

theorem tailTrace_5252242 : CollatzResearch.WordTrace tailWord_5252242 prefixEnd_5252242 2696924659731944812720385 := by
  unfold tailWord_5252242
  simp only [CollatzResearch.WordTrace]
  refine ⟨47891250859507930090993745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127710002292021146909316653 47891250859507930090993745)
  ·
    refine ⟨35918438144630947568245309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47891250859507930090993745 35918438144630947568245309)
    ·
      refine ⟨13469414304236605338091991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35918438144630947568245309 13469414304236605338091991)
      ·
        refine ⟨20204121456354908007137987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13469414304236605338091991 20204121456354908007137987)
        ·
          refine ⟨30306182184532362010706981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20204121456354908007137987 30306182184532362010706981)
          ·
            refine ⟨5682409159599817877007559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30306182184532362010706981 5682409159599817877007559)
            ·
              refine ⟨8523613739399726815511339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682409159599817877007559 8523613739399726815511339)
              ·
                refine ⟨12785420609099590223267009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8523613739399726815511339 12785420609099590223267009)
                ·
                  refine ⟨9589065456824692667450257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12785420609099590223267009 9589065456824692667450257)
                  ·
                    refine ⟨7191799092618519500587693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9589065456824692667450257 7191799092618519500587693)
                    ·
                      refine ⟨2696924659731944812720385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7191799092618519500587693 2696924659731944812720385)
                      ·
                        rfl

theorem cell23_5252242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_5252242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252242 prefixEnd_5252242 := by exact prefixLift 5252242
  have htrace : WordTrace (prefixWord ++ tailWord_5252242) baseStart_5252242 baseEnd_5252242 := by
    simpa [prefixWord, tailWord_5252242, baseEnd_5252242] using wordTrace_append hprefix tailTrace_5252242
  have hstable : (prefixWord ++ tailWord_5252242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252242).length < 2 ^ (prefixWord ++ tailWord_5252242).sum := by decide
  have hdescent : baseEnd_5252242 < baseStart_5252242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252271 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 3, 6]
def baseStart_5252271 : Nat := 118140960795 + 5252271 * 2 ^ 59
def prefixEnd_5252271 : Nat := 4983230072969 + 3 ^ 40 * 5252271 * 2
def baseEnd_5252271 : Nat := 898979850223641733085917

theorem tailTrace_5252271 : CollatzResearch.WordTrace tailWord_5252271 prefixEnd_5252271 898979850223641733085917 := by
  unfold tailWord_5252271
  simp only [CollatzResearch.WordTrace]
  refine ⟨191566061154926658316780667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127710707436617772211187111 191566061154926658316780667)
  ·
    refine ⟨287349091732389987475171001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191566061154926658316780667 287349091732389987475171001)
    ·
      refine ⟨215511818799292490606378251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287349091732389987475171001 215511818799292490606378251)
      ·
        refine ⟨323267728198938735909567377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215511818799292490606378251 323267728198938735909567377)
        ·
          refine ⟨242450796149204051932175533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323267728198938735909567377 242450796149204051932175533)
          ·
            refine ⟨90919048555951519474565825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242450796149204051932175533 90919048555951519474565825)
            ·
              refine ⟨68189286416963639605924369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90919048555951519474565825 68189286416963639605924369)
              ·
                refine ⟨51141964812722729704443277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68189286416963639605924369 51141964812722729704443277)
                ·
                  refine ⟨19178236804771023639166229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51141964812722729704443277 19178236804771023639166229)
                  ·
                    refine ⟨898979850223641733085917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19178236804771023639166229 898979850223641733085917)
                    ·
                      rfl

theorem cell23_5252271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_5252271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252271 prefixEnd_5252271 := by exact prefixLift 5252271
  have htrace : WordTrace (prefixWord ++ tailWord_5252271) baseStart_5252271 baseEnd_5252271 := by
    simpa [prefixWord, tailWord_5252271, baseEnd_5252271] using wordTrace_append hprefix tailTrace_5252271
  have hstable : (prefixWord ++ tailWord_5252271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252271).length < 2 ^ (prefixWord ++ tailWord_5252271).sum := by decide
  have hdescent : baseEnd_5252271 < baseStart_5252271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252292 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_5252292 : Nat := 118140960795 + 5252292 * 2 ^ 59
def prefixEnd_5252292 : Nat := 4983230072969 + 3 ^ 40 * 5252292 * 2
def baseEnd_5252292 : Nat := 898983444588223205698385

theorem tailTrace_5252292 : CollatzResearch.WordTrace tailWord_5252292 prefixEnd_5252292 898983444588223205698385 := by
  unfold tailWord_5252292
  simp only [CollatzResearch.WordTrace]
  refine ⟨95783413543925289451647565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127711218058567052602196753 95783413543925289451647565)
  ·
    refine ⟨35918780078971983544367837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95783413543925289451647565 35918780078971983544367837)
    ·
      refine ⟨13469542529614493829137939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35918780078971983544367837 13469542529614493829137939)
      ·
        refine ⟨20204313794421740743706909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13469542529614493829137939 20204313794421740743706909)
        ·
          refine ⟨7576617672908152778890091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20204313794421740743706909 7576617672908152778890091)
          ·
            refine ⟨11364926509362229168335137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7576617672908152778890091 11364926509362229168335137)
            ·
              refine ⟨8523694882021671876251353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11364926509362229168335137 8523694882021671876251353)
              ·
                refine ⟨6392771161516253907188515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8523694882021671876251353 6392771161516253907188515)
                ·
                  refine ⟨9589156742274380860782773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6392771161516253907188515 9589156742274380860782773)
                  ·
                    refine ⟨898983444588223205698385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9589156742274380860782773 898983444588223205698385)
                    ·
                      rfl

theorem cell23_5252292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_5252292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252292 prefixEnd_5252292 := by exact prefixLift 5252292
  have htrace : WordTrace (prefixWord ++ tailWord_5252292) baseStart_5252292 baseEnd_5252292 := by
    simpa [prefixWord, tailWord_5252292, baseEnd_5252292] using wordTrace_append hprefix tailTrace_5252292
  have hstable : (prefixWord ++ tailWord_5252292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252292).length < 2 ^ (prefixWord ++ tailWord_5252292).sum := by decide
  have hdescent : baseEnd_5252292 < baseStart_5252292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252385 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_5252385 : Nat := 118140960795 + 5252385 * 2 ^ 59
def prefixEnd_5252385 : Nat := 4983230072969 + 3 ^ 40 * 5252385 * 2
def baseEnd_5252385 : Nat := 2696998087465537753232227

theorem tailTrace_5252385 : CollatzResearch.WordTrace tailWord_5252385 prefixEnd_5252385 2696998087465537753232227 := by
  unfold tailWord_5252385
  simp only [CollatzResearch.WordTrace]
  refine ⟨191570219076513655786430609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127713479384342437190953739 191570219076513655786430609)
  ·
    refine ⟨143677664307385241839822957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191570219076513655786430609 143677664307385241839822957)
    ·
      refine ⟨53879124115269465689933609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143677664307385241839822957 53879124115269465689933609)
      ·
        refine ⟨40409343086452099267450207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53879124115269465689933609 40409343086452099267450207)
        ·
          refine ⟨60614014629678148901175311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40409343086452099267450207 60614014629678148901175311)
          ·
            refine ⟨90921021944517223351762967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60614014629678148901175311 90921021944517223351762967)
            ·
              refine ⟨136381532916775835027644451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90921021944517223351762967 136381532916775835027644451)
              ·
                refine ⟨204572299375163752541466677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136381532916775835027644451 204572299375163752541466677)
                ·
                  refine ⟨19178653066421601800762501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204572299375163752541466677 19178653066421601800762501)
                  ·
                    refine ⟨3595997449954050337642969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19178653066421601800762501 3595997449954050337642969)
                    ·
                      refine ⟨2696998087465537753232227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3595997449954050337642969 2696998087465537753232227)
                      ·
                        rfl

theorem cell23_5252385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_5252385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252385 prefixEnd_5252385 := by exact prefixLift 5252385
  have htrace : WordTrace (prefixWord ++ tailWord_5252385) baseStart_5252385 baseEnd_5252385 := by
    simpa [prefixWord, tailWord_5252385, baseEnd_5252385] using wordTrace_append hprefix tailTrace_5252385
  have hstable : (prefixWord ++ tailWord_5252385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252385).length < 2 ^ (prefixWord ++ tailWord_5252385).sum := by decide
  have hdescent : baseEnd_5252385 < baseStart_5252385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252402 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_5252402 : Nat := 118140960795 + 5252402 * 2 ^ 59
def prefixEnd_5252402 : Nat := 4983230072969 + 3 ^ 40 * 5252402 * 2
def baseEnd_5252402 : Nat := 2697006816636664186719649

theorem tailTrace_5252402 : CollatzResearch.WordTrace tailWord_5252402 prefixEnd_5252402 2697006816636664186719649 := by
  unfold tailWord_5252402
  simp only [CollatzResearch.WordTrace]
  refine ⟨47892709779363016922449865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127713892744968045126532973 47892709779363016922449865)
  ·
    refine ⟨35919532334522262691837399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47892709779363016922449865 35919532334522262691837399)
    ·
      refine ⟨53879298501783394037756099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35919532334522262691837399 53879298501783394037756099)
      ·
        refine ⟨80818947752675091056634149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53879298501783394037756099 80818947752675091056634149)
        ·
          refine ⟨15153552703626579573118903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80818947752675091056634149 15153552703626579573118903)
          ·
            refine ⟨22730329055439869359678355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15153552703626579573118903 22730329055439869359678355)
            ·
              refine ⟨34095493583159804039517533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22730329055439869359678355 34095493583159804039517533)
              ·
                refine ⟨12785810093684926514819075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34095493583159804039517533 12785810093684926514819075)
                ·
                  refine ⟨19178715140527389772228613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12785810093684926514819075 19178715140527389772228613)
                  ·
                    refine ⟨3596009088848885582292865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19178715140527389772228613 3596009088848885582292865)
                    ·
                      refine ⟨2697006816636664186719649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596009088848885582292865 2697006816636664186719649)
                      ·
                        rfl

theorem cell23_5252402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_5252402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252402 prefixEnd_5252402 := by exact prefixLift 5252402
  have htrace : WordTrace (prefixWord ++ tailWord_5252402) baseStart_5252402 baseEnd_5252402 := by
    simpa [prefixWord, tailWord_5252402, baseEnd_5252402] using wordTrace_append hprefix tailTrace_5252402
  have hstable : (prefixWord ++ tailWord_5252402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252402).length < 2 ^ (prefixWord ++ tailWord_5252402).sum := by decide
  have hdescent : baseEnd_5252402 < baseStart_5252402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252425 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 5]
def baseStart_5252425 : Nat := 118140960795 + 5252425 * 2 ^ 59
def prefixEnd_5252425 : Nat := 4983230072969 + 3 ^ 40 * 5252425 * 2
def baseEnd_5252425 : Nat := 299668736299079732970227

theorem tailTrace_5252425 : CollatzResearch.WordTrace tailWord_5252425 prefixEnd_5252425 299668736299079732970227 := by
  unfold tailWord_5252425
  simp only [CollatzResearch.WordTrace]
  refine ⟨191571677996368742617886729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127714451997579161745257819 191571677996368742617886729)
  ·
    refine ⟨143678758497276556963415047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191571677996368742617886729 143678758497276556963415047)
    ·
      refine ⟨215518137745914835445122571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143678758497276556963415047 215518137745914835445122571)
      ·
        refine ⟨323277206618872253167683857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215518137745914835445122571 323277206618872253167683857)
        ·
          refine ⟨242457904964154189875762893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323277206618872253167683857 242457904964154189875762893)
          ·
            refine ⟨90921714361557821203411085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242457904964154189875762893 90921714361557821203411085)
            ·
              refine ⟨34095642885584182951279157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90921714361557821203411085 34095642885584182951279157)
              ·
                refine ⟨3196466520523517151682421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34095642885584182951279157 3196466520523517151682421)
                ·
                  refine ⟨299668736299079732970227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3196466520523517151682421 299668736299079732970227)
                  ·
                    rfl

theorem cell23_5252425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 5].length) (baseStart_5252425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252425 prefixEnd_5252425 := by exact prefixLift 5252425
  have htrace : WordTrace (prefixWord ++ tailWord_5252425) baseStart_5252425 baseEnd_5252425 := by
    simpa [prefixWord, tailWord_5252425, baseEnd_5252425] using wordTrace_append hprefix tailTrace_5252425
  have hstable : (prefixWord ++ tailWord_5252425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252425).length < 2 ^ (prefixWord ++ tailWord_5252425).sum := by decide
  have hdescent : baseEnd_5252425 < baseStart_5252425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252475 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 4]
def baseStart_5252475 : Nat := 118140960795 + 5252475 * 2 ^ 59
def prefixEnd_5252475 : Nat := 4983230072969 + 3 ^ 40 * 5252475 * 2
def baseEnd_5252475 : Nat := 2697044300724442401106813

theorem tailTrace_5252475 : CollatzResearch.WordTrace tailWord_5252475 prefixEnd_5252475 2697044300724442401106813 := by
  unfold tailWord_5252475
  simp only [CollatzResearch.WordTrace]
  refine ⟨191573501646187601157206879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127715667764125067438137919 191573501646187601157206879)
  ·
    refine ⟨287360252469281401735810319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191573501646187601157206879 287360252469281401735810319)
    ·
      refine ⟨431040378703922102603715479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287360252469281401735810319 431040378703922102603715479)
      ·
        refine ⟨646560568055883153905573219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431040378703922102603715479 646560568055883153905573219)
        ·
          refine ⟨969840852083824730858359829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646560568055883153905573219 969840852083824730858359829)
          ·
            refine ⟨45461289941429284258985617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 969840852083824730858359829 45461289941429284258985617)
            ·
              refine ⟨34095967456071963194239213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45461289941429284258985617 34095967456071963194239213)
              ·
                refine ⟨12785987796026986197839705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34095967456071963194239213 12785987796026986197839705)
                ·
                  refine ⟨9589490847020239648379779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12785987796026986197839705 9589490847020239648379779)
                  ·
                    refine ⟨14384236270530359472569669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9589490847020239648379779 14384236270530359472569669)
                    ·
                      refine ⟨2697044300724442401106813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14384236270530359472569669 2697044300724442401106813)
                      ·
                        rfl

theorem cell23_5252475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 4].length) (baseStart_5252475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252475 prefixEnd_5252475 := by exact prefixLift 5252475
  have htrace : WordTrace (prefixWord ++ tailWord_5252475) baseStart_5252475 baseEnd_5252475 := by
    simpa [prefixWord, tailWord_5252475, baseEnd_5252475] using wordTrace_append hprefix tailTrace_5252475
  have hstable : (prefixWord ++ tailWord_5252475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252475).length < 2 ^ (prefixWord ++ tailWord_5252475).sum := by decide
  have hdescent : baseEnd_5252475 < baseStart_5252475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252485 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_5252485 : Nat := 118140960795 + 5252485 * 2 ^ 59
def prefixEnd_5252485 : Nat := 4983230072969 + 3 ^ 40 * 5252485 * 2
def baseEnd_5252485 : Nat := 899016478510329120660589

theorem tailTrace_5252485 : CollatzResearch.WordTrace tailWord_5252485 prefixEnd_5252485 899016478510329120660589 := by
  unfold tailWord_5252485
  simp only [CollatzResearch.WordTrace]
  refine ⟨191573866376151372865070909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127715910917434248576713939 191573866376151372865070909)
  ·
    refine ⟨71840199891056764824401591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191573866376151372865070909 71840199891056764824401591)
    ·
      refine ⟨107760299836585147236602387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71840199891056764824401591 107760299836585147236602387)
      ·
        refine ⟨161640449754877720854903581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107760299836585147236602387 161640449754877720854903581)
        ·
          refine ⟨60615168658079145320588843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161640449754877720854903581 60615168658079145320588843)
          ·
            refine ⟨90922752987118717980883265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60615168658079145320588843 90922752987118717980883265)
            ·
              refine ⟨68192064740339038485662449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90922752987118717980883265 68192064740339038485662449)
              ·
                refine ⟨51144048555254278864246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68192064740339038485662449 51144048555254278864246837)
                ·
                  refine ⟨4794754552055088643523141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51144048555254278864246837 4794754552055088643523141)
                  ·
                    refine ⟨899016478510329120660589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4794754552055088643523141 899016478510329120660589)
                    ·
                      rfl

theorem cell23_5252485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_5252485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252485 prefixEnd_5252485 := by exact prefixLift 5252485
  have htrace : WordTrace (prefixWord ++ tailWord_5252485) baseStart_5252485 baseEnd_5252485 := by
    simpa [prefixWord, tailWord_5252485, baseEnd_5252485] using wordTrace_append hprefix tailTrace_5252485
  have hstable : (prefixWord ++ tailWord_5252485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252485).length < 2 ^ (prefixWord ++ tailWord_5252485).sum := by decide
  have hdescent : baseEnd_5252485 < baseStart_5252485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252515 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 6]
def baseStart_5252515 : Nat := 118140960795 + 5252515 * 2 ^ 59
def prefixEnd_5252515 : Nat := 4983230072969 + 3 ^ 40 * 5252515 * 2
def baseEnd_5252515 : Nat := 299673871105624693845181

theorem tailTrace_5252515 : CollatzResearch.WordTrace tailWord_5252515 prefixEnd_5252515 299673871105624693845181 := by
  unfold tailWord_5252515
  simp only [CollatzResearch.WordTrace]
  refine ⟨191574960566042687988662999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127716640377361791992441999 191574960566042687988662999)
  ·
    refine ⟨287362440849064031982994499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191574960566042687988662999 287362440849064031982994499)
    ·
      refine ⟨431043661273596047974491749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287362440849064031982994499 431043661273596047974491749)
      ·
        refine ⟨80820686488799258995217203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 431043661273596047974491749 80820686488799258995217203)
        ·
          refine ⟨121231029733198888492825805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80820686488799258995217203 121231029733198888492825805)
          ·
            refine ⟨45461636149949583184809677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121231029733198888492825805 45461636149949583184809677)
            ·
              refine ⟨17048113556231093694303629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45461636149949583184809677 17048113556231093694303629)
              ·
                refine ⟨6393042583586660135363861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17048113556231093694303629 6393042583586660135363861)
                ·
                  refine ⟨299673871105624693845181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6393042583586660135363861 299673871105624693845181)
                  ·
                    rfl

theorem cell23_5252515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 6].length) (baseStart_5252515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252515 prefixEnd_5252515 := by exact prefixLift 5252515
  have htrace : WordTrace (prefixWord ++ tailWord_5252515) baseStart_5252515 baseEnd_5252515 := by
    simpa [prefixWord, tailWord_5252515, baseEnd_5252515] using wordTrace_append hprefix tailTrace_5252515
  have hstable : (prefixWord ++ tailWord_5252515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252515).length < 2 ^ (prefixWord ++ tailWord_5252515).sum := by decide
  have hdescent : baseEnd_5252515 < baseStart_5252515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252595 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4]
def baseStart_5252595 : Nat := 118140960795 + 5252595 * 2 ^ 59
def prefixEnd_5252595 : Nat := 4983230072969 + 3 ^ 40 * 5252595 * 2
def baseEnd_5252595 : Nat := 2697105918402981931606261

theorem tailTrace_5252595 : CollatzResearch.WordTrace tailWord_5252595 prefixEnd_5252595 2697105918402981931606261 := by
  unfold tailWord_5252595
  simp only [CollatzResearch.WordTrace]
  refine ⟨191577878405752861651575239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127718585603835241101050159 191577878405752861651575239)
  ·
    refine ⟨287366817608629292477362859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191577878405752861651575239 287366817608629292477362859)
    ·
      refine ⟨431050226412943938716044289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287366817608629292477362859 431050226412943938716044289)
      ·
        refine ⟨323287669809707954037033217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431050226412943938716044289 323287669809707954037033217)
        ·
          refine ⟨242465752357280965527774913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323287669809707954037033217 242465752357280965527774913)
          ·
            refine ⟨181849314267960724145831185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242465752357280965527774913 181849314267960724145831185)
            ·
              refine ⟨136386985700970543109373389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181849314267960724145831185 136386985700970543109373389)
              ·
                refine ⟨51145119637863953666015021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136386985700970543109373389 51145119637863953666015021)
                ·
                  refine ⟨19179419864198982624755633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51145119637863953666015021 19179419864198982624755633)
                  ·
                    refine ⟨14384564898149236968566725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19179419864198982624755633 14384564898149236968566725)
                    ·
                      refine ⟨2697105918402981931606261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14384564898149236968566725 2697105918402981931606261)
                      ·
                        rfl

theorem cell23_5252595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_5252595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252595 prefixEnd_5252595 := by exact prefixLift 5252595
  have htrace : WordTrace (prefixWord ++ tailWord_5252595) baseStart_5252595 baseEnd_5252595 := by
    simpa [prefixWord, tailWord_5252595, baseEnd_5252595] using wordTrace_append hprefix tailTrace_5252595
  have hstable : (prefixWord ++ tailWord_5252595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252595).length < 2 ^ (prefixWord ++ tailWord_5252595).sum := by decide
  have hdescent : baseEnd_5252595 < baseStart_5252595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252605 : List Nat := [1, 4, 1, 1, 1, 5, 10]
def baseStart_5252605 : Nat := 118140960795 + 5252605 * 2 ^ 59
def prefixEnd_5252605 : Nat := 4983230072969 + 3 ^ 40 * 5252605 * 2
def baseEnd_5252605 : Nat := 33297667323574406080015

theorem tailTrace_5252605 : CollatzResearch.WordTrace tailWord_5252605 prefixEnd_5252605 33297667323574406080015 := by
  unfold tailWord_5252605
  simp only [CollatzResearch.WordTrace]
  refine ⟨191578243135716633359439269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127718828757144422239626179 191578243135716633359439269)
  ·
    refine ⟨35920920587946868754894863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191578243135716633359439269 35920920587946868754894863)
    ·
      refine ⟨53881380881920303132342295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35920920587946868754894863 53881380881920303132342295)
      ·
        refine ⟨80822071322880454698513443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53881380881920303132342295 80822071322880454698513443)
        ·
          refine ⟨121233106984320682047770165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80822071322880454698513443 121233106984320682047770165)
          ·
            refine ⟨11365603779780063941978453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121233106984320682047770165 11365603779780063941978453)
            ·
              refine ⟨33297667323574406080015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11365603779780063941978453 33297667323574406080015)
              ·
                rfl

theorem cell23_5252605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 10].length) (baseStart_5252605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252605 prefixEnd_5252605 := by exact prefixLift 5252605
  have htrace : WordTrace (prefixWord ++ tailWord_5252605) baseStart_5252605 baseEnd_5252605 := by
    simpa [prefixWord, tailWord_5252605, baseEnd_5252605] using wordTrace_append hprefix tailTrace_5252605
  have hstable : (prefixWord ++ tailWord_5252605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252605).length < 2 ^ (prefixWord ++ tailWord_5252605).sum := by decide
  have hdescent : baseEnd_5252605 < baseStart_5252605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252609 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 4, 4]
def baseStart_5252609 : Nat := 118140960795 + 5252609 * 2 ^ 59
def prefixEnd_5252609 : Nat := 4983230072969 + 3 ^ 40 * 5252609 * 2
def baseEnd_5252609 : Nat := 899037702377381625610399

theorem tailTrace_5252609 : CollatzResearch.WordTrace tailWord_5252609 prefixEnd_5252609 899037702377381625610399 := by
  unfold tailWord_5252609
  simp only [CollatzResearch.WordTrace]
  refine ⟨191578389027702142042584881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127718926018468094695056587 191578389027702142042584881)
  ·
    refine ⟨143683791770776606531938661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191578389027702142042584881 143683791770776606531938661)
    ·
      refine ⟨26940710957020613724738499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143683791770776606531938661 26940710957020613724738499)
      ·
        refine ⟨40411066435530920587107749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26940710957020613724738499 40411066435530920587107749)
        ·
          refine ⟨7577074956662047610082703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40411066435530920587107749 7577074956662047610082703)
          ·
            refine ⟨11365612434993071415124055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7577074956662047610082703 11365612434993071415124055)
            ·
              refine ⟨17048418652489607122686083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11365612434993071415124055 17048418652489607122686083)
              ·
                refine ⟨25572627978734410684029125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17048418652489607122686083 25572627978734410684029125)
                ·
                  refine ⟨4794867746012702003255461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25572627978734410684029125 4794867746012702003255461)
                  ·
                    refine ⟨899037702377381625610399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4794867746012702003255461 899037702377381625610399)
                    ·
                      rfl

theorem cell23_5252609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_5252609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252609 prefixEnd_5252609 := by exact prefixLift 5252609
  have htrace : WordTrace (prefixWord ++ tailWord_5252609) baseStart_5252609 baseEnd_5252609 := by
    simpa [prefixWord, tailWord_5252609, baseEnd_5252609] using wordTrace_append hprefix tailTrace_5252609
  have hstable : (prefixWord ++ tailWord_5252609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252609).length < 2 ^ (prefixWord ++ tailWord_5252609).sum := by decide
  have hdescent : baseEnd_5252609 < baseStart_5252609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252629 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_5252629 : Nat := 118140960795 + 5252629 * 2 ^ 59
def prefixEnd_5252629 : Nat := 4983230072969 + 3 ^ 40 * 5252629 * 2
def baseEnd_5252629 : Nat := 2697123376745234798581105

theorem tailTrace_5252629 : CollatzResearch.WordTrace tailWord_5252629 prefixEnd_5252629 2697123376745234798581105 := by
  unfold tailWord_5252629
  simp only [CollatzResearch.WordTrace]
  refine ⟨191579118487629685458312941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127719412325086456972208627 191579118487629685458312941)
  ·
    refine ⟨71842169432861132046867353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191579118487629685458312941 71842169432861132046867353)
    ·
      refine ⟨53881627074645849035150515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71842169432861132046867353 53881627074645849035150515)
      ·
        refine ⟨80822440611968773552725773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53881627074645849035150515 80822440611968773552725773)
        ·
          refine ⟨30308415229488290082272165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80822440611968773552725773 30308415229488290082272165)
          ·
            refine ⟨5682827855529054390426031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30308415229488290082272165 5682827855529054390426031)
            ·
              refine ⟨8524241783293581585639047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682827855529054390426031 8524241783293581585639047)
              ·
                refine ⟨12786362674940372378458571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8524241783293581585639047 12786362674940372378458571)
                ·
                  refine ⟨19179544012410558567687857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12786362674940372378458571 19179544012410558567687857)
                  ·
                    refine ⟨14384658009307918925765893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19179544012410558567687857 14384658009307918925765893)
                    ·
                      refine ⟨2697123376745234798581105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14384658009307918925765893 2697123376745234798581105)
                      ·
                        rfl

theorem cell23_5252629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_5252629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252629 prefixEnd_5252629 := by exact prefixLift 5252629
  have htrace : WordTrace (prefixWord ++ tailWord_5252629) baseStart_5252629 baseEnd_5252629 := by
    simpa [prefixWord, tailWord_5252629, baseEnd_5252629] using wordTrace_append hprefix tailTrace_5252629
  have hstable : (prefixWord ++ tailWord_5252629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252629).length < 2 ^ (prefixWord ++ tailWord_5252629).sum := by decide
  have hdescent : baseEnd_5252629 < baseStart_5252629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252689 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 1, 4, 2]
def baseStart_5252689 : Nat := 118140960795 + 5252689 * 2 ^ 59
def prefixEnd_5252689 : Nat := 4983230072969 + 3 ^ 40 * 5252689 * 2
def baseEnd_5252689 : Nat := 2697154185584504563830829

theorem tailTrace_5252689 : CollatzResearch.WordTrace tailWord_5252689 prefixEnd_5252689 2697154185584504563830829 := by
  unfold tailWord_5252689
  simp only [CollatzResearch.WordTrace]
  refine ⟨191581306867412315705497121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127720871244941543803664747 191581306867412315705497121)
  ·
    refine ⟨143685980150559236779122841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191581306867412315705497121 143685980150559236779122841)
    ·
      refine ⟨107764485112919427584342131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143685980150559236779122841 107764485112919427584342131)
      ·
        refine ⟨161646727669379141376513197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107764485112919427584342131 161646727669379141376513197)
        ·
          refine ⟨60617522876017178016192449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161646727669379141376513197 60617522876017178016192449)
          ·
            refine ⟨45463142157012883512144337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60617522876017178016192449 45463142157012883512144337)
            ·
              refine ⟨34097356617759662634108253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45463142157012883512144337 34097356617759662634108253)
              ·
                refine ⟨12786508731659873487790595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34097356617759662634108253 12786508731659873487790595)
                ·
                  refine ⟨19179763097489810231685893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12786508731659873487790595 19179763097489810231685893)
                  ·
                    refine ⟨3596205580779339418441105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19179763097489810231685893 3596205580779339418441105)
                    ·
                      refine ⟨2697154185584504563830829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596205580779339418441105 2697154185584504563830829)
                      ·
                        rfl

theorem cell23_5252689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_5252689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252689 prefixEnd_5252689 := by exact prefixLift 5252689
  have htrace : WordTrace (prefixWord ++ tailWord_5252689) baseStart_5252689 baseEnd_5252689 := by
    simpa [prefixWord, tailWord_5252689, baseEnd_5252689] using wordTrace_append hprefix tailTrace_5252689
  have hstable : (prefixWord ++ tailWord_5252689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252689).length < 2 ^ (prefixWord ++ tailWord_5252689).sum := by decide
  have hdescent : baseEnd_5252689 < baseStart_5252689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252692 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5252692 : Nat := 118140960795 + 5252692 * 2 ^ 59
def prefixEnd_5252692 : Nat := 4983230072969 + 3 ^ 40 * 5252692 * 2
def baseEnd_5252692 : Nat := 2697155726026468052093315

theorem tailTrace_5252692 : CollatzResearch.WordTrace tailWord_5252692 prefixEnd_5252692 2697155726026468052093315 := by
  unfold tailWord_5252692
  simp only [CollatzResearch.WordTrace]
  refine ⟨95790708143200723608928165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127720944190934298145237553 95790708143200723608928165)
  ·
    refine ⟨17960757776850135676674031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95790708143200723608928165 17960757776850135676674031)
    ·
      refine ⟨26941136665275203515011047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17960757776850135676674031 26941136665275203515011047)
      ·
        refine ⟨40411704997912805272516571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26941136665275203515011047 40411704997912805272516571)
        ·
          refine ⟨60617557496869207908774857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40411704997912805272516571 60617557496869207908774857)
          ·
            refine ⟨45463168122651905931581143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60617557496869207908774857 45463168122651905931581143)
            ·
              refine ⟨68194752183977858897371715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45463168122651905931581143 68194752183977858897371715)
              ·
                refine ⟨102292128275966788346057573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68194752183977858897371715 102292128275966788346057573)
                ·
                  refine ⟨19179774051743772814885795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102292128275966788346057573 19179774051743772814885795)
                  ·
                    refine ⟨28769661077615659222328693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19179774051743772814885795 28769661077615659222328693)
                    ·
                      refine ⟨2697155726026468052093315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28769661077615659222328693 2697155726026468052093315)
                      ·
                        rfl

theorem cell23_5252692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5252692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252692 prefixEnd_5252692 := by exact prefixLift 5252692
  have htrace : WordTrace (prefixWord ++ tailWord_5252692) baseStart_5252692 baseEnd_5252692 := by
    simpa [prefixWord, tailWord_5252692, baseEnd_5252692] using wordTrace_append hprefix tailTrace_5252692
  have hstable : (prefixWord ++ tailWord_5252692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252692).length < 2 ^ (prefixWord ++ tailWord_5252692).sum := by decide
  have hdescent : baseEnd_5252692 < baseStart_5252692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252715 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_5252715 : Nat := 118140960795 + 5252715 * 2 ^ 59
def prefixEnd_5252715 : Nat := 4983230072969 + 3 ^ 40 * 5252715 * 2
def baseEnd_5252715 : Nat := 2697167536081521462105709

theorem tailTrace_5252715 : CollatzResearch.WordTrace tailWord_5252715 prefixEnd_5252715 2697167536081521462105709 := by
  unfold tailWord_5252715
  simp only [CollatzResearch.WordTrace]
  refine ⟨191582255165318122145943599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127721503443545414763962399 191582255165318122145943599)
  ·
    refine ⟨287373382747977183218915399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191582255165318122145943599 287373382747977183218915399)
    ·
      refine ⟨431060074121965774828373099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287373382747977183218915399 431060074121965774828373099)
      ·
        refine ⟨646590111182948662242559649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431060074121965774828373099 646590111182948662242559649)
        ·
          refine ⟨484942583387211496681919737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646590111182948662242559649 484942583387211496681919737)
          ·
            refine ⟨363706937540408622511439803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484942583387211496681919737 363706937540408622511439803)
            ·
              refine ⟨545560406310612933767159705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363706937540408622511439803 545560406310612933767159705)
              ·
                refine ⟨409170304732959700325369779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545560406310612933767159705 409170304732959700325369779)
                ·
                  refine ⟨613755457099439550488054669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409170304732959700325369779 613755457099439550488054669)
                  ·
                    refine ⟨230158296412289831433020501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613755457099439550488054669 230158296412289831433020501)
                    ·
                      refine ⟨2697167536081521462105709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230158296412289831433020501 2697167536081521462105709)
                      ·
                        rfl

theorem cell23_5252715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_5252715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252715 prefixEnd_5252715 := by exact prefixLift 5252715
  have htrace : WordTrace (prefixWord ++ tailWord_5252715) baseStart_5252715 baseEnd_5252715 := by
    simpa [prefixWord, tailWord_5252715, baseEnd_5252715] using wordTrace_append hprefix tailTrace_5252715
  have hstable : (prefixWord ++ tailWord_5252715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252715).length < 2 ^ (prefixWord ++ tailWord_5252715).sum := by decide
  have hdescent : baseEnd_5252715 < baseStart_5252715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252729 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 5]
def baseStart_5252729 : Nat := 118140960795 + 5252729 * 2 ^ 59
def prefixEnd_5252729 : Nat := 4983230072969 + 3 ^ 40 * 5252729 * 2
def baseEnd_5252729 : Nat := 299686080534520489703405

theorem tailTrace_5252729 : CollatzResearch.WordTrace tailWord_5252729 prefixEnd_5252729 299686080534520489703405 := by
  unfold tailWord_5252729
  simp only [CollatzResearch.WordTrace]
  refine ⟨191582765787267402536953241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127721843858178268357968827 191582765787267402536953241)
  ·
    refine ⟨143687074340450551902714931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191582765787267402536953241 143687074340450551902714931)
    ·
      refine ⟨215530611510675827854072397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143687074340450551902714931 215530611510675827854072397)
      ·
        refine ⟨80823979316503435445277149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215530611510675827854072397 80823979316503435445277149)
        ·
          refine ⟨30308992243688788291978931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80823979316503435445277149 30308992243688788291978931)
          ·
            refine ⟨45463488365533182437968397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30308992243688788291978931 45463488365533182437968397)
            ·
              refine ⟨17048808137074943414238149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45463488365533182437968397 17048808137074943414238149)
              ·
                refine ⟨3196651525701551890169653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17048808137074943414238149 3196651525701551890169653)
                ·
                  refine ⟨299686080534520489703405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3196651525701551890169653 299686080534520489703405)
                  ·
                    rfl

theorem cell23_5252729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 5].length) (baseStart_5252729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252729 prefixEnd_5252729 := by exact prefixLift 5252729
  have htrace : WordTrace (prefixWord ++ tailWord_5252729) baseStart_5252729 baseEnd_5252729 := by
    simpa [prefixWord, tailWord_5252729, baseEnd_5252729] using wordTrace_append hprefix tailTrace_5252729
  have hstable : (prefixWord ++ tailWord_5252729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252729).length < 2 ^ (prefixWord ++ tailWord_5252729).sum := by decide
  have hdescent : baseEnd_5252729 < baseStart_5252729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252759 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 2, 5]
def baseStart_5252759 : Nat := 118140960795 + 5252759 * 2 ^ 59
def prefixEnd_5252759 : Nat := 4983230072969 + 3 ^ 40 * 5252759 * 2
def baseEnd_5252759 : Nat := 899063376410106429985169

theorem tailTrace_5252759 : CollatzResearch.WordTrace tailWord_5252759 prefixEnd_5252759 899063376410106429985169 := by
  unfold tailWord_5252759
  simp only [CollatzResearch.WordTrace]
  refine ⟨191583859977158717660545331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127722573318105811773696887 191583859977158717660545331)
  ·
    refine ⟨287375789965738076490817997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191583859977158717660545331 287375789965738076490817997)
    ·
      refine ⟨107765921237151778684056749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287375789965738076490817997 107765921237151778684056749)
      ·
        refine ⟨40412220463931917006521281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107765921237151778684056749 40412220463931917006521281)
        ·
          refine ⟨30309165347948937754890961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40412220463931917006521281 30309165347948937754890961)
          ·
            refine ⟨22731874010961703316168221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30309165347948937754890961 22731874010961703316168221)
            ·
              refine ⟨8524452754110638743563083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22731874010961703316168221 8524452754110638743563083)
              ·
                refine ⟨12786679131165958115344625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8524452754110638743563083 12786679131165958115344625)
                ·
                  refine ⟨9590009348374468586508469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12786679131165958115344625 9590009348374468586508469)
                  ·
                    refine ⟨899063376410106429985169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9590009348374468586508469 899063376410106429985169)
                    ·
                      rfl

theorem cell23_5252759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_5252759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252759 prefixEnd_5252759 := by exact prefixLift 5252759
  have htrace : WordTrace (prefixWord ++ tailWord_5252759) baseStart_5252759 baseEnd_5252759 := by
    simpa [prefixWord, tailWord_5252759, baseEnd_5252759] using wordTrace_append hprefix tailTrace_5252759
  have hstable : (prefixWord ++ tailWord_5252759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252759).length < 2 ^ (prefixWord ++ tailWord_5252759).sum := by decide
  have hdescent : baseEnd_5252759 < baseStart_5252759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252796 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_5252796 : Nat := 118140960795 + 5252796 * 2 ^ 59
def prefixEnd_5252796 : Nat := 4983230072969 + 3 ^ 40 * 5252796 * 2
def baseEnd_5252796 : Nat := 2697209128014535645192837

theorem tailTrace_5252796 : CollatzResearch.WordTrace tailWord_5252796 prefixEnd_5252796 2697209128014535645192837 := by
  unfold tailWord_5252796
  simp only [CollatzResearch.WordTrace]
  refine ⟨95792604739012336489821121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127723472985349781986428161 95792604739012336489821121)
  ·
    refine ⟨71844453554259252367365841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95792604739012336489821121 71844453554259252367365841)
    ·
      refine ⟨53883340165694439275524381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71844453554259252367365841 53883340165694439275524381)
      ·
        refine ⟨20206252562135414728321643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53883340165694439275524381 20206252562135414728321643)
        ·
          refine ⟨30309378843203122092482465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20206252562135414728321643 30309378843203122092482465)
          ·
            refine ⟨22732034132402341569361849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30309378843203122092482465 22732034132402341569361849)
            ·
              refine ⟨17049025599301756177021387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22732034132402341569361849 17049025599301756177021387)
              ·
                refine ⟨25573538398952634265532081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17049025599301756177021387 25573538398952634265532081)
                ·
                  refine ⟨19180153799214475699149061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25573538398952634265532081 19180153799214475699149061)
                  ·
                    refine ⟨3596278837352714193590449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19180153799214475699149061 3596278837352714193590449)
                    ·
                      refine ⟨2697209128014535645192837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596278837352714193590449 2697209128014535645192837)
                      ·
                        rfl

theorem cell23_5252796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_5252796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252796 prefixEnd_5252796 := by exact prefixLift 5252796
  have htrace : WordTrace (prefixWord ++ tailWord_5252796) baseStart_5252796 baseEnd_5252796 := by
    simpa [prefixWord, tailWord_5252796, baseEnd_5252796] using wordTrace_append hprefix tailTrace_5252796
  have hstable : (prefixWord ++ tailWord_5252796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252796).length < 2 ^ (prefixWord ++ tailWord_5252796).sum := by decide
  have hdescent : baseEnd_5252796 < baseStart_5252796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252840 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5252840 : Nat := 118140960795 + 5252840 * 2 ^ 59
def prefixEnd_5252840 : Nat := 4983230072969 + 3 ^ 40 * 5252840 * 2
def baseEnd_5252840 : Nat := 899077240387777824347545

theorem tailTrace_5252840 : CollatzResearch.WordTrace tailWord_5252840 prefixEnd_5252840 899077240387777824347545 := by
  unfold tailWord_5252840
  simp only [CollatzResearch.WordTrace]
  refine ⟨95793407144932634247121987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127724542859910178996162649 95793407144932634247121987)
  ·
    refine ⟨143690110717398951370682981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95793407144932634247121987 143690110717398951370682981)
    ·
      refine ⟨26941895759512303382003059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143690110717398951370682981 26941895759512303382003059)
      ·
        refine ⟨40412843639268455073004589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26941895759512303382003059 40412843639268455073004589)
        ·
          refine ⟨15154816364725670652376721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40412843639268455073004589 15154816364725670652376721)
          ·
            refine ⟨11366112273544252989282541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15154816364725670652376721 11366112273544252989282541)
            ·
              refine ⟨4262292102579094870980953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11366112273544252989282541 4262292102579094870980953)
              ·
                refine ⟨3196719076934321153235715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262292102579094870980953 3196719076934321153235715)
                ·
                  refine ⟨4795078615401481729853573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196719076934321153235715 4795078615401481729853573)
                  ·
                    refine ⟨899077240387777824347545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795078615401481729853573 899077240387777824347545)
                    ·
                      rfl

theorem cell23_5252840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5252840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252840 prefixEnd_5252840 := by exact prefixLift 5252840
  have htrace : WordTrace (prefixWord ++ tailWord_5252840) baseStart_5252840 baseEnd_5252840 := by
    simpa [prefixWord, tailWord_5252840, baseEnd_5252840] using wordTrace_append hprefix tailTrace_5252840
  have hstable : (prefixWord ++ tailWord_5252840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252840).length < 2 ^ (prefixWord ++ tailWord_5252840).sum := by decide
  have hdescent : baseEnd_5252840 < baseStart_5252840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252866 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5252866 : Nat := 118140960795 + 5252866 * 2 ^ 59
def prefixEnd_5252866 : Nat := 4983230072969 + 3 ^ 40 * 5252866 * 2
def baseEnd_5252866 : Nat := 899081690553450123772505

theorem tailTrace_5252866 : CollatzResearch.WordTrace tailWord_5252866 prefixEnd_5252866 899081690553450123772505 := by
  unfold tailWord_5252866
  simp only [CollatzResearch.WordTrace]
  refine ⟨47896940646942768733672613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127725175058514049956460301 47896940646942768733672613)
  ·
    refine ⟨8980676371301769137563615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47896940646942768733672613 8980676371301769137563615)
    ·
      refine ⟨13471014556952653706345423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8980676371301769137563615 13471014556952653706345423)
      ·
        refine ⟨20206521835428980559518135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13471014556952653706345423 20206521835428980559518135)
        ·
          refine ⟨30309782753143470839277203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20206521835428980559518135 30309782753143470839277203)
          ·
            refine ⟨45464674129715206258915805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30309782753143470839277203 45464674129715206258915805)
            ·
              refine ⟨17049252798643202347093427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45464674129715206258915805 17049252798643202347093427)
              ·
                refine ⟨25573879197964803520640141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17049252798643202347093427 25573879197964803520640141)
                ·
                  refine ⟨9590204699236801320240053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25573879197964803520640141 9590204699236801320240053)
                  ·
                    refine ⟨899081690553450123772505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9590204699236801320240053 899081690553450123772505)
                    ·
                      rfl

theorem cell23_5252866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5252866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252866 prefixEnd_5252866 := by exact prefixLift 5252866
  have htrace : WordTrace (prefixWord ++ tailWord_5252866) baseStart_5252866 baseEnd_5252866 := by
    simpa [prefixWord, tailWord_5252866, baseEnd_5252866] using wordTrace_append hprefix tailTrace_5252866
  have hstable : (prefixWord ++ tailWord_5252866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252866).length < 2 ^ (prefixWord ++ tailWord_5252866).sum := by decide
  have hdescent : baseEnd_5252866 < baseStart_5252866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252879 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 4, 4]
def baseStart_5252879 : Nat := 118140960795 + 5252879 * 2 ^ 59
def prefixEnd_5252879 : Nat := 4983230072969 + 3 ^ 40 * 5252879 * 2
def baseEnd_5252879 : Nat := 899083915636286273484985

theorem tailTrace_5252879 : CollatzResearch.WordTrace tailWord_5252879 prefixEnd_5252879 899083915636286273484985 := by
  unfold tailWord_5252879
  simp only [CollatzResearch.WordTrace]
  refine ⟨191588236736723978154913691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127725491157815985436609127 191588236736723978154913691)
  ·
    refine ⟨287382355105085967232370537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191588236736723978154913691 287382355105085967232370537)
    ·
      refine ⟨215536766328814475424277903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287382355105085967232370537 215536766328814475424277903)
      ·
        refine ⟨323305149493221713136416855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215536766328814475424277903 323305149493221713136416855)
        ·
          refine ⟨484957724239832569704625283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323305149493221713136416855 484957724239832569704625283)
          ·
            refine ⟨727436586359748854556937925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484957724239832569704625283 727436586359748854556937925)
            ·
              refine ⟨136394359942452910229425861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 727436586359748854556937925 136394359942452910229425861)
              ·
                refine ⟨25573942489209920668017349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136394359942452910229425861 25573942489209920668017349)
                ·
                  refine ⟨4795114216726860125253253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25573942489209920668017349 4795114216726860125253253)
                  ·
                    refine ⟨899083915636286273484985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795114216726860125253253 899083915636286273484985)
                    ·
                      rfl

theorem cell23_5252879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_5252879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252879 prefixEnd_5252879 := by exact prefixLift 5252879
  have htrace : WordTrace (prefixWord ++ tailWord_5252879) baseStart_5252879 baseEnd_5252879 := by
    simpa [prefixWord, tailWord_5252879, baseEnd_5252879] using wordTrace_append hprefix tailTrace_5252879
  have hstable : (prefixWord ++ tailWord_5252879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252879).length < 2 ^ (prefixWord ++ tailWord_5252879).sum := by decide
  have hdescent : baseEnd_5252879 < baseStart_5252879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252897 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_5252897 : Nat := 118140960795 + 5252897 * 2 ^ 59
def prefixEnd_5252897 : Nat := 4983230072969 + 3 ^ 40 * 5252897 * 2
def baseEnd_5252897 : Nat := 2697260989560639750029873

theorem tailTrace_5252897 : CollatzResearch.WordTrace tailWord_5252897 prefixEnd_5252897 2697260989560639750029873 := by
  unfold tailWord_5252897
  simp only [CollatzResearch.WordTrace]
  refine ⟨191588893250658767229068945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127725928833772511486045963 191588893250658767229068945)
  ·
    refine ⟨143691669937994075421801709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191588893250658767229068945 143691669937994075421801709)
    ·
      refine ⟨53884376226747778283175641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143691669937994075421801709 53884376226747778283175641)
      ·
        refine ⟨40413282170060833712381731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53884376226747778283175641 40413282170060833712381731)
        ·
          refine ⟨60619923255091250568572597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40413282170060833712381731 60619923255091250568572597)
          ·
            refine ⟨5683117805164804740803681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60619923255091250568572597 5683117805164804740803681)
            ·
              refine ⟨4262338353873603555602761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5683117805164804740803681 4262338353873603555602761)
              ·
                refine ⟨3196753765405202666702071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262338353873603555602761 3196753765405202666702071)
                ·
                  refine ⟨4795130648107804000053107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196753765405202666702071 4795130648107804000053107)
                  ·
                    refine ⟨7192695972161706000079661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4795130648107804000053107 7192695972161706000079661)
                    ·
                      refine ⟨2697260989560639750029873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7192695972161706000079661 2697260989560639750029873)
                      ·
                        rfl

theorem cell23_5252897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_5252897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252897 prefixEnd_5252897 := by exact prefixLift 5252897
  have htrace : WordTrace (prefixWord ++ tailWord_5252897) baseStart_5252897 baseEnd_5252897 := by
    simpa [prefixWord, tailWord_5252897, baseEnd_5252897] using wordTrace_append hprefix tailTrace_5252897
  have hstable : (prefixWord ++ tailWord_5252897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252897).length < 2 ^ (prefixWord ++ tailWord_5252897).sum := by decide
  have hdescent : baseEnd_5252897 < baseStart_5252897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252936 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_5252936 : Nat := 118140960795 + 5252936 * 2 ^ 59
def prefixEnd_5252936 : Nat := 4983230072969 + 3 ^ 40 * 5252936 * 2
def baseEnd_5252936 : Nat := 2697281015306165097442193

theorem tailTrace_5252936 : CollatzResearch.WordTrace tailWord_5252936 prefixEnd_5252936 2697281015306165097442193 := by
  unfold tailWord_5252936
  simp only [CollatzResearch.WordTrace]
  refine ⟨95795157848758738444869331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127726877131678317926492441 95795157848758738444869331)
  ·
    refine ⟨143692736773138107667303997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95795157848758738444869331 143692736773138107667303997)
    ·
      refine ⟨53884776289926790375238999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143692736773138107667303997 53884776289926790375238999)
      ·
        refine ⟨80827164434890185562858499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53884776289926790375238999 80827164434890185562858499)
        ·
          refine ⟨121240746652335278344287749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80827164434890185562858499 121240746652335278344287749)
          ·
            refine ⟨22732639997312864689553953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121240746652335278344287749 22732639997312864689553953)
            ·
              refine ⟨17049479997984648517165465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22732639997312864689553953 17049479997984648517165465)
              ·
                refine ⟨12787109998488486387874099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17049479997984648517165465 12787109998488486387874099)
                ·
                  refine ⟨19180664997732729581811149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12787109998488486387874099 19180664997732729581811149)
                  ·
                    refine ⟨7192749374149773593179181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19180664997732729581811149 7192749374149773593179181)
                    ·
                      refine ⟨2697281015306165097442193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7192749374149773593179181 2697281015306165097442193)
                      ·
                        rfl

theorem cell23_5252936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_5252936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252936 prefixEnd_5252936 := by exact prefixLift 5252936
  have htrace : WordTrace (prefixWord ++ tailWord_5252936) baseStart_5252936 baseEnd_5252936 := by
    simpa [prefixWord, tailWord_5252936, baseEnd_5252936] using wordTrace_append hprefix tailTrace_5252936
  have hstable : (prefixWord ++ tailWord_5252936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252936).length < 2 ^ (prefixWord ++ tailWord_5252936).sum := by decide
  have hdescent : baseEnd_5252936 < baseStart_5252936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5252979 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5]
def baseStart_5252979 : Nat := 118140960795 + 5252979 * 2 ^ 59
def prefixEnd_5252979 : Nat := 4983230072969 + 3 ^ 40 * 5252979 * 2
def baseEnd_5252979 : Nat := 2697303094974308429204495

theorem tailTrace_5252979 : CollatzResearch.WordTrace tailWord_5252979 prefixEnd_5252979 2697303094974308429204495 := by
  unfold tailWord_5252979
  simp only [CollatzResearch.WordTrace]
  refine ⟨191591884036361695233553991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127727922690907796822369327 191591884036361695233553991)
  ·
    refine ⟨287387826054542542850330987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191591884036361695233553991 287387826054542542850330987)
    ·
      refine ⟨431081739081813814275496481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287387826054542542850330987 431081739081813814275496481)
      ·
        refine ⟨323311304311360360706622361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431081739081813814275496481 323311304311360360706622361)
        ·
          refine ⟨242483478233520270529966771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323311304311360360706622361 242483478233520270529966771)
          ·
            refine ⟨363725217350280405794950157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242483478233520270529966771 363725217350280405794950157)
            ·
              refine ⟨136396956506355152173106309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363725217350280405794950157 136396956506355152173106309)
              ·
                refine ⟨25574429344941591032457433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136396956506355152173106309 25574429344941591032457433)
                ·
                  refine ⟨19180822008706193274343075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25574429344941591032457433 19180822008706193274343075)
                  ·
                    refine ⟨28771233013059289911514613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19180822008706193274343075 28771233013059289911514613)
                    ·
                      refine ⟨2697303094974308429204495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28771233013059289911514613 2697303094974308429204495)
                      ·
                        rfl

theorem cell23_5252979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_5252979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5252979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5252979 prefixEnd_5252979 := by exact prefixLift 5252979
  have htrace : WordTrace (prefixWord ++ tailWord_5252979) baseStart_5252979 baseEnd_5252979 := by
    simpa [prefixWord, tailWord_5252979, baseEnd_5252979] using wordTrace_append hprefix tailTrace_5252979
  have hstable : (prefixWord ++ tailWord_5252979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5252979).length < 2 ^ (prefixWord ++ tailWord_5252979).sum := by decide
  have hdescent : baseEnd_5252979 < baseStart_5252979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5252979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253029 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_5253029 : Nat := 118140960795 + 5253029 * 2 ^ 59
def prefixEnd_5253029 : Nat := 4983230072969 + 3 ^ 40 * 5253029 * 2
def baseEnd_5253029 : Nat := 899109589669011077859755

theorem tailTrace_5253029 : CollatzResearch.WordTrace tailWord_5253029 prefixEnd_5253029 899109589669011077859755 := by
  unfold tailWord_5253029
  simp only [CollatzResearch.WordTrace]
  refine ⟨191593707686180553772874141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127729138457453702515249427 191593707686180553772874141)
  ·
    refine ⟨71847640382317707664827803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191593707686180553772874141 71847640382317707664827803)
    ·
      refine ⟨107771460573476561497241705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71847640382317707664827803 107771460573476561497241705)
      ·
        refine ⟨80828595430107421122931279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107771460573476561497241705 80828595430107421122931279)
        ·
          refine ⟨121242893145161131684396919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80828595430107421122931279 121242893145161131684396919)
          ·
            refine ⟨181864339717741697526595379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121242893145161131684396919 181864339717741697526595379)
            ·
              refine ⟨272796509576612546289893069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181864339717741697526595379 272796509576612546289893069)
              ·
                refine ⟨102298691091229704858709901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272796509576612546289893069 102298691091229704858709901)
                ·
                  refine ⟨38362009159211139322016213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102298691091229704858709901 38362009159211139322016213)
                  ·
                    refine ⟨899109589669011077859755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38362009159211139322016213 899109589669011077859755)
                    ·
                      rfl

theorem cell23_5253029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_5253029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253029 prefixEnd_5253029 := by exact prefixLift 5253029
  have htrace : WordTrace (prefixWord ++ tailWord_5253029) baseStart_5253029 baseEnd_5253029 := by
    simpa [prefixWord, tailWord_5253029, baseEnd_5253029] using wordTrace_append hprefix tailTrace_5253029
  have hstable : (prefixWord ++ tailWord_5253029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253029).length < 2 ^ (prefixWord ++ tailWord_5253029).sum := by decide
  have hdescent : baseEnd_5253029 < baseStart_5253029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253039 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_5253039 : Nat := 118140960795 + 5253039 * 2 ^ 59
def prefixEnd_5253039 : Nat := 4983230072969 + 3 ^ 40 * 5253039 * 2
def baseEnd_5253039 : Nat := 2697333903813578194454219

theorem tailTrace_5253039 : CollatzResearch.WordTrace tailWord_5253039 prefixEnd_5253039 2697333903813578194454219 := by
  unfold tailWord_5253039
  simp only [CollatzResearch.WordTrace]
  refine ⟨191594072416144325480738171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127729381610762883653825447 191594072416144325480738171)
  ·
    refine ⟨287391108624216488221107257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191594072416144325480738171 287391108624216488221107257)
    ·
      refine ⟨215543331468162366165830443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287391108624216488221107257 215543331468162366165830443)
      ·
        refine ⟨323314997202243549248745665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215543331468162366165830443 323314997202243549248745665)
        ·
          refine ⟨242486247901682661936559249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323314997202243549248745665 242486247901682661936559249)
          ·
            refine ⟨181864685926261996452419437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242486247901682661936559249 181864685926261996452419437)
            ·
              refine ⟨68199257222348248669657289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181864685926261996452419437 68199257222348248669657289)
              ·
                refine ⟨51149442916761186502242967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68199257222348248669657289 51149442916761186502242967)
                ·
                  refine ⟨76724164375141779753364451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51149442916761186502242967 76724164375141779753364451)
                  ·
                    refine ⟨115086246562712669630046677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76724164375141779753364451 115086246562712669630046677)
                    ·
                      refine ⟨2697333903813578194454219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115086246562712669630046677 2697333903813578194454219)
                      ·
                        rfl

theorem cell23_5253039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_5253039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253039 prefixEnd_5253039 := by exact prefixLift 5253039
  have htrace : WordTrace (prefixWord ++ tailWord_5253039) baseStart_5253039 baseEnd_5253039 := by
    simpa [prefixWord, tailWord_5253039, baseEnd_5253039] using wordTrace_append hprefix tailTrace_5253039
  have hstable : (prefixWord ++ tailWord_5253039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253039).length < 2 ^ (prefixWord ++ tailWord_5253039).sum := by decide
  have hdescent : baseEnd_5253039 < baseStart_5253039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253177 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5253177 : Nat := 118140960795 + 5253177 * 2 ^ 59
def prefixEnd_5253177 : Nat := 4983230072969 + 3 ^ 40 * 5253177 * 2
def baseEnd_5253177 : Nat := 2697404764143898654528585

theorem tailTrace_5253177 : CollatzResearch.WordTrace tailWord_5253177 prefixEnd_5253177 2697404764143898654528585 := by
  unfold tailWord_5253177
  simp only [CollatzResearch.WordTrace]
  refine ⟨191599105689644375049261785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127732737126429583366174523 191599105689644375049261785)
  ·
    refine ⟨143699329267233281286946339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191599105689644375049261785 143699329267233281286946339)
    ·
      refine ⟨215548993900849921930419509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143699329267233281286946339 215548993900849921930419509)
      ·
        refine ⟨20207718178204680180976829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215548993900849921930419509 20207718178204680180976829)
        ·
          refine ⟨7577894316826755067866311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20207718178204680180976829 7577894316826755067866311)
          ·
            refine ⟨11366841475240132601799467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7577894316826755067866311 11366841475240132601799467)
            ·
              refine ⟨17050262212860198902699201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11366841475240132601799467 17050262212860198902699201)
              ·
                refine ⟨12787696659645149177024401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17050262212860198902699201 12787696659645149177024401)
                ·
                  refine ⟨9590772494733861882768301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12787696659645149177024401 9590772494733861882768301)
                  ·
                    refine ⟨3596539685525198206038113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9590772494733861882768301 3596539685525198206038113)
                    ·
                      refine ⟨2697404764143898654528585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596539685525198206038113 2697404764143898654528585)
                      ·
                        rfl

theorem cell23_5253177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5253177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253177 prefixEnd_5253177 := by exact prefixLift 5253177
  have htrace : WordTrace (prefixWord ++ tailWord_5253177) baseStart_5253177 baseEnd_5253177 := by
    simpa [prefixWord, tailWord_5253177, baseEnd_5253177] using wordTrace_append hprefix tailTrace_5253177
  have hstable : (prefixWord ++ tailWord_5253177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253177).length < 2 ^ (prefixWord ++ tailWord_5253177).sum := by decide
  have hdescent : baseEnd_5253177 < baseStart_5253177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253183 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 4, 4]
def baseStart_5253183 : Nat := 118140960795 + 5253183 * 2 ^ 59
def prefixEnd_5253183 : Nat := 4983230072969 + 3 ^ 40 * 5253183 * 2
def baseEnd_5253183 : Nat := 899135948342608543684519

theorem tailTrace_5253183 : CollatzResearch.WordTrace tailWord_5253183 prefixEnd_5253183 899135948342608543684519 := by
  unfold tailWord_5253183
  simp only [CollatzResearch.WordTrace]
  refine ⟨191599324527622638073980203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127732883018415092049320135 191599324527622638073980203)
  ·
    refine ⟨287398986791433957110970305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191599324527622638073980203 287398986791433957110970305)
    ·
      refine ⟨215549240093575467833227729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287398986791433957110970305 215549240093575467833227729)
      ·
        refine ⟨161661930070181600874920797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215549240093575467833227729 161661930070181600874920797)
        ·
          refine ⟨60623223776318100328095299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161661930070181600874920797 60623223776318100328095299)
          ·
            refine ⟨90934835664477150492142949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60623223776318100328095299 90934835664477150492142949)
            ·
              refine ⟨17050281687089465717276803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90934835664477150492142949 17050281687089465717276803)
              ·
                refine ⟨25575422530634198575915205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17050281687089465717276803 25575422530634198575915205)
                ·
                  refine ⟨4795391724493912232984101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25575422530634198575915205 4795391724493912232984101)
                  ·
                    refine ⟨899135948342608543684519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795391724493912232984101 899135948342608543684519)
                    ·
                      rfl

theorem cell23_5253183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_5253183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253183 prefixEnd_5253183 := by exact prefixLift 5253183
  have htrace : WordTrace (prefixWord ++ tailWord_5253183) baseStart_5253183 baseEnd_5253183 := by
    simpa [prefixWord, tailWord_5253183, baseEnd_5253183] using wordTrace_append hprefix tailTrace_5253183
  have hstable : (prefixWord ++ tailWord_5253183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253183).length < 2 ^ (prefixWord ++ tailWord_5253183).sum := by decide
  have hdescent : baseEnd_5253183 < baseStart_5253183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253184 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 1, 1, 3]
def baseStart_5253184 : Nat := 118140960795 + 5253184 * 2 ^ 59
def prefixEnd_5253184 : Nat := 4983230072969 + 3 ^ 40 * 5253184 * 2
def baseEnd_5253184 : Nat := 2697408358508480127141053

theorem tailTrace_5253184 : CollatzResearch.WordTrace tailWord_5253184 prefixEnd_5253184 2697408358508480127141053 := by
  unfold tailWord_5253184
  simp only [CollatzResearch.WordTrace]
  refine ⟨95799680500309507622383303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127732907333746010163177737 95799680500309507622383303)
  ·
    refine ⟨143699520750464261433574955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95799680500309507622383303 143699520750464261433574955)
    ·
      refine ⟨215549281125696392150362433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143699520750464261433574955 215549281125696392150362433)
      ·
        refine ⟨161661960844272294112771825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215549281125696392150362433 161661960844272294112771825)
        ·
          refine ⟨121246470633204220584578869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161661960844272294112771825 121246470633204220584578869)
          ·
            refine ⟨11366856621862895679804269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121246470633204220584578869 11366856621862895679804269)
            ·
              refine ⟨4262571233198585879926601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11366856621862895679804269 4262571233198585879926601)
              ·
                refine ⟨3196928424898939409944951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262571233198585879926601 3196928424898939409944951)
                ·
                  refine ⟨4795392637348409114917427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196928424898939409944951 4795392637348409114917427)
                  ·
                    refine ⟨7193088956022613672376141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4795392637348409114917427 7193088956022613672376141)
                    ·
                      refine ⟨2697408358508480127141053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7193088956022613672376141 2697408358508480127141053)
                      ·
                        rfl

theorem cell23_5253184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_5253184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253184 prefixEnd_5253184 := by exact prefixLift 5253184
  have htrace : WordTrace (prefixWord ++ tailWord_5253184) baseStart_5253184 baseEnd_5253184 := by
    simpa [prefixWord, tailWord_5253184, baseEnd_5253184] using wordTrace_append hprefix tailTrace_5253184
  have hstable : (prefixWord ++ tailWord_5253184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253184).length < 2 ^ (prefixWord ++ tailWord_5253184).sum := by decide
  have hdescent : baseEnd_5253184 < baseStart_5253184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253193 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_5253193 : Nat := 118140960795 + 5253193 * 2 ^ 59
def prefixEnd_5253193 : Nat := 4983230072969 + 3 ^ 40 * 5253193 * 2
def baseEnd_5253193 : Nat := 2697412979834370591928511

theorem tailTrace_5253193 : CollatzResearch.WordTrace tailWord_5253193 prefixEnd_5253193 2697412979834370591928511 := by
  unfold tailWord_5253193
  simp only [CollatzResearch.WordTrace]
  refine ⟨191599689257586409781844233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127733126171724273187896155 191599689257586409781844233)
  ·
    refine ⟨143699766943189807336383175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191599689257586409781844233 143699766943189807336383175)
    ·
      refine ⟨215549650414784711004574763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143699766943189807336383175 215549650414784711004574763)
      ·
        refine ⟨323324475622177066506862145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215549650414784711004574763 323324475622177066506862145)
        ·
          refine ⟨242493356716632799880146609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323324475622177066506862145 242493356716632799880146609)
          ·
            refine ⟨181870017537474599910109957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242493356716632799880146609 181870017537474599910109957)
            ·
              refine ⟨34100628288276487483145617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181870017537474599910109957 34100628288276487483145617)
              ·
                refine ⟨25575471216207365612359213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34100628288276487483145617 25575471216207365612359213)
                ·
                  refine ⟨9590801706077762104634705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25575471216207365612359213 9590801706077762104634705)
                  ·
                    refine ⟨7193101279558321578476029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9590801706077762104634705 7193101279558321578476029)
                    ·
                      refine ⟨2697412979834370591928511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7193101279558321578476029 2697412979834370591928511)
                      ·
                        rfl

theorem cell23_5253193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_5253193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253193 prefixEnd_5253193 := by exact prefixLift 5253193
  have htrace : WordTrace (prefixWord ++ tailWord_5253193) baseStart_5253193 baseEnd_5253193 := by
    simpa [prefixWord, tailWord_5253193, baseEnd_5253193] using wordTrace_append hprefix tailTrace_5253193
  have hstable : (prefixWord ++ tailWord_5253193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253193).length < 2 ^ (prefixWord ++ tailWord_5253193).sum := by decide
  have hdescent : baseEnd_5253193 < baseStart_5253193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253196 : List Nat := [2, 2, 1, 3, 1, 1, 3, 10]
def baseStart_5253196 : Nat := 118140960795 + 5253196 * 2 ^ 59
def prefixEnd_5253196 : Nat := 4983230072969 + 3 ^ 40 * 5253196 * 2
def baseEnd_5253196 : Nat := 99904241491716077044111

theorem tailTrace_5253196 : CollatzResearch.WordTrace tailWord_5253196 prefixEnd_5253196 99904241491716077044111 := by
  unfold tailWord_5253196
  simp only [CollatzResearch.WordTrace]
  refine ⟨95799899338287770647101721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127733199117717027529468961 95799899338287770647101721)
  ·
    refine ⟨71849924503715827985326291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95799899338287770647101721 71849924503715827985326291)
    ·
      refine ⟨107774886755573741977989437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71849924503715827985326291 107774886755573741977989437)
      ·
        refine ⟨40415582533340153241746039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107774886755573741977989437 40415582533340153241746039)
        ·
          refine ⟨60623373800010229862619059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40415582533340153241746039 60623373800010229862619059)
          ·
            refine ⟨90935060700015344793928589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60623373800010229862619059 90935060700015344793928589)
            ·
              refine ⟨34100647762505754297723221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90935060700015344793928589 34100647762505754297723221)
              ·
                refine ⟨99904241491716077044111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34100647762505754297723221 99904241491716077044111)
                ·
                  rfl

theorem cell23_5253196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 10].length) (baseStart_5253196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253196 prefixEnd_5253196 := by exact prefixLift 5253196
  have htrace : WordTrace (prefixWord ++ tailWord_5253196) baseStart_5253196 baseEnd_5253196 := by
    simpa [prefixWord, tailWord_5253196, baseEnd_5253196] using wordTrace_append hprefix tailTrace_5253196
  have hstable : (prefixWord ++ tailWord_5253196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253196).length < 2 ^ (prefixWord ++ tailWord_5253196).sum := by decide
  have hdescent : baseEnd_5253196 < baseStart_5253196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253241 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 1, 2, 2]
def baseStart_5253241 : Nat := 118140960795 + 5253241 * 2 ^ 59
def prefixEnd_5253241 : Nat := 4983230072969 + 3 ^ 40 * 5253241 * 2
def baseEnd_5253241 : Nat := 2697437626905786404128291

theorem tailTrace_5253241 : CollatzResearch.WordTrace tailWord_5253241 prefixEnd_5253241 2697437626905786404128291 := by
  unfold tailWord_5253241
  simp only [CollatzResearch.WordTrace]
  refine ⟨191601439961412513979591577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127734293307608342653061051 191601439961412513979591577)
  ·
    refine ⟨143701079971059385484693683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191601439961412513979591577 143701079971059385484693683)
    ·
      refine ⟨215551619956589078227040525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143701079971059385484693683 215551619956589078227040525)
      ·
        refine ⟨80831857483720904335140197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215551619956589078227040525 80831857483720904335140197)
        ·
          refine ⟨15155973278197669562838787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80831857483720904335140197 15155973278197669562838787)
          ·
            refine ⟨22733959917296504344258181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15155973278197669562838787 22733959917296504344258181)
            ·
              refine ⟨4262617484493094564548409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22733959917296504344258181 4262617484493094564548409)
              ·
                refine ⟨3196963113369820923411307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262617484493094564548409 3196963113369820923411307)
                ·
                  refine ⟨4795444670054731385116961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196963113369820923411307 4795444670054731385116961)
                  ·
                    refine ⟨3596583502541048538837721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4795444670054731385116961 3596583502541048538837721)
                    ·
                      refine ⟨2697437626905786404128291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596583502541048538837721 2697437626905786404128291)
                      ·
                        rfl

theorem cell23_5253241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_5253241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253241 prefixEnd_5253241 := by exact prefixLift 5253241
  have htrace : WordTrace (prefixWord ++ tailWord_5253241) baseStart_5253241 baseEnd_5253241 := by
    simpa [prefixWord, tailWord_5253241, baseEnd_5253241] using wordTrace_append hprefix tailTrace_5253241
  have hstable : (prefixWord ++ tailWord_5253241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253241).length < 2 ^ (prefixWord ++ tailWord_5253241).sum := by decide
  have hdescent : baseEnd_5253241 < baseStart_5253241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253278 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_5253278 : Nat := 118140960795 + 5253278 * 2 ^ 59
def prefixEnd_5253278 : Nat := 4983230072969 + 3 ^ 40 * 5253278 * 2
def baseEnd_5253278 : Nat := 2697456625690002759365621

theorem tailTrace_5253278 : CollatzResearch.WordTrace tailWord_5253278 prefixEnd_5253278 2697456625690002759365621 := by
  unfold tailWord_5253278
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950348682784808662336061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127735192974852312865792325 23950348682784808662336061)
  ·
    refine ⟨8981380756044303248376023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23950348682784808662336061 8981380756044303248376023)
    ·
      refine ⟨13472071134066454872564035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981380756044303248376023 13472071134066454872564035)
      ·
        refine ⟨20208106701099682308846053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13472071134066454872564035 20208106701099682308846053)
        ·
          refine ⟨3789020006456190432908635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20208106701099682308846053 3789020006456190432908635)
          ·
            refine ⟨5683530009684285649362953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789020006456190432908635 5683530009684285649362953)
            ·
              refine ⟨4262647507263214237022215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5683530009684285649362953 4262647507263214237022215)
              ·
                refine ⟨6393971260894821355533323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262647507263214237022215 6393971260894821355533323)
                ·
                  refine ⟨9590956891342232033299985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6393971260894821355533323 9590956891342232033299985)
                  ·
                    refine ⟨7193217668506674024974989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9590956891342232033299985 7193217668506674024974989)
                    ·
                      refine ⟨2697456625690002759365621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7193217668506674024974989 2697456625690002759365621)
                      ·
                        rfl

theorem cell23_5253278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_5253278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253278 prefixEnd_5253278 := by exact prefixLift 5253278
  have htrace : WordTrace (prefixWord ++ tailWord_5253278) baseStart_5253278 baseEnd_5253278 := by
    simpa [prefixWord, tailWord_5253278, baseEnd_5253278] using wordTrace_append hprefix tailTrace_5253278
  have hstable : (prefixWord ++ tailWord_5253278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253278).length < 2 ^ (prefixWord ++ tailWord_5253278).sum := by decide
  have hdescent : baseEnd_5253278 < baseStart_5253278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253284 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_5253284 : Nat := 118140960795 + 5253284 * 2 ^ 59
def prefixEnd_5253284 : Nat := 4983230072969 + 3 ^ 40 * 5253284 * 2
def baseEnd_5253284 : Nat := 2697459706573929735890593

theorem tailTrace_5253284 : CollatzResearch.WordTrace tailWord_5253284 prefixEnd_5253284 2697459706573929735890593 := by
  unfold tailWord_5253284
  simp only [CollatzResearch.WordTrace]
  refine ⟨95801504150128366161703453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127735338866837821548937937 95801504150128366161703453)
  ·
    refine ⟨35925564056298137310638795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95801504150128366161703453 35925564056298137310638795)
    ·
      refine ⟨53888346084447205965958193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35925564056298137310638795 53888346084447205965958193)
      ·
        refine ⟨40416259563335404474468645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53888346084447205965958193 40416259563335404474468645)
        ·
          refine ⟨7578048668125388338962871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40416259563335404474468645 7578048668125388338962871)
          ·
            refine ⟨11367073002188082508444307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578048668125388338962871 11367073002188082508444307)
            ·
              refine ⟨17050609503282123762666461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367073002188082508444307 17050609503282123762666461)
              ·
                refine ⟨6393978563730796410999923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17050609503282123762666461 6393978563730796410999923)
                ·
                  refine ⟨9590967845596194616499885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6393978563730796410999923 9590967845596194616499885)
                  ·
                    refine ⟨3596612942098572981187457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9590967845596194616499885 3596612942098572981187457)
                    ·
                      refine ⟨2697459706573929735890593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596612942098572981187457 2697459706573929735890593)
                      ·
                        rfl

theorem cell23_5253284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_5253284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253284 prefixEnd_5253284 := by exact prefixLift 5253284
  have htrace : WordTrace (prefixWord ++ tailWord_5253284) baseStart_5253284 baseEnd_5253284 := by
    simpa [prefixWord, tailWord_5253284, baseEnd_5253284] using wordTrace_append hprefix tailTrace_5253284
  have hstable : (prefixWord ++ tailWord_5253284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253284).length < 2 ^ (prefixWord ++ tailWord_5253284).sum := by decide
  have hdescent : baseEnd_5253284 < baseStart_5253284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253303 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 7]
def baseStart_5253303 : Nat := 118140960795 + 5253303 * 2 ^ 59
def prefixEnd_5253303 : Nat := 4983230072969 + 3 ^ 40 * 5253303 * 2
def baseEnd_5253303 : Nat := 299718829189596129061445

theorem tailTrace_5253303 : CollatzResearch.WordTrace tailWord_5253303 prefixEnd_5253303 299718829189596129061445 := by
  unfold tailWord_5253303
  simp only [CollatzResearch.WordTrace]
  refine ⟨191603701287187898568348563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127735800858125265712232375 191603701287187898568348563)
  ·
    refine ⟨287405551930781847852522845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191603701287187898568348563 287405551930781847852522845)
    ·
      refine ⟨107777081974043192944696067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287405551930781847852522845 107777081974043192944696067)
      ·
        refine ⟨161665622961064789417044101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107777081974043192944696067 161665622961064789417044101)
        ·
          refine ⟨30312304305199648015695769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161665622961064789417044101 30312304305199648015695769)
          ·
            refine ⟨22734228228899736011771827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30312304305199648015695769 22734228228899736011771827)
            ·
              refine ⟨34101342343349604017657741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22734228228899736011771827 34101342343349604017657741)
              ·
                refine ⟨12788003378756101506621653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34101342343349604017657741 12788003378756101506621653)
                ·
                  refine ⟨299718829189596129061445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12788003378756101506621653 299718829189596129061445)
                  ·
                    rfl

theorem cell23_5253303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 7].length) (baseStart_5253303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253303 prefixEnd_5253303 := by exact prefixLift 5253303
  have htrace : WordTrace (prefixWord ++ tailWord_5253303) baseStart_5253303 baseEnd_5253303 := by
    simpa [prefixWord, tailWord_5253303, baseEnd_5253303] using wordTrace_append hprefix tailTrace_5253303
  have hstable : (prefixWord ++ tailWord_5253303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253303).length < 2 ^ (prefixWord ++ tailWord_5253303).sum := by decide
  have hdescent : baseEnd_5253303 < baseStart_5253303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253343 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_5253343 : Nat := 118140960795 + 5253343 * 2 ^ 59
def prefixEnd_5253343 : Nat := 4983230072969 + 3 ^ 40 * 5253343 * 2
def baseEnd_5253343 : Nat := 2697490001932545005052821

theorem tailTrace_5253343 : CollatzResearch.WordTrace tailWord_5253343 prefixEnd_5253343 2697490001932545005052821 := by
  unfold tailWord_5253343
  simp only [CollatzResearch.WordTrace]
  refine ⟨191605160207042985399804683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127736773471361990266536455 191605160207042985399804683)
  ·
    refine ⟨287407740310564478099707025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191605160207042985399804683 287407740310564478099707025)
    ·
      refine ⟨215555805232923358574780269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287407740310564478099707025 215555805232923358574780269)
      ·
        refine ⟨80833426962346259465542601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215555805232923358574780269 80833426962346259465542601)
        ·
          refine ⟨60625070221759694599156951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80833426962346259465542601 60625070221759694599156951)
          ·
            refine ⟨90937605332639541898735427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60625070221759694599156951 90937605332639541898735427)
            ·
              refine ⟨136406407998959312848103141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90937605332639541898735427 136406407998959312848103141)
              ·
                refine ⟨25576201499804871159019339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136406407998959312848103141 25576201499804871159019339)
                ·
                  refine ⟨38364302249707306738529009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25576201499804871159019339 38364302249707306738529009)
                  ·
                    refine ⟨28773226687280480053896757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38364302249707306738529009 28773226687280480053896757)
                    ·
                      refine ⟨2697490001932545005052821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28773226687280480053896757 2697490001932545005052821)
                      ·
                        rfl

theorem cell23_5253343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_5253343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253343 prefixEnd_5253343 := by exact prefixLift 5253343
  have htrace : WordTrace (prefixWord ++ tailWord_5253343) baseStart_5253343 baseEnd_5253343 := by
    simpa [prefixWord, tailWord_5253343, baseEnd_5253343] using wordTrace_append hprefix tailTrace_5253343
  have hstable : (prefixWord ++ tailWord_5253343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253343).length < 2 ^ (prefixWord ++ tailWord_5253343).sum := by decide
  have hdescent : baseEnd_5253343 < baseStart_5253343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253373 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_5253373 : Nat := 118140960795 + 5253373 * 2 ^ 59
def prefixEnd_5253373 : Nat := 4983230072969 + 3 ^ 40 * 5253373 * 2
def baseEnd_5253373 : Nat := 2697505406352179887677683

theorem tailTrace_5253373 : CollatzResearch.WordTrace tailWord_5253373 prefixEnd_5253373 2697505406352179887677683 := by
  unfold tailWord_5253373
  simp only [CollatzResearch.WordTrace]
  refine ⟨191606254396934300523396773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127737502931289533682264515 191606254396934300523396773)
  ·
    refine ⟨35926172699425181348136895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191606254396934300523396773 35926172699425181348136895)
    ·
      refine ⟨53889259049137772022205343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35926172699425181348136895 53889259049137772022205343)
      ·
        refine ⟨80833888573706658033308015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53889259049137772022205343 80833888573706658033308015)
        ·
          refine ⟨121250832860559987049962023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80833888573706658033308015 121250832860559987049962023)
          ·
            refine ⟨181876249290839980574943035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121250832860559987049962023 181876249290839980574943035)
            ·
              refine ⟨272814373936259970862414553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181876249290839980574943035 272814373936259970862414553)
              ·
                refine ⟨204610780452194978146810915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272814373936259970862414553 204610780452194978146810915)
                ·
                  refine ⟨306916170678292467220216373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204610780452194978146810915 306916170678292467220216373)
                  ·
                    refine ⟨28773391001089918801895285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 306916170678292467220216373 28773391001089918801895285)
                    ·
                      refine ⟨2697505406352179887677683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28773391001089918801895285 2697505406352179887677683)
                      ·
                        rfl

theorem cell23_5253373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_5253373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253373 prefixEnd_5253373 := by exact prefixLift 5253373
  have htrace : WordTrace (prefixWord ++ tailWord_5253373) baseStart_5253373 baseEnd_5253373 := by
    simpa [prefixWord, tailWord_5253373, baseEnd_5253373] using wordTrace_append hprefix tailTrace_5253373
  have hstable : (prefixWord ++ tailWord_5253373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253373).length < 2 ^ (prefixWord ++ tailWord_5253373).sum := by decide
  have hdescent : baseEnd_5253373 < baseStart_5253373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253407 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_5253407 : Nat := 118140960795 + 5253407 * 2 ^ 59
def prefixEnd_5253407 : Nat := 4983230072969 + 3 ^ 40 * 5253407 * 2
def baseEnd_5253407 : Nat := 2697522864694432754652527

theorem tailTrace_5253407 : CollatzResearch.WordTrace tailWord_5253407 prefixEnd_5253407 2697522864694432754652527 := by
  unfold tailWord_5253407
  simp only [CollatzResearch.WordTrace]
  refine ⟨191607494478811124330134475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127738329652540749553422983 191607494478811124330134475)
  ·
    refine ⟨287411241718216686495201713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191607494478811124330134475 287411241718216686495201713)
    ·
      refine ⟨215558431288662514871401285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287411241718216686495201713 215558431288662514871401285)
      ·
        refine ⟨40417205866624221538387741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215558431288662514871401285 40417205866624221538387741)
        ·
          refine ⟨15156452199984083076895403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40417205866624221538387741 15156452199984083076895403)
          ·
            refine ⟨22734678299976124615343105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15156452199984083076895403 22734678299976124615343105)
            ·
              refine ⟨17051008724982093461507329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22734678299976124615343105 17051008724982093461507329)
              ·
                refine ⟨12788256543736570096130497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17051008724982093461507329 12788256543736570096130497)
                ·
                  refine ⟨9591192407802427572097873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12788256543736570096130497 9591192407802427572097873)
                  ·
                    refine ⟨7193394305851820679073405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9591192407802427572097873 7193394305851820679073405)
                    ·
                      refine ⟨2697522864694432754652527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7193394305851820679073405 2697522864694432754652527)
                      ·
                        rfl

theorem cell23_5253407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_5253407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253407 prefixEnd_5253407 := by exact prefixLift 5253407
  have htrace : WordTrace (prefixWord ++ tailWord_5253407) baseStart_5253407 baseEnd_5253407 := by
    simpa [prefixWord, tailWord_5253407, baseEnd_5253407] using wordTrace_append hprefix tailTrace_5253407
  have hstable : (prefixWord ++ tailWord_5253407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253407).length < 2 ^ (prefixWord ++ tailWord_5253407).sum := by decide
  have hdescent : baseEnd_5253407 < baseStart_5253407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253421 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5253421 : Nat := 118140960795 + 5253421 * 2 ^ 59
def prefixEnd_5253421 : Nat := 4983230072969 + 3 ^ 40 * 5253421 * 2
def baseEnd_5253421 : Nat := 2697530053423595699877463

theorem tailTrace_5253421 : CollatzResearch.WordTrace tailWord_5253421 prefixEnd_5253421 2697530053423595699877463 := by
  unfold tailWord_5253421
  simp only [CollatzResearch.WordTrace]
  refine ⟨191608005100760404721144117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127738670067173603147429411 191608005100760404721144117)
  ·
    refine ⟨17963250478196287942607261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191608005100760404721144117 17963250478196287942607261)
    ·
      refine ⟨6736218929323607978477723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17963250478196287942607261 6736218929323607978477723)
      ·
        refine ⟨10104328393985411967716585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736218929323607978477723 10104328393985411967716585)
        ·
          refine ⟨7578246295489058975787439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10104328393985411967716585 7578246295489058975787439)
          ·
            refine ⟨11367369443233588463681159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578246295489058975787439 11367369443233588463681159)
            ·
              refine ⟨17051054164850382695521739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367369443233588463681159 17051054164850382695521739)
              ·
                refine ⟨25576581247275574043282609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17051054164850382695521739 25576581247275574043282609)
                ·
                  refine ⟨19182435935456680532461957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25576581247275574043282609 19182435935456680532461957)
                  ·
                    refine ⟨3596706737898127599836617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19182435935456680532461957 3596706737898127599836617)
                    ·
                      refine ⟨2697530053423595699877463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596706737898127599836617 2697530053423595699877463)
                      ·
                        rfl

theorem cell23_5253421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5253421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253421 prefixEnd_5253421 := by exact prefixLift 5253421
  have htrace : WordTrace (prefixWord ++ tailWord_5253421) baseStart_5253421 baseEnd_5253421 := by
    simpa [prefixWord, tailWord_5253421, baseEnd_5253421] using wordTrace_append hprefix tailTrace_5253421
  have hstable : (prefixWord ++ tailWord_5253421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253421).length < 2 ^ (prefixWord ++ tailWord_5253421).sum := by decide
  have hdescent : baseEnd_5253421 < baseStart_5253421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253441 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5253441 : Nat := 118140960795 + 5253441 * 2 ^ 59
def prefixEnd_5253441 : Nat := 4983230072969 + 3 ^ 40 * 5253441 * 2
def baseEnd_5253441 : Nat := 2697540323036685621627371

theorem tailTrace_5253441 : CollatzResearch.WordTrace tailWord_5253441 prefixEnd_5253441 2697540323036685621627371 := by
  unfold tailWord_5253441
  simp only [CollatzResearch.WordTrace]
  refine ⟨191608734560687948136872177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127739156373791965424581451 191608734560687948136872177)
  ·
    refine ⟨143706550920515961102654133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191608734560687948136872177 143706550920515961102654133)
    ·
      refine ⟨13472489148798371353373825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143706550920515961102654133 13472489148798371353373825)
      ·
        refine ⟨10104366861598778515030369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13472489148798371353373825 10104366861598778515030369)
        ·
          refine ⟨7578275146199083886272777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10104366861598778515030369 7578275146199083886272777)
          ·
            refine ⟨5683706359649312914704583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7578275146199083886272777 5683706359649312914704583)
            ·
              refine ⟨8525559539473969372056875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683706359649312914704583 8525559539473969372056875)
              ·
                refine ⟨12788339309210954058085313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525559539473969372056875 12788339309210954058085313)
                ·
                  refine ⟨9591254481908215543563985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12788339309210954058085313 9591254481908215543563985)
                  ·
                    refine ⟨7193440861431161657672989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9591254481908215543563985 7193440861431161657672989)
                    ·
                      refine ⟨2697540323036685621627371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7193440861431161657672989 2697540323036685621627371)
                      ·
                        rfl

theorem cell23_5253441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5253441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253441 prefixEnd_5253441 := by exact prefixLift 5253441
  have htrace : WordTrace (prefixWord ++ tailWord_5253441) baseStart_5253441 baseEnd_5253441 := by
    simpa [prefixWord, tailWord_5253441, baseEnd_5253441] using wordTrace_append hprefix tailTrace_5253441
  have hstable : (prefixWord ++ tailWord_5253441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253441).length < 2 ^ (prefixWord ++ tailWord_5253441).sum := by decide
  have hdescent : baseEnd_5253441 < baseStart_5253441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253447 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_5253447 : Nat := 118140960795 + 5253447 * 2 ^ 59
def prefixEnd_5253447 : Nat := 4983230072969 + 3 ^ 40 * 5253447 * 2
def baseEnd_5253447 : Nat := 2697543403920612598152343

theorem tailTrace_5253447 : CollatzResearch.WordTrace tailWord_5253447 prefixEnd_5253447 2697543403920612598152343 := by
  unfold tailWord_5253447
  simp only [CollatzResearch.WordTrace]
  refine ⟨191608953398666211161590595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127739302265777474107727063 191608953398666211161590595)
  ·
    refine ⟨287413430097999316742385893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191608953398666211161590595 287413430097999316742385893)
    ·
      refine ⟨53890018143374871889197355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287413430097999316742385893 53890018143374871889197355)
      ·
        refine ⟨80835027215062307833796033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53890018143374871889197355 80835027215062307833796033)
        ·
          refine ⟨60626270411296730875347025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80835027215062307833796033 60626270411296730875347025)
          ·
            refine ⟨45469702808472548156510269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60626270411296730875347025 45469702808472548156510269)
            ·
              refine ⟨17051138553177205558691351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45469702808472548156510269 17051138553177205558691351)
              ·
                refine ⟨25576707829765808338037027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17051138553177205558691351 25576707829765808338037027)
                ·
                  refine ⟨38365061744648712507055541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25576707829765808338037027 38365061744648712507055541)
                  ·
                    refine ⟨3596724538560816797536457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38365061744648712507055541 3596724538560816797536457)
                    ·
                      refine ⟨2697543403920612598152343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596724538560816797536457 2697543403920612598152343)
                      ·
                        rfl

theorem cell23_5253447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_5253447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253447 prefixEnd_5253447 := by exact prefixLift 5253447
  have htrace : WordTrace (prefixWord ++ tailWord_5253447) baseStart_5253447 baseEnd_5253447 := by
    simpa [prefixWord, tailWord_5253447, baseEnd_5253447] using wordTrace_append hprefix tailTrace_5253447
  have hstable : (prefixWord ++ tailWord_5253447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253447).length < 2 ^ (prefixWord ++ tailWord_5253447).sum := by decide
  have hdescent : baseEnd_5253447 < baseStart_5253447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253457 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 1, 5]
def baseStart_5253457 : Nat := 118140960795 + 5253457 * 2 ^ 59
def prefixEnd_5253457 : Nat := 4983230072969 + 3 ^ 40 * 5253457 * 2
def baseEnd_5253457 : Nat := 899182846242385853009099

theorem tailTrace_5253457 : CollatzResearch.WordTrace tailWord_5253457 prefixEnd_5253457 899182846242385853009099 := by
  unfold tailWord_5253457
  simp only [CollatzResearch.WordTrace]
  refine ⟨191609318128629982869454625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127739545419086655246303083 191609318128629982869454625)
  ·
    refine ⟨143706988596472487152090969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191609318128629982869454625 143706988596472487152090969)
    ·
      refine ⟨107780241447354365364068227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143706988596472487152090969 107780241447354365364068227)
      ·
        refine ⟨161670362171031548046102341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107780241447354365364068227 161670362171031548046102341)
        ·
          refine ⟨30313192907068415258644189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161670362171031548046102341 30313192907068415258644189)
          ·
            refine ⟨11367447340150655721991571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30313192907068415258644189 11367447340150655721991571)
            ·
              refine ⟨17051171010225983582987357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367447340150655721991571 17051171010225983582987357)
              ·
                refine ⟨6394189128834743843620259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17051171010225983582987357 6394189128834743843620259)
                ·
                  refine ⟨9591283693252115765430389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6394189128834743843620259 9591283693252115765430389)
                  ·
                    refine ⟨899182846242385853009099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9591283693252115765430389 899182846242385853009099)
                    ·
                      rfl

theorem cell23_5253457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_5253457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253457 prefixEnd_5253457 := by exact prefixLift 5253457
  have htrace : WordTrace (prefixWord ++ tailWord_5253457) baseStart_5253457 baseEnd_5253457 := by
    simpa [prefixWord, tailWord_5253457, baseEnd_5253457] using wordTrace_append hprefix tailTrace_5253457
  have hstable : (prefixWord ++ tailWord_5253457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253457).length < 2 ^ (prefixWord ++ tailWord_5253457).sum := by decide
  have hdescent : baseEnd_5253457 < baseStart_5253457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253528 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5253528 : Nat := 118140960795 + 5253528 * 2 ^ 59
def prefixEnd_5253528 : Nat := 4983230072969 + 3 ^ 40 * 5253528 * 2
def baseEnd_5253528 : Nat := 2697584995853626781239471

theorem tailTrace_5253528 : CollatzResearch.WordTrace tailWord_5253528 prefixEnd_5253528 2697584995853626781239471 := by
  unfold tailWord_5253528
  simp only [CollatzResearch.WordTrace]
  refine ⟨95805953855686380997644619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127741271807581841330192825 95805953855686380997644619)
  ·
    refine ⟨143708930783529571496466929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95805953855686380997644619 143708930783529571496466929)
    ·
      refine ⟨107781698087647178622350197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143708930783529571496466929 107781698087647178622350197)
      ·
        refine ⟨10104534195716922995845331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107781698087647178622350197 10104534195716922995845331)
        ·
          refine ⟨15156801293575384493767997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10104534195716922995845331 15156801293575384493767997)
          ·
            refine ⟨5683800485090769185162999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15156801293575384493767997 5683800485090769185162999)
            ·
              refine ⟨8525700727636153777744499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683800485090769185162999 8525700727636153777744499)
              ·
                refine ⟨12788551091454230666616749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525700727636153777744499 12788551091454230666616749)
                ·
                  refine ⟨4795706659295336499981281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12788551091454230666616749 4795706659295336499981281)
                  ·
                    refine ⟨3596779994471502374985961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4795706659295336499981281 3596779994471502374985961)
                    ·
                      refine ⟨2697584995853626781239471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596779994471502374985961 2697584995853626781239471)
                      ·
                        rfl

theorem cell23_5253528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5253528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253528 prefixEnd_5253528 := by exact prefixLift 5253528
  have htrace : WordTrace (prefixWord ++ tailWord_5253528) baseStart_5253528 baseEnd_5253528 := by
    simpa [prefixWord, tailWord_5253528, baseEnd_5253528] using wordTrace_append hprefix tailTrace_5253528
  have hstable : (prefixWord ++ tailWord_5253528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253528).length < 2 ^ (prefixWord ++ tailWord_5253528).sum := by decide
  have hdescent : baseEnd_5253528 < baseStart_5253528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253534 : List Nat := [4, 3, 1, 2, 1, 2, 2, 8]
def baseStart_5253534 : Nat := 118140960795 + 5253534 * 2 ^ 59
def prefixEnd_5253534 : Nat := 4983230072969 + 3 ^ 40 * 5253534 * 2
def baseEnd_5253534 : Nat := 99910669508798287324609

theorem tailTrace_5253534 : CollatzResearch.WordTrace tailWord_5253534 prefixEnd_5253534 99910669508798287324609 := by
  unfold tailWord_5253534
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951515818668878127500957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127741417699567350013338437 23951515818668878127500957)
  ·
    refine ⟨8981818432000829297812859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23951515818668878127500957 8981818432000829297812859)
    ·
      refine ⟨13472727648001243946719289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981818432000829297812859 13472727648001243946719289)
      ·
        refine ⟨10104545736000932960039467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13472727648001243946719289 10104545736000932960039467)
        ·
          refine ⟨15156818604001399440059201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10104545736000932960039467 15156818604001399440059201)
          ·
            refine ⟨11367613953001049580044401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15156818604001399440059201 11367613953001049580044401)
            ·
              refine ⟨8525710464750787185033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11367613953001049580044401 8525710464750787185033301)
              ·
                refine ⟨99910669508798287324609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8525710464750787185033301 99910669508798287324609)
                ·
                  rfl

theorem cell23_5253534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_5253534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253534 prefixEnd_5253534 := by exact prefixLift 5253534
  have htrace : WordTrace (prefixWord ++ tailWord_5253534) baseStart_5253534 baseEnd_5253534 := by
    simpa [prefixWord, tailWord_5253534, baseEnd_5253534] using wordTrace_append hprefix tailTrace_5253534
  have hstable : (prefixWord ++ tailWord_5253534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253534).length < 2 ^ (prefixWord ++ tailWord_5253534).sum := by decide
  have hdescent : baseEnd_5253534 < baseStart_5253534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253554 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_5253554 : Nat := 118140960795 + 5253554 * 2 ^ 59
def prefixEnd_5253554 : Nat := 4983230072969 + 3 ^ 40 * 5253554 * 2
def baseEnd_5253554 : Nat := 2697598346350643679514351

theorem tailTrace_5253554 : CollatzResearch.WordTrace tailWord_5253554 prefixEnd_5253554 2697598346350643679514351 := by
  unfold tailWord_5253554
  simp only [CollatzResearch.WordTrace]
  refine ⟨47903214002319642108933929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127741904006185712290490477 47903214002319642108933929)
  ·
    refine ⟨35927410501739731581700447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47903214002319642108933929 35927410501739731581700447)
    ·
      refine ⟨53891115752609597372550671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35927410501739731581700447 53891115752609597372550671)
      ·
        refine ⟨80836673628914396058826007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53891115752609597372550671 80836673628914396058826007)
        ·
          refine ⟨121255010443371594088239011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80836673628914396058826007 121255010443371594088239011)
          ·
            refine ⟨181882515665057391132358517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121255010443371594088239011 181882515665057391132358517)
            ·
              refine ⟨17051485843599130418658611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181882515665057391132358517 17051485843599130418658611)
              ·
                refine ⟨25577228765398695627987917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17051485843599130418658611 25577228765398695627987917)
                ·
                  refine ⟨9591460787024510860495469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25577228765398695627987917 9591460787024510860495469)
                  ·
                    refine ⟨3596797795134191572685801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9591460787024510860495469 3596797795134191572685801)
                    ·
                      refine ⟨2697598346350643679514351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596797795134191572685801 2697598346350643679514351)
                      ·
                        rfl

theorem cell23_5253554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_5253554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253554 prefixEnd_5253554 := by exact prefixLift 5253554
  have htrace : WordTrace (prefixWord ++ tailWord_5253554) baseStart_5253554 baseEnd_5253554 := by
    simpa [prefixWord, tailWord_5253554, baseEnd_5253554] using wordTrace_append hprefix tailTrace_5253554
  have hstable : (prefixWord ++ tailWord_5253554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253554).length < 2 ^ (prefixWord ++ tailWord_5253554).sum := by decide
  have hdescent : baseEnd_5253554 < baseStart_5253554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253560 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_5253560 : Nat := 118140960795 + 5253560 * 2 ^ 59
def prefixEnd_5253560 : Nat := 4983230072969 + 3 ^ 40 * 5253560 * 2
def baseEnd_5253560 : Nat := 899200475744856885346441

theorem tailTrace_5253560 : CollatzResearch.WordTrace tailWord_5253560 prefixEnd_5253560 899200475744856885346441 := by
  unfold tailWord_5253560
  simp only [CollatzResearch.WordTrace]
  refine ⟨95806537423628415730227067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127742049898171220973636089 95806537423628415730227067)
  ·
    refine ⟨143709806135442623595340601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95806537423628415730227067 143709806135442623595340601)
    ·
      refine ⟨107782354601581967696505451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143709806135442623595340601 107782354601581967696505451)
      ·
        refine ⟨161673531902372951544758177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107782354601581967696505451 161673531902372951544758177)
        ·
          refine ⟨121255148926779713658568633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161673531902372951544758177 121255148926779713658568633)
          ·
            refine ⟨90941361695084785243926475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121255148926779713658568633 90941361695084785243926475)
            ·
              refine ⟨136412042542627177865889713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90941361695084785243926475 136412042542627177865889713)
              ·
                refine ⟨102309031906970383399417285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136412042542627177865889713 102309031906970383399417285)
                ·
                  refine ⟨19182943482556946887390741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102309031906970383399417285 19182943482556946887390741)
                  ·
                    refine ⟨899200475744856885346441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19182943482556946887390741 899200475744856885346441)
                    ·
                      rfl

theorem cell23_5253560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_5253560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253560 prefixEnd_5253560 := by exact prefixLift 5253560
  have htrace : WordTrace (prefixWord ++ tailWord_5253560) baseStart_5253560 baseEnd_5253560 := by
    simpa [prefixWord, tailWord_5253560, baseEnd_5253560] using wordTrace_append hprefix tailTrace_5253560
  have hstable : (prefixWord ++ tailWord_5253560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253560).length < 2 ^ (prefixWord ++ tailWord_5253560).sum := by decide
  have hdescent : baseEnd_5253560 < baseStart_5253560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253601 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_5253601 : Nat := 118140960795 + 5253601 * 2 ^ 59
def prefixEnd_5253601 : Nat := 4983230072969 + 3 ^ 40 * 5253601 * 2
def baseEnd_5253601 : Nat := 2697622479941404995626635

theorem tailTrace_5253601 : CollatzResearch.WordTrace tailWord_5253601 prefixEnd_5253601 2697622479941404995626635 := by
  unfold tailWord_5253601
  simp only [CollatzResearch.WordTrace]
  refine ⟨191614570240108295462696657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127743046826738863641797771 191614570240108295462696657)
  ·
    refine ⟨143710927680081221597022493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191614570240108295462696657 143710927680081221597022493)
    ·
      refine ⟨53891597880030458098883435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143710927680081221597022493 53891597880030458098883435)
      ·
        refine ⟨80837396820045687148325153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53891597880030458098883435 80837396820045687148325153)
        ·
          refine ⟨60628047615034265361243865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80837396820045687148325153 60628047615034265361243865)
          ·
            refine ⟨45471035711275699020932899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60628047615034265361243865 45471035711275699020932899)
            ·
              refine ⟨68206553566913548531399349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45471035711275699020932899 68206553566913548531399349)
              ·
                refine ⟨6394364396898145174818689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68206553566913548531399349 6394364396898145174818689)
                ·
                  refine ⟨4795773297673608881114017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394364396898145174818689 4795773297673608881114017)
                  ·
                    refine ⟨3596829973255206660835513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4795773297673608881114017 3596829973255206660835513)
                    ·
                      refine ⟨2697622479941404995626635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596829973255206660835513 2697622479941404995626635)
                      ·
                        rfl

theorem cell23_5253601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_5253601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253601 prefixEnd_5253601 := by exact prefixLift 5253601
  have htrace : WordTrace (prefixWord ++ tailWord_5253601) baseStart_5253601 baseEnd_5253601 := by
    simpa [prefixWord, tailWord_5253601, baseEnd_5253601] using wordTrace_append hprefix tailTrace_5253601
  have hstable : (prefixWord ++ tailWord_5253601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253601).length < 2 ^ (prefixWord ++ tailWord_5253601).sum := by decide
  have hdescent : baseEnd_5253601 < baseStart_5253601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253607 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 7]
def baseStart_5253607 : Nat := 118140960795 + 5253607 * 2 ^ 59
def prefixEnd_5253607 : Nat := 4983230072969 + 3 ^ 40 * 5253607 * 2
def baseEnd_5253607 : Nat := 299736173425036885794623

theorem tailTrace_5253607 : CollatzResearch.WordTrace tailWord_5253607 prefixEnd_5253607 299736173425036885794623 := by
  unfold tailWord_5253607
  simp only [CollatzResearch.WordTrace]
  refine ⟨191614789078086558487415075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127743192718724372324943383 191614789078086558487415075)
  ·
    refine ⟨287422183617129837731122613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191614789078086558487415075 287422183617129837731122613)
    ·
      refine ⟨26945829714105922287292745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 287422183617129837731122613 26945829714105922287292745)
      ·
        refine ⟨20209372285579441715469559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26945829714105922287292745 20209372285579441715469559)
        ·
          refine ⟨30314058428369162573204339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20209372285579441715469559 30314058428369162573204339)
          ·
            refine ⟨45471087642553743859806509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30314058428369162573204339 45471087642553743859806509)
            ·
              refine ⟨17051657865957653947427441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45471087642553743859806509 17051657865957653947427441)
              ·
                refine ⟨12788743399468240460570581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17051657865957653947427441 12788743399468240460570581)
                ·
                  refine ⟨299736173425036885794623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12788743399468240460570581 299736173425036885794623)
                  ·
                    rfl

theorem cell23_5253607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 7].length) (baseStart_5253607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253607 prefixEnd_5253607 := by exact prefixLift 5253607
  have htrace : WordTrace (prefixWord ++ tailWord_5253607) baseStart_5253607 baseEnd_5253607 := by
    simpa [prefixWord, tailWord_5253607, baseEnd_5253607] using wordTrace_append hprefix tailTrace_5253607
  have hstable : (prefixWord ++ tailWord_5253607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253607).length < 2 ^ (prefixWord ++ tailWord_5253607).sum := by decide
  have hdescent : baseEnd_5253607 < baseStart_5253607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253617 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_5253617 : Nat := 118140960795 + 5253617 * 2 ^ 59
def prefixEnd_5253617 : Nat := 4983230072969 + 3 ^ 40 * 5253617 * 2
def baseEnd_5253617 : Nat := 2697630695631876933026561

theorem tailTrace_5253617 : CollatzResearch.WordTrace tailWord_5253617 prefixEnd_5253617 2697630695631876933026561 := by
  unfold tailWord_5253617
  simp only [CollatzResearch.WordTrace]
  refine ⟨191615153808050330195279105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127743435872033553463519403 191615153808050330195279105)
  ·
    refine ⟨143711365356037747646459329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191615153808050330195279105 143711365356037747646459329)
    ·
      refine ⟨107783524017028310734844497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143711365356037747646459329 107783524017028310734844497)
      ·
        refine ⟨80837643012771233051133373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107783524017028310734844497 80837643012771233051133373)
        ·
          refine ⟨30314116129789212394175015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80837643012771233051133373 30314116129789212394175015)
          ·
            refine ⟨45471174194683818591262523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30314116129789212394175015 45471174194683818591262523)
            ·
              refine ⟨68206761292025727886893785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45471174194683818591262523 68206761292025727886893785)
              ·
                refine ⟨51155070969019295915170339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68206761292025727886893785 51155070969019295915170339)
                ·
                  refine ⟨76732606453528943872755509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51155070969019295915170339 76732606453528943872755509)
                  ·
                    refine ⟨7193681855018338488070829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76732606453528943872755509 7193681855018338488070829)
                    ·
                      refine ⟨2697630695631876933026561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7193681855018338488070829 2697630695631876933026561)
                      ·
                        rfl

theorem cell23_5253617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_5253617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253617 prefixEnd_5253617 := by exact prefixLift 5253617
  have htrace : WordTrace (prefixWord ++ tailWord_5253617) baseStart_5253617 baseEnd_5253617 := by
    simpa [prefixWord, tailWord_5253617, baseEnd_5253617] using wordTrace_append hprefix tailTrace_5253617
  have hstable : (prefixWord ++ tailWord_5253617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253617).length < 2 ^ (prefixWord ++ tailWord_5253617).sum := by decide
  have hdescent : baseEnd_5253617 < baseStart_5253617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253624 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 5]
def baseStart_5253624 : Nat := 118140960795 + 5253624 * 2 ^ 59
def prefixEnd_5253624 : Nat := 4983230072969 + 3 ^ 40 * 5253624 * 2
def baseEnd_5253624 : Nat := 299737143332939822848781

theorem tailTrace_5253624 : CollatzResearch.WordTrace tailWord_5253624 prefixEnd_5253624 299737143332939822848781 := by
  unfold tailWord_5253624
  simp only [CollatzResearch.WordTrace]
  refine ⟨95807704559512485195391963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127743606079349980260522617 95807704559512485195391963)
  ·
    refine ⟨143711556839268727793087945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95807704559512485195391963 143711556839268727793087945)
    ·
      refine ⟨107783667629451545844815959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143711556839268727793087945 107783667629451545844815959)
      ·
        refine ⟨161675501444177318767223939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107783667629451545844815959 161675501444177318767223939)
        ·
          refine ⟨242513252166265978150835909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161675501444177318767223939 242513252166265978150835909)
          ·
            refine ⟨45471234781174870903281733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242513252166265978150835909 45471234781174870903281733)
            ·
              refine ⟨8525856521470288294365325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45471234781174870903281733 8525856521470288294365325)
              ·
                refine ⟨3197196195551358110386997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8525856521470288294365325 3197196195551358110386997)
                ·
                  refine ⟨299737143332939822848781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3197196195551358110386997 299737143332939822848781)
                  ·
                    rfl

theorem cell23_5253624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 5].length) (baseStart_5253624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253624 prefixEnd_5253624 := by exact prefixLift 5253624
  have htrace : WordTrace (prefixWord ++ tailWord_5253624) baseStart_5253624 baseEnd_5253624 := by
    simpa [prefixWord, tailWord_5253624, baseEnd_5253624] using wordTrace_append hprefix tailTrace_5253624
  have hstable : (prefixWord ++ tailWord_5253624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253624).length < 2 ^ (prefixWord ++ tailWord_5253624).sum := by decide
  have hdescent : baseEnd_5253624 < baseStart_5253624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253637 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_5253637 : Nat := 118140960795 + 5253637 * 2 ^ 59
def prefixEnd_5253637 : Nat := 4983230072969 + 3 ^ 40 * 5253637 * 2
def baseEnd_5253637 : Nat := 899213655081655618258823

theorem tailTrace_5253637 : CollatzResearch.WordTrace tailWord_5253637 prefixEnd_5253637 899213655081655618258823 := by
  unfold tailWord_5253637
  simp only [CollatzResearch.WordTrace]
  refine ⟨191615883267977873611007165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127743922178651915740671443 191615883267977873611007165)
  ·
    refine ⟨71855956225491702604127687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191615883267977873611007165 71855956225491702604127687)
    ·
      refine ⟨107783934338237553906191531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71855956225491702604127687 107783934338237553906191531)
      ·
        refine ⟨161675901507356330859287297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107783934338237553906191531 161675901507356330859287297)
        ·
          refine ⟨121256926130517248144465473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161675901507356330859287297 121256926130517248144465473)
          ·
            refine ⟨90942694597887936108349105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121256926130517248144465473 90942694597887936108349105)
            ·
              refine ⟨68207020948415952081261829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90942694597887936108349105 68207020948415952081261829)
              ·
                refine ⟨12788816427827991015236593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68207020948415952081261829 12788816427827991015236593)
                ·
                  refine ⟨9591612320870993261427445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12788816427827991015236593 9591612320870993261427445)
                  ·
                    refine ⟨899213655081655618258823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9591612320870993261427445 899213655081655618258823)
                    ·
                      rfl

theorem cell23_5253637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_5253637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253637 prefixEnd_5253637 := by exact prefixLift 5253637
  have htrace : WordTrace (prefixWord ++ tailWord_5253637) baseStart_5253637 baseEnd_5253637 := by
    simpa [prefixWord, tailWord_5253637, baseEnd_5253637] using wordTrace_append hprefix tailTrace_5253637
  have hstable : (prefixWord ++ tailWord_5253637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253637).length < 2 ^ (prefixWord ++ tailWord_5253637).sum := by decide
  have hdescent : baseEnd_5253637 < baseStart_5253637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253652 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5253652 : Nat := 118140960795 + 5253652 * 2 ^ 59
def prefixEnd_5253652 : Nat := 4983230072969 + 3 ^ 40 * 5253652 * 2
def baseEnd_5253652 : Nat := 2697648667454784296088901

theorem tailTrace_5253652 : CollatzResearch.WordTrace tailWord_5253652 prefixEnd_5253652 2697648667454784296088901 := by
  unfold tailWord_5253652
  simp only [CollatzResearch.WordTrace]
  refine ⟨95808215181461765586401605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127744286908615687448535473 95808215181461765586401605)
  ·
    refine ⟨17964040346524081047450301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95808215181461765586401605 17964040346524081047450301)
    ·
      refine ⟨6736515129946530392793863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17964040346524081047450301 6736515129946530392793863)
      ·
        refine ⟨10104772694919795589190795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736515129946530392793863 10104772694919795589190795)
        ·
          refine ⟨15157159042379693383786193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10104772694919795589190795 15157159042379693383786193)
          ·
            refine ⟨11367869281784770037839645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15157159042379693383786193 11367869281784770037839645)
            ·
              refine ⟨4262950980669288764189867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11367869281784770037839645 4262950980669288764189867)
              ·
                refine ⟨6394426471003933146284801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262950980669288764189867 6394426471003933146284801)
                ·
                  refine ⟨4795819853252949859713601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394426471003933146284801 4795819853252949859713601)
                  ·
                    refine ⟨3596864889939712394785201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4795819853252949859713601 3596864889939712394785201)
                    ·
                      refine ⟨2697648667454784296088901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596864889939712394785201 2697648667454784296088901)
                      ·
                        rfl

theorem cell23_5253652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5253652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253652 prefixEnd_5253652 := by exact prefixLift 5253652
  have htrace : WordTrace (prefixWord ++ tailWord_5253652) baseStart_5253652 baseEnd_5253652 := by
    simpa [prefixWord, tailWord_5253652, baseEnd_5253652] using wordTrace_append hprefix tailTrace_5253652
  have hstable : (prefixWord ++ tailWord_5253652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253652).length < 2 ^ (prefixWord ++ tailWord_5253652).sum := by decide
  have hdescent : baseEnd_5253652 < baseStart_5253652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253657 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_5253657 : Nat := 118140960795 + 5253657 * 2 ^ 59
def prefixEnd_5253657 : Nat := 4983230072969 + 3 ^ 40 * 5253657 * 2
def baseEnd_5253657 : Nat := 2697651234858056776526377

theorem tailTrace_5253657 : CollatzResearch.WordTrace tailWord_5253657 prefixEnd_5253657 2697651234858056776526377 := by
  unfold tailWord_5253657
  simp only [CollatzResearch.WordTrace]
  refine ⟨191616612727905417026735225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127744408485270278017823483 191616612727905417026735225)
  ·
    refine ⟨143712459545929062770051419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191616612727905417026735225 143712459545929062770051419)
    ·
      refine ⟨215568689318893594155077129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143712459545929062770051419 215568689318893594155077129)
      ·
        refine ⟨161676516989170195616307847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215568689318893594155077129 161676516989170195616307847)
        ·
          refine ⟨242514775483755293424461771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161676516989170195616307847 242514775483755293424461771)
          ·
            refine ⟨363772163225632940136692657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242514775483755293424461771 363772163225632940136692657)
            ·
              refine ⟨272829122419224705102519493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363772163225632940136692657 272829122419224705102519493)
              ·
                refine ⟨51155460453604632206722405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272829122419224705102519493 51155460453604632206722405)
                ·
                  refine ⟨9591648835050868538760451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51155460453604632206722405 9591648835050868538760451)
                  ·
                    refine ⟨14387473252576302808140677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9591648835050868538760451 14387473252576302808140677)
                    ·
                      refine ⟨2697651234858056776526377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14387473252576302808140677 2697651234858056776526377)
                      ·
                        rfl

theorem cell23_5253657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_5253657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253657 prefixEnd_5253657 := by exact prefixLift 5253657
  have htrace : WordTrace (prefixWord ++ tailWord_5253657) baseStart_5253657 baseEnd_5253657 := by
    simpa [prefixWord, tailWord_5253657, baseEnd_5253657] using wordTrace_append hprefix tailTrace_5253657
  have hstable : (prefixWord ++ tailWord_5253657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253657).length < 2 ^ (prefixWord ++ tailWord_5253657).sum := by decide
  have hdescent : baseEnd_5253657 < baseStart_5253657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253674 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5253674 : Nat := 118140960795 + 5253674 * 2 ^ 59
def prefixEnd_5253674 : Nat := 4983230072969 + 3 ^ 40 * 5253674 * 2
def baseEnd_5253674 : Nat := 2697659964029183210013799

theorem tailTrace_5253674 : CollatzResearch.WordTrace tailWord_5253674 prefixEnd_5253674 2697659964029183210013799 := by
  unfold tailWord_5253674
  simp only [CollatzResearch.WordTrace]
  refine ⟨47904308192210957232526019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127744821845895885953402717 47904308192210957232526019)
  ·
    refine ⟨71856462288316435848789029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47904308192210957232526019 71856462288316435848789029)
    ·
      refine ⟨13473086679059331721647943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71856462288316435848789029 13473086679059331721647943)
      ·
        refine ⟨20209630018588997582471915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13473086679059331721647943 20209630018588997582471915)
        ·
          refine ⟨30314445027883496373707873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20209630018588997582471915 30314445027883496373707873)
          ·
            refine ⟨22735833770912622280280905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30314445027883496373707873 22735833770912622280280905)
            ·
              refine ⟨17051875328184466710210679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22735833770912622280280905 17051875328184466710210679)
              ·
                refine ⟨25577812992276700065316019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17051875328184466710210679 25577812992276700065316019)
                ·
                  refine ⟨38366719488415050097974029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25577812992276700065316019 38366719488415050097974029)
                  ·
                    refine ⟨14387519808155643786740261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38366719488415050097974029 14387519808155643786740261)
                    ·
                      refine ⟨2697659964029183210013799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14387519808155643786740261 2697659964029183210013799)
                      ·
                        rfl

theorem cell23_5253674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5253674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253674 prefixEnd_5253674 := by exact prefixLift 5253674
  have htrace : WordTrace (prefixWord ++ tailWord_5253674) baseStart_5253674 baseEnd_5253674 := by
    simpa [prefixWord, tailWord_5253674, baseEnd_5253674] using wordTrace_append hprefix tailTrace_5253674
  have hstable : (prefixWord ++ tailWord_5253674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253674).length < 2 ^ (prefixWord ++ tailWord_5253674).sum := by decide
  have hdescent : baseEnd_5253674 < baseStart_5253674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253701 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_5253701 : Nat := 118140960795 + 5253701 * 2 ^ 59
def prefixEnd_5253701 : Nat := 4983230072969 + 3 ^ 40 * 5253701 * 2
def baseEnd_5253701 : Nat := 899224609335618201458725

theorem tailTrace_5253701 : CollatzResearch.WordTrace tailWord_5253701 prefixEnd_5253701 899224609335618201458725 := by
  unfold tailWord_5253701
  simp only [CollatzResearch.WordTrace]
  refine ⟨191618217539746012541336957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127745478359830675027557971 191618217539746012541336957)
  ·
    refine ⟨71856831577404754703001359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191618217539746012541336957 71856831577404754703001359)
    ·
      refine ⟨107785247366107132054502039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71856831577404754703001359 107785247366107132054502039)
      ·
        refine ⟨161677871049160698081753059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107785247366107132054502039 161677871049160698081753059)
        ·
          refine ⟨242516806573741047122629589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161677871049160698081753059 242516806573741047122629589)
          ·
            refine ⟨5683987654072055791936631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 242516806573741047122629589 5683987654072055791936631)
            ·
              refine ⟨8525981481108083687904947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683987654072055791936631 8525981481108083687904947)
              ·
                refine ⟨12788972221662125531857421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525981481108083687904947 12788972221662125531857421)
                ·
                  refine ⟨4795864583123297074446533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12788972221662125531857421 4795864583123297074446533)
                  ·
                    refine ⟨899224609335618201458725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795864583123297074446533 899224609335618201458725)
                    ·
                      rfl

theorem cell23_5253701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_5253701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253701 prefixEnd_5253701 := by exact prefixLift 5253701
  have htrace : WordTrace (prefixWord ++ tailWord_5253701) baseStart_5253701 baseEnd_5253701 := by
    simpa [prefixWord, tailWord_5253701, baseEnd_5253701] using wordTrace_append hprefix tailTrace_5253701
  have hstable : (prefixWord ++ tailWord_5253701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253701).length < 2 ^ (prefixWord ++ tailWord_5253701).sum := by decide
  have hdescent : baseEnd_5253701 < baseStart_5253701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253714 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_5253714 : Nat := 118140960795 + 5253714 * 2 ^ 59
def prefixEnd_5253714 : Nat := 4983230072969 + 3 ^ 40 * 5253714 * 2
def baseEnd_5253714 : Nat := 299742278139484783723735

theorem tailTrace_5253714 : CollatzResearch.WordTrace tailWord_5253714 prefixEnd_5253714 299742278139484783723735 := by
  unfold tailWord_5253714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47904672922174728940390049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127745794459132610507706797 47904672922174728940390049)
  ·
    refine ⟨35928504691631046705292537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47904672922174728940390049 35928504691631046705292537)
    ·
      refine ⟨26946378518723285028969403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35928504691631046705292537 26946378518723285028969403)
      ·
        refine ⟨40419567778084927543454105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26946378518723285028969403 40419567778084927543454105)
        ·
          refine ⟨30314675833563695657590579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40419567778084927543454105 30314675833563695657590579)
          ·
            refine ⟨45472013750345543486385869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30314675833563695657590579 45472013750345543486385869)
            ·
              refine ⟨17052005156379578807394701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45472013750345543486385869 17052005156379578807394701)
              ·
                refine ⟨6394501933642342052773013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17052005156379578807394701 6394501933642342052773013)
                ·
                  refine ⟨299742278139484783723735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6394501933642342052773013 299742278139484783723735)
                  ·
                    rfl

theorem cell23_5253714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_5253714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253714 prefixEnd_5253714 := by exact prefixLift 5253714
  have htrace : WordTrace (prefixWord ++ tailWord_5253714) baseStart_5253714 baseEnd_5253714 := by
    simpa [prefixWord, tailWord_5253714, baseEnd_5253714] using wordTrace_append hprefix tailTrace_5253714
  have hstable : (prefixWord ++ tailWord_5253714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253714).length < 2 ^ (prefixWord ++ tailWord_5253714).sum := by decide
  have hdescent : baseEnd_5253714 < baseStart_5253714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253717 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5253717 : Nat := 118140960795 + 5253717 * 2 ^ 59
def prefixEnd_5253717 : Nat := 4983230072969 + 3 ^ 40 * 5253717 * 2
def baseEnd_5253717 : Nat := 2697682043697326541776101

theorem tailTrace_5253717 : CollatzResearch.WordTrace tailWord_5253717 prefixEnd_5253717 2697682043697326541776101 := by
  unfold tailWord_5253717
  simp only [CollatzResearch.WordTrace]
  refine ⟨191618801107688047273919405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127745867405125364849279603 191618801107688047273919405)
  ·
    refine ⟨71857050415383017727719777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191618801107688047273919405 71857050415383017727719777)
    ·
      refine ⟨53892787811537263295789833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71857050415383017727719777 53892787811537263295789833)
      ·
        refine ⟨40419590858652947471842375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53892787811537263295789833 40419590858652947471842375)
        ·
          refine ⟨60629386287979421207763563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40419590858652947471842375 60629386287979421207763563)
          ·
            refine ⟨90944079431969131811645345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60629386287979421207763563 90944079431969131811645345)
            ·
              refine ⟨68208059573976848858734009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90944079431969131811645345 68208059573976848858734009)
              ·
                refine ⟨51156044680482636644050507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68208059573976848858734009 51156044680482636644050507)
                ·
                  refine ⟨76734067020723954966075761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51156044680482636644050507 76734067020723954966075761)
                  ·
                    refine ⟨57550550265542966224556821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76734067020723954966075761 57550550265542966224556821)
                    ·
                      refine ⟨2697682043697326541776101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57550550265542966224556821 2697682043697326541776101)
                      ·
                        rfl

theorem cell23_5253717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5253717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253717 prefixEnd_5253717 := by exact prefixLift 5253717
  have htrace : WordTrace (prefixWord ++ tailWord_5253717) baseStart_5253717 baseEnd_5253717 := by
    simpa [prefixWord, tailWord_5253717, baseEnd_5253717] using wordTrace_append hprefix tailTrace_5253717
  have hstable : (prefixWord ++ tailWord_5253717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253717).length < 2 ^ (prefixWord ++ tailWord_5253717).sum := by decide
  have hdescent : baseEnd_5253717 < baseStart_5253717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253751 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 2, 3, 2]
def baseStart_5253751 : Nat := 118140960795 + 5253751 * 2 ^ 59
def prefixEnd_5253751 : Nat := 4983230072969 + 3 ^ 40 * 5253751 * 2
def baseEnd_5253751 : Nat := 2697699502039579408750945

theorem tailTrace_5253751 : CollatzResearch.WordTrace tailWord_5253751 prefixEnd_5253751 2697699502039579408750945 := by
  unfold tailWord_5253751
  simp only [CollatzResearch.WordTrace]
  refine ⟨191620041189564871080657107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127746694126376580720438071 191620041189564871080657107)
  ·
    refine ⟨287430061784347306620985661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191620041189564871080657107 287430061784347306620985661)
    ·
      refine ⟨107786273169130239982869623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287430061784347306620985661 107786273169130239982869623)
      ·
        refine ⟨161679409753695359974304435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107786273169130239982869623 161679409753695359974304435)
        ·
          refine ⟨242519114630543039961456653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161679409753695359974304435 242519114630543039961456653)
          ·
            refine ⟨90944667986453639985546245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242519114630543039961456653 90944667986453639985546245)
            ·
              refine ⟨17052125247460057497289921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90944667986453639985546245 17052125247460057497289921)
              ·
                refine ⟨12789093935595043122967441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17052125247460057497289921 12789093935595043122967441)
                ·
                  refine ⟨9591820451696282342225581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12789093935595043122967441 9591820451696282342225581)
                  ·
                    refine ⟨3596932669386105878334593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9591820451696282342225581 3596932669386105878334593)
                    ·
                      refine ⟨2697699502039579408750945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596932669386105878334593 2697699502039579408750945)
                      ·
                        rfl

theorem cell23_5253751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_5253751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253751 prefixEnd_5253751 := by exact prefixLift 5253751
  have htrace : WordTrace (prefixWord ++ tailWord_5253751) baseStart_5253751 baseEnd_5253751 := by
    simpa [prefixWord, tailWord_5253751, baseEnd_5253751] using wordTrace_append hprefix tailTrace_5253751
  have hstable : (prefixWord ++ tailWord_5253751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253751).length < 2 ^ (prefixWord ++ tailWord_5253751).sum := by decide
  have hdescent : baseEnd_5253751 < baseStart_5253751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253777 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_5253777 : Nat := 118140960795 + 5253777 * 2 ^ 59
def prefixEnd_5253777 : Nat := 4983230072969 + 3 ^ 40 * 5253777 * 2
def baseEnd_5253777 : Nat := 2697712852536596307025825

theorem tailTrace_5253777 : CollatzResearch.WordTrace tailWord_5253777 prefixEnd_5253777 2697712852536596307025825 := by
  unfold tailWord_5253777
  simp only [CollatzResearch.WordTrace]
  refine ⟨191620989487470677521103585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127747326324980451680735723 191620989487470677521103585)
  ·
    refine ⟨143715742115603008140827689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191620989487470677521103585 143715742115603008140827689)
    ·
      refine ⟨107786806586702256105620767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143715742115603008140827689 107786806586702256105620767)
      ·
        refine ⟨161680209880053384158431151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107786806586702256105620767 161680209880053384158431151)
        ·
          refine ⟨242520314820080076237646727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161680209880053384158431151 242520314820080076237646727)
          ·
            refine ⟨363780472230120114356470091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242520314820080076237646727 363780472230120114356470091)
            ·
              refine ⟨545670708345180171534705137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363780472230120114356470091 545670708345180171534705137)
              ·
                refine ⟨409253031258885128651028853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545670708345180171534705137 409253031258885128651028853)
                ·
                  refine ⟨38367471680520480811033955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 409253031258885128651028853 38367471680520480811033955)
                  ·
                    refine ⟨57551207520780721216550933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38367471680520480811033955 57551207520780721216550933)
                    ·
                      refine ⟨2697712852536596307025825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57551207520780721216550933 2697712852536596307025825)
                      ·
                        rfl

theorem cell23_5253777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_5253777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253777 prefixEnd_5253777 := by exact prefixLift 5253777
  have htrace : WordTrace (prefixWord ++ tailWord_5253777) baseStart_5253777 baseEnd_5253777 := by
    simpa [prefixWord, tailWord_5253777, baseEnd_5253777] using wordTrace_append hprefix tailTrace_5253777
  have hstable : (prefixWord ++ tailWord_5253777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253777).length < 2 ^ (prefixWord ++ tailWord_5253777).sum := by decide
  have hdescent : baseEnd_5253777 < baseStart_5253777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253815 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 3, 2, 2]
def baseStart_5253815 : Nat := 118140960795 + 5253815 * 2 ^ 59
def prefixEnd_5253815 : Nat := 4983230072969 + 3 ^ 40 * 5253815 * 2
def baseEnd_5253815 : Nat := 2697732364801467158350651

theorem tailTrace_5253815 : CollatzResearch.WordTrace tailWord_5253815 prefixEnd_5253815 2697732364801467158350651 := by
  unfold tailWord_5253815
  simp only [CollatzResearch.WordTrace]
  refine ⟨191622375461333010010986899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127748250307555340007324599 191622375461333010010986899)
  ·
    refine ⟨287433563191999515016480349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191622375461333010010986899 287433563191999515016480349)
    ·
      refine ⟨107787586196999818131180131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287433563191999515016480349 107787586196999818131180131)
      ·
        refine ⟨161681379295499727196770197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107787586196999818131180131 161681379295499727196770197)
        ·
          refine ⟨7578814654476549712348603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161681379295499727196770197 7578814654476549712348603)
          ·
            refine ⟨11368221981714824568522905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578814654476549712348603 11368221981714824568522905)
            ·
              refine ⟨8526166486286118426392179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11368221981714824568522905 8526166486286118426392179)
              ·
                refine ⟨12789249729429177639588269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8526166486286118426392179 12789249729429177639588269)
                ·
                  refine ⟨4795968648535941614845601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12789249729429177639588269 4795968648535941614845601)
                  ·
                    refine ⟨3596976486401956211134201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4795968648535941614845601 3596976486401956211134201)
                    ·
                      refine ⟨2697732364801467158350651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3596976486401956211134201 2697732364801467158350651)
                      ·
                        rfl

theorem cell23_5253815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_5253815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253815 prefixEnd_5253815 := by exact prefixLift 5253815
  have htrace : WordTrace (prefixWord ++ tailWord_5253815) baseStart_5253815 baseEnd_5253815 := by
    simpa [prefixWord, tailWord_5253815, baseEnd_5253815] using wordTrace_append hprefix tailTrace_5253815
  have hstable : (prefixWord ++ tailWord_5253815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253815).length < 2 ^ (prefixWord ++ tailWord_5253815).sum := by decide
  have hdescent : baseEnd_5253815 < baseStart_5253815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253825 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5253825 : Nat := 118140960795 + 5253825 * 2 ^ 59
def prefixEnd_5253825 : Nat := 4983230072969 + 3 ^ 40 * 5253825 * 2
def baseEnd_5253825 : Nat := 899245833202670706408535

theorem tailTrace_5253825 : CollatzResearch.WordTrace tailWord_5253825 prefixEnd_5253825 899245833202670706408535 := by
  unfold tailWord_5253825
  simp only [CollatzResearch.WordTrace]
  refine ⟨191622740191296781718850929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127748493460864521145900619 191622740191296781718850929)
  ·
    refine ⟨143717055143472586289138197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191622740191296781718850929 143717055143472586289138197)
    ·
      refine ⟨6736736959850277482303353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 143717055143472586289138197 6736736959850277482303353)
      ·
        refine ⟨5052552719887708111727515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6736736959850277482303353 5052552719887708111727515)
        ·
          refine ⟨7578829079831562167591273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052552719887708111727515 7578829079831562167591273)
          ·
            refine ⟨5684121809873671625693455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7578829079831562167591273 5684121809873671625693455)
            ·
              refine ⟨8526182714810507438540183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684121809873671625693455 8526182714810507438540183)
              ·
                refine ⟨12789274072215761157810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8526182714810507438540183 12789274072215761157810275)
                ·
                  refine ⟨19183911108323641736715413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12789274072215761157810275 19183911108323641736715413)
                  ·
                    refine ⟨899245833202670706408535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19183911108323641736715413 899245833202670706408535)
                    ·
                      rfl

theorem cell23_5253825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5253825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253825 prefixEnd_5253825 := by exact prefixLift 5253825
  have htrace : WordTrace (prefixWord ++ tailWord_5253825) baseStart_5253825 baseEnd_5253825 := by
    simpa [prefixWord, tailWord_5253825, baseEnd_5253825] using wordTrace_append hprefix tailTrace_5253825
  have hstable : (prefixWord ++ tailWord_5253825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253825).length < 2 ^ (prefixWord ++ tailWord_5253825).sum := by decide
  have hdescent : baseEnd_5253825 < baseStart_5253825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253828 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_5253828 : Nat := 118140960795 + 5253828 * 2 ^ 59
def prefixEnd_5253828 : Nat := 4983230072969 + 3 ^ 40 * 5253828 * 2
def baseEnd_5253828 : Nat := 2697739040049975607488091

theorem tailTrace_5253828 : CollatzResearch.WordTrace tailWord_5253828 prefixEnd_5253828 2697739040049975607488091 := by
  unfold tailWord_5253828
  simp only [CollatzResearch.WordTrace]
  refine ⟨95811424805142956615605069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127748566406857275487473425 95811424805142956615605069)
  ·
    refine ⟨35929284301928608730851901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95811424805142956615605069 35929284301928608730851901)
    ·
      refine ⟨13473481613223228274069463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35929284301928608730851901 13473481613223228274069463)
      ·
        refine ⟨20210222419834842411104195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13473481613223228274069463 20210222419834842411104195)
        ·
          refine ⟨30315333629752263616656293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20210222419834842411104195 30315333629752263616656293)
          ·
            refine ⟨5684125055578549428123055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30315333629752263616656293 5684125055578549428123055)
            ·
              refine ⟨8526187583367824142184583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684125055578549428123055 8526187583367824142184583)
              ·
                refine ⟨12789281375051736213276875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8526187583367824142184583 12789281375051736213276875)
                ·
                  refine ⟨19183922062577604319915313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12789281375051736213276875 19183922062577604319915313)
                  ·
                    refine ⟨14387941546933203239936485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19183922062577604319915313 14387941546933203239936485)
                    ·
                      refine ⟨2697739040049975607488091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14387941546933203239936485 2697739040049975607488091)
                      ·
                        rfl

theorem cell23_5253828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_5253828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253828 prefixEnd_5253828 := by exact prefixLift 5253828
  have htrace : WordTrace (prefixWord ++ tailWord_5253828) baseStart_5253828 baseEnd_5253828 := by
    simpa [prefixWord, tailWord_5253828, baseEnd_5253828] using wordTrace_append hprefix tailTrace_5253828
  have hstable : (prefixWord ++ tailWord_5253828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253828).length < 2 ^ (prefixWord ++ tailWord_5253828).sum := by decide
  have hdescent : baseEnd_5253828 < baseStart_5253828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253876 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5253876 : Nat := 118140960795 + 5253876 * 2 ^ 59
def prefixEnd_5253876 : Nat := 4983230072969 + 3 ^ 40 * 5253876 * 2
def baseEnd_5253876 : Nat := 899254562373797139895957

theorem tailTrace_5253876 : CollatzResearch.WordTrace tailWord_5253876 prefixEnd_5253876 899254562373797139895957 := by
  unfold tailWord_5253876
  simp only [CollatzResearch.WordTrace]
  refine ⟨95812300157056008714478741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127749733542741344952638321 95812300157056008714478741)
  ·
    refine ⟨4491201569862000408491191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95812300157056008714478741 4491201569862000408491191)
    ·
      refine ⟨6736802354793000612736787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4491201569862000408491191 6736802354793000612736787)
      ·
        refine ⟨10105203532189500919105181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736802354793000612736787 10105203532189500919105181)
        ·
          refine ⟨3789451324571062844664443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10105203532189500919105181 3789451324571062844664443)
          ·
            refine ⟨5684176986856594266996665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789451324571062844664443 5684176986856594266996665)
            ·
              refine ⟨4263132740142445700247499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5684176986856594266996665 4263132740142445700247499)
              ·
                refine ⟨6394699110213668550371249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263132740142445700247499 6394699110213668550371249)
                ·
                  refine ⟨4796024332660251412778437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394699110213668550371249 4796024332660251412778437)
                  ·
                    refine ⟨899254562373797139895957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796024332660251412778437 899254562373797139895957)
                    ·
                      rfl

theorem cell23_5253876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5253876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253876 prefixEnd_5253876 := by exact prefixLift 5253876
  have htrace : WordTrace (prefixWord ++ tailWord_5253876) baseStart_5253876 baseEnd_5253876 := by
    simpa [prefixWord, tailWord_5253876, baseEnd_5253876] using wordTrace_append hprefix tailTrace_5253876
  have hstable : (prefixWord ++ tailWord_5253876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253876).length < 2 ^ (prefixWord ++ tailWord_5253876).sum := by decide
  have hdescent : baseEnd_5253876 < baseStart_5253876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253921 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_5253921 : Nat := 118140960795 + 5253921 * 2 ^ 59
def prefixEnd_5253921 : Nat := 4983230072969 + 3 ^ 40 * 5253921 * 2
def baseEnd_5253921 : Nat := 2697786793750843743625163

theorem tailTrace_5253921 : CollatzResearch.WordTrace tailWord_5253921 prefixEnd_5253921 2697786793750843743625163 := by
  unfold tailWord_5253921
  simp only [CollatzResearch.WordTrace]
  refine ⟨191626241598948990114345617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127750827732632660076230411 191626241598948990114345617)
  ·
    refine ⟨143719681199211742585759213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191626241598948990114345617 143719681199211742585759213)
    ·
      refine ⟨53894880449704403469659705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143719681199211742585759213 53894880449704403469659705)
      ·
        refine ⟨40421160337278302602244779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53894880449704403469659705 40421160337278302602244779)
        ·
          refine ⟨60631740505917453903367169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40421160337278302602244779 60631740505917453903367169)
          ·
            refine ⟨45473805379438090427525377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60631740505917453903367169 45473805379438090427525377)
            ·
              refine ⟨34105354034578567820644033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45473805379438090427525377 34105354034578567820644033)
              ·
                refine ⟨25579015525933925865483025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34105354034578567820644033 25579015525933925865483025)
                ·
                  refine ⟨19184261644450444399112269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25579015525933925865483025 19184261644450444399112269)
                  ·
                    refine ⟨7194098116668916649667101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19184261644450444399112269 7194098116668916649667101)
                    ·
                      refine ⟨2697786793750843743625163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194098116668916649667101 2697786793750843743625163)
                      ·
                        rfl

theorem cell23_5253921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_5253921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253921 prefixEnd_5253921 := by exact prefixLift 5253921
  have htrace : WordTrace (prefixWord ++ tailWord_5253921) baseStart_5253921 baseEnd_5253921 := by
    simpa [prefixWord, tailWord_5253921, baseEnd_5253921] using wordTrace_append hprefix tailTrace_5253921
  have hstable : (prefixWord ++ tailWord_5253921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253921).length < 2 ^ (prefixWord ++ tailWord_5253921).sum := by decide
  have hdescent : baseEnd_5253921 < baseStart_5253921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253922 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_5253922 : Nat := 118140960795 + 5253922 * 2 ^ 59
def prefixEnd_5253922 : Nat := 4983230072969 + 3 ^ 40 * 5253922 * 2
def baseEnd_5253922 : Nat := 2697787307231498239712659

theorem tailTrace_5253922 : CollatzResearch.WordTrace tailWord_5253922 prefixEnd_5253922 2697787307231498239712659 := by
  unfold tailWord_5253922
  simp only [CollatzResearch.WordTrace]
  refine ⟨47906569517986341821283005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127750852047963578190088013 47906569517986341821283005)
  ·
    refine ⟨17964963569244878182981127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47906569517986341821283005 17964963569244878182981127)
    ·
      refine ⟨26947445353867317274471691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17964963569244878182981127 26947445353867317274471691)
      ·
        refine ⟨40421168030800975911707537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26947445353867317274471691 40421168030800975911707537)
        ·
          refine ⟨30315876023100731933780653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40421168030800975911707537 30315876023100731933780653)
          ·
            refine ⟨11368453508662774475167745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30315876023100731933780653 11368453508662774475167745)
            ·
              refine ⟨8526340131497080856375809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11368453508662774475167745 8526340131497080856375809)
              ·
                refine ⟨6394755098622810642281857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526340131497080856375809 6394755098622810642281857)
                ·
                  refine ⟨4796066323967107981711393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394755098622810642281857 4796066323967107981711393)
                  ·
                    refine ⟨3597049742975330986283545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796066323967107981711393 3597049742975330986283545)
                    ·
                      refine ⟨2697787307231498239712659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597049742975330986283545 2697787307231498239712659)
                      ·
                        rfl

theorem cell23_5253922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_5253922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253922 prefixEnd_5253922 := by exact prefixLift 5253922
  have htrace : WordTrace (prefixWord ++ tailWord_5253922) baseStart_5253922 baseEnd_5253922 := by
    simpa [prefixWord, tailWord_5253922, baseEnd_5253922] using wordTrace_append hprefix tailTrace_5253922
  have hstable : (prefixWord ++ tailWord_5253922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253922).length < 2 ^ (prefixWord ++ tailWord_5253922).sum := by decide
  have hdescent : baseEnd_5253922 < baseStart_5253922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253928 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 5]
def baseStart_5253928 : Nat := 118140960795 + 5253928 * 2 ^ 59
def prefixEnd_5253928 : Nat := 4983230072969 + 3 ^ 40 * 5253928 * 2
def baseEnd_5253928 : Nat := 299754487568380579581959

theorem tailTrace_5253928 : CollatzResearch.WordTrace tailWord_5253928 prefixEnd_5253928 299754487568380579581959 := by
  unfold tailWord_5253928
  simp only [CollatzResearch.WordTrace]
  refine ⟨95813248454961815154925219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127750997939949086873233625 95813248454961815154925219)
  ·
    refine ⟨143719872682442722732387829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95813248454961815154925219 143719872682442722732387829)
    ·
      refine ⟨13473738063979005256161359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143719872682442722732387829 13473738063979005256161359)
      ·
        refine ⟨20210607095968507884242039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13473738063979005256161359 20210607095968507884242039)
        ·
          refine ⟨30315910643952761826363059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20210607095968507884242039 30315910643952761826363059)
          ·
            refine ⟨45473865965929142739544589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30315910643952761826363059 45473865965929142739544589)
            ·
              refine ⟨17052699737223428527329221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45473865965929142739544589 17052699737223428527329221)
              ·
                refine ⟨3197381200729392848874229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17052699737223428527329221 3197381200729392848874229)
                ·
                  refine ⟨299754487568380579581959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3197381200729392848874229 299754487568380579581959)
                  ·
                    rfl

theorem cell23_5253928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 5].length) (baseStart_5253928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253928 prefixEnd_5253928 := by exact prefixLift 5253928
  have htrace : WordTrace (prefixWord ++ tailWord_5253928) baseStart_5253928 baseEnd_5253928 := by
    simpa [prefixWord, tailWord_5253928, baseEnd_5253928] using wordTrace_append hprefix tailTrace_5253928
  have hstable : (prefixWord ++ tailWord_5253928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253928).length < 2 ^ (prefixWord ++ tailWord_5253928).sum := by decide
  have hdescent : baseEnd_5253928 < baseStart_5253928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253931 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 2, 5, 2]
def baseStart_5253931 : Nat := 118140960795 + 5253931 * 2 ^ 59
def prefixEnd_5253931 : Nat := 4983230072969 + 3 ^ 40 * 5253931 * 2
def baseEnd_5253931 : Nat := 2697791928557388704500117

theorem tailTrace_5253931 : CollatzResearch.WordTrace tailWord_5253931 prefixEnd_5253931 2697791928557388704500117 := by
  unfold tailWord_5253931
  simp only [CollatzResearch.WordTrace]
  refine ⟨191626606328912761822209647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127751070885941841214806431 191626606328912761822209647)
  ·
    refine ⟨287439909493369142733314471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191626606328912761822209647 287439909493369142733314471)
    ·
      refine ⟨431159864240053714099971707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287439909493369142733314471 431159864240053714099971707)
      ·
        refine ⟨646739796360080571149957561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431159864240053714099971707 646739796360080571149957561)
        ·
          refine ⟨485054847270060428362468171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646739796360080571149957561 485054847270060428362468171)
          ·
            refine ⟨727582270905090642543702257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485054847270060428362468171 727582270905090642543702257)
            ·
              refine ⟨545686703178817981907776693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727582270905090642543702257 545686703178817981907776693)
              ·
                refine ⟨51158128423014185803854065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 545686703178817981907776693 51158128423014185803854065)
                ·
                  refine ⟨38368596317260639352890549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51158128423014185803854065 38368596317260639352890549)
                  ·
                    refine ⟨3597055904743184939333489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38368596317260639352890549 3597055904743184939333489)
                    ·
                      refine ⟨2697791928557388704500117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597055904743184939333489 2697791928557388704500117)
                      ·
                        rfl

theorem cell23_5253931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5, 2].length) (baseStart_5253931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253931 prefixEnd_5253931 := by exact prefixLift 5253931
  have htrace : WordTrace (prefixWord ++ tailWord_5253931) baseStart_5253931 baseEnd_5253931 := by
    simpa [prefixWord, tailWord_5253931, baseEnd_5253931] using wordTrace_append hprefix tailTrace_5253931
  have hstable : (prefixWord ++ tailWord_5253931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253931).length < 2 ^ (prefixWord ++ tailWord_5253931).sum := by decide
  have hdescent : baseEnd_5253931 < baseStart_5253931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253961 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_5253961 : Nat := 118140960795 + 5253961 * 2 ^ 59
def prefixEnd_5253961 : Nat := 4983230072969 + 3 ^ 40 * 5253961 * 2
def baseEnd_5253961 : Nat := 2697807332977023587124979

theorem tailTrace_5253961 : CollatzResearch.WordTrace tailWord_5253961 prefixEnd_5253961 2697807332977023587124979 := by
  unfold tailWord_5253961
  simp only [CollatzResearch.WordTrace]
  refine ⟨191627700518804076945801737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127751800345869384630534491 191627700518804076945801737)
  ·
    refine ⟨143720775389103057709351303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191627700518804076945801737 143720775389103057709351303)
    ·
      refine ⟨215581163083654586564026955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143720775389103057709351303 215581163083654586564026955)
      ·
        refine ⟨323371744625481879846040433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215581163083654586564026955 323371744625481879846040433)
        ·
          refine ⟨242528808469111409884530325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323371744625481879846040433 242528808469111409884530325)
          ·
            refine ⟨11368537896989597338337359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 242528808469111409884530325 11368537896989597338337359)
            ·
              refine ⟨17052806845484396007506039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11368537896989597338337359 17052806845484396007506039)
              ·
                refine ⟨25579210268226594011259059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17052806845484396007506039 25579210268226594011259059)
                ·
                  refine ⟨38368815402339891016888589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25579210268226594011259059 38368815402339891016888589)
                  ·
                    refine ⟨14388305775877459131333221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38368815402339891016888589 14388305775877459131333221)
                    ·
                      refine ⟨2697807332977023587124979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14388305775877459131333221 2697807332977023587124979)
                      ·
                        rfl

theorem cell23_5253961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_5253961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253961 prefixEnd_5253961 := by exact prefixLift 5253961
  have htrace : WordTrace (prefixWord ++ tailWord_5253961) baseStart_5253961 baseEnd_5253961 := by
    simpa [prefixWord, tailWord_5253961, baseEnd_5253961] using wordTrace_append hprefix tailTrace_5253961
  have hstable : (prefixWord ++ tailWord_5253961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253961).length < 2 ^ (prefixWord ++ tailWord_5253961).sum := by decide
  have hdescent : baseEnd_5253961 < baseStart_5253961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253978 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2]
def baseStart_5253978 : Nat := 118140960795 + 5253978 * 2 ^ 59
def prefixEnd_5253978 : Nat := 4983230072969 + 3 ^ 40 * 5253978 * 2
def baseEnd_5253978 : Nat := 2697816062148150020612401

theorem tailTrace_5253978 : CollatzResearch.WordTrace tailWord_5253978 prefixEnd_5253978 2697816062148150020612401 := by
  unfold tailWord_5253978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47907080139935622212292647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127752213706494992566113725 47907080139935622212292647)
  ·
    refine ⟨71860620209903433318438971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47907080139935622212292647 71860620209903433318438971)
    ·
      refine ⟨107790930314855149977658457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71860620209903433318438971 107790930314855149977658457)
      ·
        refine ⟨80843197736141362483243843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107790930314855149977658457 80843197736141362483243843)
        ·
          refine ⟨121264796604212043724865765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80843197736141362483243843 121264796604212043724865765)
          ·
            refine ⟨22737149363289758198412331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121264796604212043724865765 22737149363289758198412331)
            ·
              refine ⟨34105724044934637297618497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22737149363289758198412331 34105724044934637297618497)
              ·
                refine ⟨25579293033700977973213873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34105724044934637297618497 25579293033700977973213873)
                ·
                  refine ⟨19184469775275733479910405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25579293033700977973213873 19184469775275733479910405)
                  ·
                    refine ⟨3597088082864200027483201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19184469775275733479910405 3597088082864200027483201)
                    ·
                      refine ⟨2697816062148150020612401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597088082864200027483201 2697816062148150020612401)
                      ·
                        rfl

theorem cell23_5253978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_5253978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253978 prefixEnd_5253978 := by exact prefixLift 5253978
  have htrace : WordTrace (prefixWord ++ tailWord_5253978) baseStart_5253978 baseEnd_5253978 := by
    simpa [prefixWord, tailWord_5253978, baseEnd_5253978] using wordTrace_append hprefix tailTrace_5253978
  have hstable : (prefixWord ++ tailWord_5253978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253978).length < 2 ^ (prefixWord ++ tailWord_5253978).sum := by decide
  have hdescent : baseEnd_5253978 < baseStart_5253978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5253988 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_5253988 : Nat := 118140960795 + 5253988 * 2 ^ 59
def prefixEnd_5253988 : Nat := 4983230072969 + 3 ^ 40 * 5253988 * 2
def baseEnd_5253988 : Nat := 899273732318231660495785

theorem tailTrace_5253988 : CollatzResearch.WordTrace tailWord_5253988 prefixEnd_5253988 899273732318231660495785 := by
  unfold tailWord_5253988
  simp only [CollatzResearch.WordTrace]
  refine ⟨95814342644853130278517309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127752456859804173704689745 95814342644853130278517309)
  ·
    refine ⟨35930378491819923854443991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95814342644853130278517309 35930378491819923854443991)
    ·
      refine ⟨53895567737729885781665987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35930378491819923854443991 53895567737729885781665987)
      ·
        refine ⟨80843351606594828672498981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53895567737729885781665987 80843351606594828672498981)
        ·
          refine ⟨15158128426236530376093559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80843351606594828672498981 15158128426236530376093559)
          ·
            refine ⟨22737192639354795564140339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15158128426236530376093559 22737192639354795564140339)
            ·
              refine ⟨34105788959032193346210509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22737192639354795564140339 34105788959032193346210509)
              ·
                refine ⟨12789670859637072504828941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34105788959032193346210509 12789670859637072504828941)
                ·
                  refine ⟨4796126572363902189310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12789670859637072504828941 4796126572363902189310853)
                  ·
                    refine ⟨899273732318231660495785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796126572363902189310853 899273732318231660495785)
                    ·
                      rfl

theorem cell23_5253988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_5253988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5253988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5253988 prefixEnd_5253988 := by exact prefixLift 5253988
  have htrace : WordTrace (prefixWord ++ tailWord_5253988) baseStart_5253988 baseEnd_5253988 := by
    simpa [prefixWord, tailWord_5253988, baseEnd_5253988] using wordTrace_append hprefix tailTrace_5253988
  have hstable : (prefixWord ++ tailWord_5253988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5253988).length < 2 ^ (prefixWord ++ tailWord_5253988).sum := by decide
  have hdescent : baseEnd_5253988 < baseStart_5253988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5253988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254028 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_5254028 : Nat := 118140960795 + 5254028 * 2 ^ 59
def prefixEnd_5254028 : Nat := 4983230072969 + 3 ^ 40 * 5254028 * 2
def baseEnd_5254028 : Nat := 2697841736180874824987171

theorem tailTrace_5254028 : CollatzResearch.WordTrace tailWord_5254028 prefixEnd_5254028 2697841736180874824987171 := by
  unfold tailWord_5254028
  simp only [CollatzResearch.WordTrace]
  refine ⟨95815072104780673694245369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127753429473040898258993825 95815072104780673694245369)
  ·
    refine ⟨71861304078585505270684027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95815072104780673694245369 71861304078585505270684027)
    ·
      refine ⟨107791956117878257906026041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71861304078585505270684027 107791956117878257906026041)
      ·
        refine ⟨80843967088408693429519531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107791956117878257906026041 80843967088408693429519531)
        ·
          refine ⟨121265950632613040144279297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80843967088408693429519531 121265950632613040144279297)
          ·
            refine ⟨90949462974459780108209473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121265950632613040144279297 90949462974459780108209473)
            ·
              refine ⟨68212097230844835081157105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90949462974459780108209473 68212097230844835081157105)
              ·
                refine ⟨51159072923133626310867829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68212097230844835081157105 51159072923133626310867829)
                ·
                  refine ⟨4796163086543777466643859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51159072923133626310867829 4796163086543777466643859)
                  ·
                    refine ⟨7194244629815666199965789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796163086543777466643859 7194244629815666199965789)
                    ·
                      refine ⟨2697841736180874824987171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194244629815666199965789 2697841736180874824987171)
                      ·
                        rfl

theorem cell23_5254028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_5254028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254028 prefixEnd_5254028 := by exact prefixLift 5254028
  have htrace : WordTrace (prefixWord ++ tailWord_5254028) baseStart_5254028 baseEnd_5254028 := by
    simpa [prefixWord, tailWord_5254028, baseEnd_5254028] using wordTrace_append hprefix tailTrace_5254028
  have hstable : (prefixWord ++ tailWord_5254028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254028).length < 2 ^ (prefixWord ++ tailWord_5254028).sum := by decide
  have hdescent : baseEnd_5254028 < baseStart_5254028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254071 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_5254071 : Nat := 118140960795 + 5254071 * 2 ^ 59
def prefixEnd_5254071 : Nat := 4983230072969 + 3 ^ 40 * 5254071 * 2
def baseEnd_5254071 : Nat := 2697863815849018156749473

theorem tailTrace_5254071 : CollatzResearch.WordTrace tailWord_5254071 prefixEnd_5254071 2697863815849018156749473 := by
  unfold tailWord_5254071
  simp only [CollatzResearch.WordTrace]
  refine ⟨191631712548405565732306067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127754475032270377154870711 191631712548405565732306067)
  ·
    refine ⟨287447568822608348598459101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191631712548405565732306067 287447568822608348598459101)
    ·
      refine ⟨107792838308478130724422163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287447568822608348598459101 107792838308478130724422163)
      ·
        refine ⟨161689257462717196086633245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107792838308478130724422163 161689257462717196086633245)
        ·
          refine ⟨60633471548518948532487467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161689257462717196086633245 60633471548518948532487467)
          ·
            refine ⟨90950207322778422798731201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60633471548518948532487467 90950207322778422798731201)
            ·
              refine ⟨68212655492083817099048401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90950207322778422798731201 68212655492083817099048401)
              ·
                refine ⟨51159491619062862824286301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68212655492083817099048401 51159491619062862824286301)
                ·
                  refine ⟨19184809357148573559107363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51159491619062862824286301 19184809357148573559107363)
                  ·
                    refine ⟨28777214035722860338661045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19184809357148573559107363 28777214035722860338661045)
                    ·
                      refine ⟨2697863815849018156749473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28777214035722860338661045 2697863815849018156749473)
                      ·
                        rfl

theorem cell23_5254071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_5254071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254071 prefixEnd_5254071 := by exact prefixLift 5254071
  have htrace : WordTrace (prefixWord ++ tailWord_5254071) baseStart_5254071 baseEnd_5254071 := by
    simpa [prefixWord, tailWord_5254071, baseEnd_5254071] using wordTrace_append hprefix tailTrace_5254071
  have hstable : (prefixWord ++ tailWord_5254071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254071).length < 2 ^ (prefixWord ++ tailWord_5254071).sum := by decide
  have hdescent : baseEnd_5254071 < baseStart_5254071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254078 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_5254078 : Nat := 118140960795 + 5254078 * 2 ^ 59
def prefixEnd_5254078 : Nat := 4983230072969 + 3 ^ 40 * 5254078 * 2
def baseEnd_5254078 : Nat := 899289136737866543120647

theorem tailTrace_5254078 : CollatzResearch.WordTrace tailWord_5254078 prefixEnd_5254078 899289136737866543120647 := by
  unfold tailWord_5254078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23953995982422525740976361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127754645239586803951873925 23953995982422525740976361)
  ·
    refine ⟨17965496986816894305732271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23953995982422525740976361 17965496986816894305732271)
    ·
      refine ⟨26948245480225341458598407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17965496986816894305732271 26948245480225341458598407)
      ·
        refine ⟨40422368220338012187897611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26948245480225341458598407 40422368220338012187897611)
        ·
          refine ⟨60633552330507018281846417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40422368220338012187897611 60633552330507018281846417)
          ·
            refine ⟨45475164247880263711384813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60633552330507018281846417 45475164247880263711384813)
            ·
              refine ⟨17053186592955098891769305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45475164247880263711384813 17053186592955098891769305)
              ·
                refine ⟨12789889944716324168826979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17053186592955098891769305 12789889944716324168826979)
                ·
                  refine ⟨19184834917074486253240469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12789889944716324168826979 19184834917074486253240469)
                  ·
                    refine ⟨899289136737866543120647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19184834917074486253240469 899289136737866543120647)
                    ·
                      rfl

theorem cell23_5254078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_5254078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254078 prefixEnd_5254078 := by exact prefixLift 5254078
  have htrace : WordTrace (prefixWord ++ tailWord_5254078) baseStart_5254078 baseEnd_5254078 := by
    simpa [prefixWord, tailWord_5254078, baseEnd_5254078] using wordTrace_append hprefix tailTrace_5254078
  have hstable : (prefixWord ++ tailWord_5254078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254078).length < 2 ^ (prefixWord ++ tailWord_5254078).sum := by decide
  have hdescent : baseEnd_5254078 < baseStart_5254078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254086 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_5254086 : Nat := 118140960795 + 5254086 * 2 ^ 59
def prefixEnd_5254086 : Nat := 4983230072969 + 3 ^ 40 * 5254086 * 2
def baseEnd_5254086 : Nat := 299763502006537288673545

theorem tailTrace_5254086 : CollatzResearch.WordTrace tailWord_5254086 prefixEnd_5254086 299763502006537288673545 := by
  unfold tailWord_5254086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988508113854725727940691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127754839762234148862734741 5988508113854725727940691)
  ·
    refine ⟨8982762170782088591911037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988508113854725727940691 8982762170782088591911037)
    ·
      refine ⟨3368535814043283221966639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8982762170782088591911037 3368535814043283221966639)
      ·
        refine ⟨5052803721064924832949959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368535814043283221966639 5052803721064924832949959)
        ·
          refine ⟨7579205581597387249424939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052803721064924832949959 7579205581597387249424939)
          ·
            refine ⟨11368808372396080874137409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7579205581597387249424939 11368808372396080874137409)
            ·
              refine ⟨8526606279297060655603057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11368808372396080874137409 8526606279297060655603057)
              ·
                refine ⟨6394954709472795491702293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526606279297060655603057 6394954709472795491702293)
                ·
                  refine ⟨299763502006537288673545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6394954709472795491702293 299763502006537288673545)
                  ·
                    rfl

theorem cell23_5254086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_5254086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254086 prefixEnd_5254086 := by exact prefixLift 5254086
  have htrace : WordTrace (prefixWord ++ tailWord_5254086) baseStart_5254086 baseEnd_5254086 := by
    simpa [prefixWord, tailWord_5254086, baseEnd_5254086] using wordTrace_append hprefix tailTrace_5254086
  have hstable : (prefixWord ++ tailWord_5254086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254086).length < 2 ^ (prefixWord ++ tailWord_5254086).sum := by decide
  have hdescent : baseEnd_5254086 < baseStart_5254086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254095 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 2, 4]
def baseStart_5254095 : Nat := 118140960795 + 5254095 * 2 ^ 59
def prefixEnd_5254095 : Nat := 4983230072969 + 3 ^ 40 * 5254095 * 2
def baseEnd_5254095 : Nat := 899292046461575354283121

theorem tailTrace_5254095 : CollatzResearch.WordTrace tailWord_5254095 prefixEnd_5254095 899292046461575354283121 := by
  unfold tailWord_5254095
  simp only [CollatzResearch.WordTrace]
  refine ⟨191632587900318617831179739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127755058600212411887453159 191632587900318617831179739)
  ·
    refine ⟨287448881850477926746769609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191632587900318617831179739 287448881850477926746769609)
    ·
      refine ⟨215586661387858445060077207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287448881850477926746769609 215586661387858445060077207)
      ·
        refine ⟨323379992081787667590115811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215586661387858445060077207 323379992081787667590115811)
        ·
          refine ⟨485069988122681501385173717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323379992081787667590115811 485069988122681501385173717)
          ·
            refine ⟨11368827846625347688715009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 485069988122681501385173717 11368827846625347688715009)
            ·
              refine ⟨8526620884969010766536257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11368827846625347688715009 8526620884969010766536257)
              ·
                refine ⟨6394965663726758074902193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526620884969010766536257 6394965663726758074902193)
                ·
                  refine ⟨4796224247795068556176645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394965663726758074902193 4796224247795068556176645)
                  ·
                    refine ⟨899292046461575354283121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796224247795068556176645 899292046461575354283121)
                    ·
                      rfl

theorem cell23_5254095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_5254095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254095 prefixEnd_5254095 := by exact prefixLift 5254095
  have htrace : WordTrace (prefixWord ++ tailWord_5254095) baseStart_5254095 baseEnd_5254095 := by
    simpa [prefixWord, tailWord_5254095, baseEnd_5254095] using wordTrace_append hprefix tailTrace_5254095
  have hstable : (prefixWord ++ tailWord_5254095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254095).length < 2 ^ (prefixWord ++ tailWord_5254095).sum := by decide
  have hdescent : baseEnd_5254095 < baseStart_5254095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254146 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5254146 : Nat := 118140960795 + 5254146 * 2 ^ 59
def prefixEnd_5254146 : Nat := 4983230072969 + 3 ^ 40 * 5254146 * 2
def baseEnd_5254146 : Nat := 899300775632701787770543

theorem tailTrace_5254146 : CollatzResearch.WordTrace tailWord_5254146 prefixEnd_5254146 899300775632701787770543 := by
  unfold tailWord_5254146
  simp only [CollatzResearch.WordTrace]
  refine ⟨47908612005783463385321573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127756298682089235694190861 47908612005783463385321573)
  ·
    refine ⟨8982864751084399384747795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47908612005783463385321573 8982864751084399384747795)
    ·
      refine ⟨13474297126626599077121693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8982864751084399384747795 13474297126626599077121693)
      ·
        refine ⟨5052861422484974653920635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13474297126626599077121693 5052861422484974653920635)
        ·
          refine ⟨7579292133727461980880953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052861422484974653920635 7579292133727461980880953)
          ·
            refine ⟨5684469100295596485660715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7579292133727461980880953 5684469100295596485660715)
            ·
              refine ⟨8526703650443394728491073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684469100295596485660715 8526703650443394728491073)
              ·
                refine ⟨6395027737832546046368305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526703650443394728491073 6395027737832546046368305)
                ·
                  refine ⟨4796270803374409534776229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395027737832546046368305 4796270803374409534776229)
                  ·
                    refine ⟨899300775632701787770543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796270803374409534776229 899300775632701787770543)
                    ·
                      rfl

theorem cell23_5254146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5254146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254146 prefixEnd_5254146 := by exact prefixLift 5254146
  have htrace : WordTrace (prefixWord ++ tailWord_5254146) baseStart_5254146 baseEnd_5254146 := by
    simpa [prefixWord, tailWord_5254146, baseEnd_5254146] using wordTrace_append hprefix tailTrace_5254146
  have hstable : (prefixWord ++ tailWord_5254146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254146).length < 2 ^ (prefixWord ++ tailWord_5254146).sum := by decide
  have hdescent : baseEnd_5254146 < baseStart_5254146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254152 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_5254152 : Nat := 118140960795 + 5254152 * 2 ^ 59
def prefixEnd_5254152 : Nat := 4983230072969 + 3 ^ 40 * 5254152 * 2
def baseEnd_5254152 : Nat := 2697905407782032339836601

theorem tailTrace_5254152 : CollatzResearch.WordTrace tailWord_5254152 prefixEnd_5254152 2697905407782032339836601 := by
  unfold tailWord_5254152
  simp only [CollatzResearch.WordTrace]
  refine ⟨95817333430556058283002355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127756444574074744377336473 95817333430556058283002355)
  ·
    refine ⟨143726000145834087424503533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95817333430556058283002355 143726000145834087424503533)
    ·
      refine ⟨53897250054687782784188825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143726000145834087424503533 53897250054687782784188825)
      ·
        refine ⟨40422937541015837088141619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53897250054687782784188825 40422937541015837088141619)
        ·
          refine ⟨60634406311523755632212429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40422937541015837088141619 60634406311523755632212429)
          ·
            refine ⟨22737902366821408362079661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60634406311523755632212429 22737902366821408362079661)
            ·
              refine ⟨8526713387558028135779873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22737902366821408362079661 8526713387558028135779873)
              ·
                refine ⟨6395035040668521101834905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526713387558028135779873 6395035040668521101834905)
                ·
                  refine ⟨4796276280501390826376179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395035040668521101834905 4796276280501390826376179)
                  ·
                    refine ⟨7194414420752086239564269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796276280501390826376179 7194414420752086239564269)
                    ·
                      refine ⟨2697905407782032339836601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194414420752086239564269 2697905407782032339836601)
                      ·
                        rfl

theorem cell23_5254152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_5254152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254152 prefixEnd_5254152 := by exact prefixLift 5254152
  have htrace : WordTrace (prefixWord ++ tailWord_5254152) baseStart_5254152 baseEnd_5254152 := by
    simpa [prefixWord, tailWord_5254152, baseEnd_5254152] using wordTrace_append hprefix tailTrace_5254152
  have hstable : (prefixWord ++ tailWord_5254152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254152).length < 2 ^ (prefixWord ++ tailWord_5254152).sum := by decide
  have hdescent : baseEnd_5254152 < baseStart_5254152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254168 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_5254168 : Nat := 118140960795 + 5254168 * 2 ^ 59
def prefixEnd_5254168 : Nat := 4983230072969 + 3 ^ 40 * 5254168 * 2
def baseEnd_5254168 : Nat := 899304541157501425745509

theorem tailTrace_5254168 : CollatzResearch.WordTrace tailWord_5254168 prefixEnd_5254168 899304541157501425745509 := by
  unfold tailWord_5254168
  simp only [CollatzResearch.WordTrace]
  refine ⟨95817625214527075649293579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127756833619369434199058105 95817625214527075649293579)
  ·
    refine ⟨143726437821790613473940369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95817625214527075649293579 143726437821790613473940369)
    ·
      refine ⟨107794828366342960105455277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143726437821790613473940369 107794828366342960105455277)
      ·
        refine ⟨40423060637378610039545729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107794828366342960105455277 40423060637378610039545729)
        ·
          refine ⟨30317295478033957529659297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40423060637378610039545729 30317295478033957529659297)
          ·
            refine ⟨22737971608525468147244473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30317295478033957529659297 22737971608525468147244473)
            ·
              refine ⟨17053478706394101110433355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22737971608525468147244473 17053478706394101110433355)
              ·
                refine ⟨25580218059591151665650033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17053478706394101110433355 25580218059591151665650033)
                ·
                  refine ⟨19185163544693363749237525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25580218059591151665650033 19185163544693363749237525)
                  ·
                    refine ⟨899304541157501425745509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19185163544693363749237525 899304541157501425745509)
                    ·
                      rfl

theorem cell23_5254168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_5254168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254168 prefixEnd_5254168 := by exact prefixLift 5254168
  have htrace : WordTrace (prefixWord ++ tailWord_5254168) baseStart_5254168 baseEnd_5254168 := by
    simpa [prefixWord, tailWord_5254168, baseEnd_5254168] using wordTrace_append hprefix tailTrace_5254168
  have hstable : (prefixWord ++ tailWord_5254168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254168).length < 2 ^ (prefixWord ++ tailWord_5254168).sum := by decide
  have hdescent : baseEnd_5254168 < baseStart_5254168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254215 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 7]
def baseStart_5254215 : Nat := 118140960795 + 5254215 * 2 ^ 59
def prefixEnd_5254215 : Nat := 4983230072969 + 3 ^ 40 * 5254215 * 2
def baseEnd_5254215 : Nat := 299770861895918399260979

theorem tailTrace_5254215 : CollatzResearch.WordTrace tailWord_5254215 prefixEnd_5254215 299770861895918399260979 := by
  unfold tailWord_5254215
  simp only [CollatzResearch.WordTrace]
  refine ⟨191636964659883878325548099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127757976439922585550365399 191636964659883878325548099)
  ·
    refine ⟨287455446989825817488322149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191636964659883878325548099 287455446989825817488322149)
    ·
      refine ⟨53897896310592340779060403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287455446989825817488322149 53897896310592340779060403)
      ·
        refine ⟨80846844465888511168590605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53897896310592340779060403 80846844465888511168590605)
        ·
          refine ⟨30317566674708191688221477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80846844465888511168590605 30317566674708191688221477)
          ·
            refine ⟨5684543751507785941541527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30317566674708191688221477 5684543751507785941541527)
            ·
              refine ⟨8526815627261678912312291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684543751507785941541527 8526815627261678912312291)
              ·
                refine ⟨12790223440892518368468437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8526815627261678912312291 12790223440892518368468437)
                ·
                  refine ⟨299770861895918399260979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12790223440892518368468437 299770861895918399260979)
                  ·
                    rfl

theorem cell23_5254215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 7].length) (baseStart_5254215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254215 prefixEnd_5254215 := by exact prefixLift 5254215
  have htrace : WordTrace (prefixWord ++ tailWord_5254215) baseStart_5254215 baseEnd_5254215 := by
    simpa [prefixWord, tailWord_5254215, baseEnd_5254215] using wordTrace_append hprefix tailTrace_5254215
  have hstable : (prefixWord ++ tailWord_5254215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254215).length < 2 ^ (prefixWord ++ tailWord_5254215).sum := by decide
  have hdescent : baseEnd_5254215 < baseStart_5254215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254226 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_5254226 : Nat := 118140960795 + 5254226 * 2 ^ 59
def prefixEnd_5254226 : Nat := 4983230072969 + 3 ^ 40 * 5254226 * 2
def baseEnd_5254226 : Nat := 2697943405350465050311261

theorem tailTrace_5254226 : CollatzResearch.WordTrace tailWord_5254226 prefixEnd_5254226 2697943405350465050311261 := by
  unfold tailWord_5254226
  simp only [CollatzResearch.WordTrace]
  refine ⟨47909341465711006801049633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127758243908562684802799021 47909341465711006801049633)
  ·
    refine ⟨35932006099283255100787225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47909341465711006801049633 35932006099283255100787225)
    ·
      refine ⟨26949004574462441325590419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35932006099283255100787225 26949004574462441325590419)
      ·
        refine ⟨40423506861693661988385629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26949004574462441325590419 40423506861693661988385629)
        ·
          refine ⟨15158815073135123245644611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40423506861693661988385629 15158815073135123245644611)
          ·
            refine ⟨22738222609702684868466917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15158815073135123245644611 22738222609702684868466917)
            ·
              refine ⟨4263416739319253412837547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22738222609702684868466917 4263416739319253412837547)
              ·
                refine ⟨6395125108978880119256321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263416739319253412837547 6395125108978880119256321)
                ·
                  refine ⟨4796343831734160089442241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395125108978880119256321 4796343831734160089442241)
                  ·
                    refine ⟨3597257873800620067081681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796343831734160089442241 3597257873800620067081681)
                    ·
                      refine ⟨2697943405350465050311261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597257873800620067081681 2697943405350465050311261)
                      ·
                        rfl

theorem cell23_5254226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_5254226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254226 prefixEnd_5254226 := by exact prefixLift 5254226
  have htrace : WordTrace (prefixWord ++ tailWord_5254226) baseStart_5254226 baseEnd_5254226 := by
    simpa [prefixWord, tailWord_5254226, baseEnd_5254226] using wordTrace_append hprefix tailTrace_5254226
  have hstable : (prefixWord ++ tailWord_5254226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254226).length < 2 ^ (prefixWord ++ tailWord_5254226).sum := by decide
  have hdescent : baseEnd_5254226 < baseStart_5254226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254228 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_5254228 : Nat := 118140960795 + 5254228 * 2 ^ 59
def prefixEnd_5254228 : Nat := 4983230072969 + 3 ^ 40 * 5254228 * 2
def baseEnd_5254228 : Nat := 899314810770591347495417

theorem tailTrace_5254228 : CollatzResearch.WordTrace tailWord_5254228 prefixEnd_5254228 899314810770591347495417 := by
  unfold tailWord_5254228
  simp only [CollatzResearch.WordTrace]
  refine ⟨95818719404418390772885669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127758292539224521030514225 95818719404418390772885669)
  ·
    refine ⟨17966009888328448269916063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95818719404418390772885669 17966009888328448269916063)
    ·
      refine ⟨26949014832492672404874095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17966009888328448269916063 26949014832492672404874095)
      ·
        refine ⟨40423522248739008607311143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26949014832492672404874095 40423522248739008607311143)
        ·
          refine ⟨60635283373108512910966715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40423522248739008607311143 60635283373108512910966715)
          ·
            refine ⟨90952925059662769366450073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60635283373108512910966715 90952925059662769366450073)
            ·
              refine ⟨68214693794747077024837555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90952925059662769366450073 68214693794747077024837555)
              ·
                refine ⟨102322040692120615537256333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68214693794747077024837555 102322040692120615537256333)
                ·
                  refine ⟨38370765259545230826471125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102322040692120615537256333 38370765259545230826471125)
                  ·
                    refine ⟨899314810770591347495417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38370765259545230826471125 899314810770591347495417)
                    ·
                      rfl

theorem cell23_5254228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_5254228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254228 prefixEnd_5254228 := by exact prefixLift 5254228
  have htrace : WordTrace (prefixWord ++ tailWord_5254228) baseStart_5254228 baseEnd_5254228 := by
    simpa [prefixWord, tailWord_5254228, baseEnd_5254228] using wordTrace_append hprefix tailTrace_5254228
  have hstable : (prefixWord ++ tailWord_5254228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254228).length < 2 ^ (prefixWord ++ tailWord_5254228).sum := by decide
  have hdescent : baseEnd_5254228 < baseStart_5254228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254230 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5254230 : Nat := 118140960795 + 5254230 * 2 ^ 59
def prefixEnd_5254230 : Nat := 4983230072969 + 3 ^ 40 * 5254230 * 2
def baseEnd_5254230 : Nat := 2697945459273083034661243

theorem tailTrace_5254230 : CollatzResearch.WordTrace tailWord_5254230 prefixEnd_5254230 2697945459273083034661243 := by
  unfold tailWord_5254230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977344484676845992959009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127758341169886357258229429 11977344484676845992959009)
  ·
    refine ⟨8983008363507634494719257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11977344484676845992959009 8983008363507634494719257)
    ·
      refine ⟨6737256272630725871039443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8983008363507634494719257 6737256272630725871039443)
      ·
        refine ⟨10105884408946088806559165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737256272630725871039443 10105884408946088806559165)
        ·
          refine ⟨3789706653354783302459687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10105884408946088806559165 3789706653354783302459687)
          ·
            refine ⟨5684559980032174953689531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789706653354783302459687 5684559980032174953689531)
            ·
              refine ⟨8526839970048262430534297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684559980032174953689531 8526839970048262430534297)
              ·
                refine ⟨6395129977536196822900723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526839970048262430534297 6395129977536196822900723)
                ·
                  refine ⟨9592694966304295234351085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6395129977536196822900723 9592694966304295234351085)
                  ·
                    refine ⟨3597260612364110712881657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9592694966304295234351085 3597260612364110712881657)
                    ·
                      refine ⟨2697945459273083034661243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597260612364110712881657 2697945459273083034661243)
                      ·
                        rfl

theorem cell23_5254230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5254230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254230 prefixEnd_5254230 := by exact prefixLift 5254230
  have htrace : WordTrace (prefixWord ++ tailWord_5254230) baseStart_5254230 baseEnd_5254230 := by
    simpa [prefixWord, tailWord_5254230, baseEnd_5254230] using wordTrace_append hprefix tailTrace_5254230
  have hstable : (prefixWord ++ tailWord_5254230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254230).length < 2 ^ (prefixWord ++ tailWord_5254230).sum := by decide
  have hdescent : baseEnd_5254230 < baseStart_5254230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254245 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_5254245 : Nat := 118140960795 + 5254245 * 2 ^ 59
def prefixEnd_5254245 : Nat := 4983230072969 + 3 ^ 40 * 5254245 * 2
def baseEnd_5254245 : Nat := 899317720494300158657891

theorem tailTrace_5254245 : CollatzResearch.WordTrace tailWord_5254245 prefixEnd_5254245 899317720494300158657891 := by
  unfold tailWord_5254245
  simp only [CollatzResearch.WordTrace]
  refine ⟨191638058849775193449140189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127758705899850128966093459 191638058849775193449140189)
  ·
    refine ⟨71864272068665697543427571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191638058849775193449140189 71864272068665697543427571)
    ·
      refine ⟨107796408102998546315141357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71864272068665697543427571 107796408102998546315141357)
      ·
        refine ⟨40423653038624454868178009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107796408102998546315141357 40423653038624454868178009)
        ·
          refine ⟨30317739778968341151133507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40423653038624454868178009 30317739778968341151133507)
          ·
            refine ⟨45476609668452511726700261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30317739778968341151133507 45476609668452511726700261)
            ·
              refine ⟨8526864312834845948756299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45476609668452511726700261 8526864312834845948756299)
              ·
                refine ⟨12790296469252268923134449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8526864312834845948756299 12790296469252268923134449)
                ·
                  refine ⟨9592722351939201692350837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12790296469252268923134449 9592722351939201692350837)
                  ·
                    refine ⟨899317720494300158657891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9592722351939201692350837 899317720494300158657891)
                    ·
                      rfl

theorem cell23_5254245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_5254245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254245 prefixEnd_5254245 := by exact prefixLift 5254245
  have htrace : WordTrace (prefixWord ++ tailWord_5254245) baseStart_5254245 baseEnd_5254245 := by
    simpa [prefixWord, tailWord_5254245, baseEnd_5254245] using wordTrace_append hprefix tailTrace_5254245
  have hstable : (prefixWord ++ tailWord_5254245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254245).length < 2 ^ (prefixWord ++ tailWord_5254245).sum := by decide
  have hdescent : baseEnd_5254245 < baseStart_5254245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254268 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_5254268 : Nat := 118140960795 + 5254268 * 2 ^ 59
def prefixEnd_5254268 : Nat := 4983230072969 + 3 ^ 40 * 5254268 * 2
def baseEnd_5254268 : Nat := 2697964971537953885986067

theorem tailTrace_5254268 : CollatzResearch.WordTrace tailWord_5254268 prefixEnd_5254268 2697964971537953885986067 := by
  unfold tailWord_5254268
  simp only [CollatzResearch.WordTrace]
  refine ⟨95819448864345934188613729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127759265152461245584818305 95819448864345934188613729)
  ·
    refine ⟨71864586648259450641460297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95819448864345934188613729 71864586648259450641460297)
    ·
      refine ⟨53898439986194587981095223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71864586648259450641460297 53898439986194587981095223)
      ·
        refine ⟨80847659979291881971642835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53898439986194587981095223 80847659979291881971642835)
        ·
          refine ⟨121271489968937822957464253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80847659979291881971642835 121271489968937822957464253)
          ·
            refine ⟨45476808738351683609049095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121271489968937822957464253 45476808738351683609049095)
            ·
              refine ⟨68215213107527525413573643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45476808738351683609049095 68215213107527525413573643)
              ·
                refine ⟨102322819661291288120360465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68215213107527525413573643 102322819661291288120360465)
                ·
                  refine ⟨76742114745968466090270349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102322819661291288120360465 76742114745968466090270349)
                  ·
                    refine ⟨28778293029738174783851381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76742114745968466090270349 28778293029738174783851381)
                    ·
                      refine ⟨2697964971537953885986067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28778293029738174783851381 2697964971537953885986067)
                      ·
                        rfl

theorem cell23_5254268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_5254268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254268 prefixEnd_5254268 := by exact prefixLift 5254268
  have htrace : WordTrace (prefixWord ++ tailWord_5254268) baseStart_5254268 baseEnd_5254268 := by
    simpa [prefixWord, tailWord_5254268, baseEnd_5254268] using wordTrace_append hprefix tailTrace_5254268
  have hstable : (prefixWord ++ tailWord_5254268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254268).length < 2 ^ (prefixWord ++ tailWord_5254268).sum := by decide
  have hdescent : baseEnd_5254268 < baseStart_5254268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254275 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 3, 4]
def baseStart_5254275 : Nat := 118140960795 + 5254275 * 2 ^ 59
def prefixEnd_5254275 : Nat := 4983230072969 + 3 ^ 40 * 5254275 * 2
def baseEnd_5254275 : Nat := 899322855300845119532845

theorem tailTrace_5254275 : CollatzResearch.WordTrace tailWord_5254275 prefixEnd_5254275 899322855300845119532845 := by
  unfold tailWord_5254275
  simp only [CollatzResearch.WordTrace]
  refine ⟨191639153039666508572732279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127759435359777672381821519 191639153039666508572732279)
  ·
    refine ⟨287458729559499762859098419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191639153039666508572732279 287458729559499762859098419)
    ·
      refine ⟨431188094339249644288647629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287458729559499762859098419 431188094339249644288647629)
      ·
        refine ⟨161695535377218616608242861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 431188094339249644288647629 161695535377218616608242861)
        ·
          refine ⟨60635825766456981228091073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161695535377218616608242861 60635825766456981228091073)
          ·
            refine ⟨45476869324842735921068305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60635825766456981228091073 45476869324842735921068305)
            ·
              refine ⟨34107651993632051940801229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45476869324842735921068305 34107651993632051940801229)
              ·
                refine ⟨12790369497612019477800461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34107651993632051940801229 12790369497612019477800461)
                ·
                  refine ⟨4796388561604507304175173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12790369497612019477800461 4796388561604507304175173)
                  ·
                    refine ⟨899322855300845119532845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796388561604507304175173 899322855300845119532845)
                    ·
                      rfl

theorem cell23_5254275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 4].length) (baseStart_5254275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254275 prefixEnd_5254275 := by exact prefixLift 5254275
  have htrace : WordTrace (prefixWord ++ tailWord_5254275) baseStart_5254275 baseEnd_5254275 := by
    simpa [prefixWord, tailWord_5254275, baseEnd_5254275] using wordTrace_append hprefix tailTrace_5254275
  have hstable : (prefixWord ++ tailWord_5254275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254275).length < 2 ^ (prefixWord ++ tailWord_5254275).sum := by decide
  have hdescent : baseEnd_5254275 < baseStart_5254275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254282 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_5254282 : Nat := 118140960795 + 5254282 * 2 ^ 59
def prefixEnd_5254282 : Nat := 4983230072969 + 3 ^ 40 * 5254282 * 2
def baseEnd_5254282 : Nat := 2697972160267116831211003

theorem tailTrace_5254282 : CollatzResearch.WordTrace tailWord_5254282 prefixEnd_5254282 2697972160267116831211003 := by
  unfold tailWord_5254282
  simp only [CollatzResearch.WordTrace]
  refine ⟨47909852087660287192059275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127759605567094099178824733 47909852087660287192059275)
  ·
    refine ⟨71864778131490430788088913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47909852087660287192059275 71864778131490430788088913)
    ·
      refine ⟨53898583598617823091066685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71864778131490430788088913 53898583598617823091066685)
      ·
        refine ⟨20211968849481683659150007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53898583598617823091066685 20211968849481683659150007)
        ·
          refine ⟨30317953274222525488725011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20211968849481683659150007 30317953274222525488725011)
          ·
            refine ⟨45476929911333788233087517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30317953274222525488725011 45476929911333788233087517)
            ·
              refine ⟨17053848716750170587407819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45476929911333788233087517 17053848716750170587407819)
              ·
                refine ⟨25580773075125255881111729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17053848716750170587407819 25580773075125255881111729)
                ·
                  refine ⟨19185579806343941910833797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25580773075125255881111729 19185579806343941910833797)
                  ·
                    refine ⟨3597296213689489108281337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19185579806343941910833797 3597296213689489108281337)
                    ·
                      refine ⟨2697972160267116831211003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597296213689489108281337 2697972160267116831211003)
                      ·
                        rfl

theorem cell23_5254282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_5254282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254282 prefixEnd_5254282 := by exact prefixLift 5254282
  have htrace : WordTrace (prefixWord ++ tailWord_5254282) baseStart_5254282 baseEnd_5254282 := by
    simpa [prefixWord, tailWord_5254282, baseEnd_5254282] using wordTrace_append hprefix tailTrace_5254282
  have hstable : (prefixWord ++ tailWord_5254282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254282).length < 2 ^ (prefixWord ++ tailWord_5254282).sum := by decide
  have hdescent : baseEnd_5254282 < baseStart_5254282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254309 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_5254309 : Nat := 118140960795 + 5254309 * 2 ^ 59
def prefixEnd_5254309 : Nat := 4983230072969 + 3 ^ 40 * 5254309 * 2
def baseEnd_5254309 : Nat := 899328674748262741857793

theorem tailTrace_5254309 : CollatzResearch.WordTrace tailWord_5254309 prefixEnd_5254309 899328674748262741857793 := by
  unfold tailWord_5254309
  simp only [CollatzResearch.WordTrace]
  refine ⟨191640393121543332379469981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127760262081028888252979987 191640393121543332379469981)
  ·
    refine ⟨71865147420578749642301243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191640393121543332379469981 71865147420578749642301243)
    ·
      refine ⟨107797721130868124463451865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71865147420578749642301243 107797721130868124463451865)
      ·
        refine ⟨80848290848151093347588899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107797721130868124463451865 80848290848151093347588899)
        ·
          refine ⟨121272436272226640021383349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80848290848151093347588899 121272436272226640021383349)
          ·
            refine ⟨11369290900521247502004689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121272436272226640021383349 11369290900521247502004689)
            ·
              refine ⟨8526968175390935626503517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11369290900521247502004689 8526968175390935626503517)
              ·
                refine ⟨3197613065771600859938819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8526968175390935626503517 3197613065771600859938819)
                ·
                  refine ⟨4796419598657401289908229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197613065771600859938819 4796419598657401289908229)
                  ·
                    refine ⟨899328674748262741857793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796419598657401289908229 899328674748262741857793)
                    ·
                      rfl

theorem cell23_5254309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_5254309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254309 prefixEnd_5254309 := by exact prefixLift 5254309
  have htrace : WordTrace (prefixWord ++ tailWord_5254309) baseStart_5254309 baseEnd_5254309 := by
    simpa [prefixWord, tailWord_5254309, baseEnd_5254309] using wordTrace_append hprefix tailTrace_5254309
  have hstable : (prefixWord ++ tailWord_5254309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254309).length < 2 ^ (prefixWord ++ tailWord_5254309).sum := by decide
  have hdescent : baseEnd_5254309 < baseStart_5254309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254322 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_5254322 : Nat := 118140960795 + 5254322 * 2 ^ 59
def prefixEnd_5254322 : Nat := 4983230072969 + 3 ^ 40 * 5254322 * 2
def baseEnd_5254322 : Nat := 299776966610366297190091

theorem tailTrace_5254322 : CollatzResearch.WordTrace tailWord_5254322 prefixEnd_5254322 299776966610366297190091 := by
  unfold tailWord_5254322
  simp only [CollatzResearch.WordTrace]
  refine ⟨47910216817624058899923305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127760578180330823733128813 47910216817624058899923305)
  ·
    refine ⟨35932662613218044174942479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47910216817624058899923305 35932662613218044174942479)
    ·
      refine ⟨53898993919827066262413719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35932662613218044174942479 53898993919827066262413719)
      ·
        refine ⟨80848490879740599393620579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53898993919827066262413719 80848490879740599393620579)
        ·
          refine ⟨121272736319610899090430869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80848490879740599393620579 121272736319610899090430869)
          ·
            refine ⟨5684659514981760894863947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121272736319610899090430869 5684659514981760894863947)
            ·
              refine ⟨8526989272472641342295921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684659514981760894863947 8526989272472641342295921)
              ·
                refine ⟨6395241954354481006721941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526989272472641342295921 6395241954354481006721941)
                ·
                  refine ⟨299776966610366297190091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6395241954354481006721941 299776966610366297190091)
                  ·
                    rfl

theorem cell23_5254322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_5254322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254322 prefixEnd_5254322 := by exact prefixLift 5254322
  have htrace : WordTrace (prefixWord ++ tailWord_5254322) baseStart_5254322 baseEnd_5254322 := by
    simpa [prefixWord, tailWord_5254322, baseEnd_5254322] using wordTrace_append hprefix tailTrace_5254322
  have hstable : (prefixWord ++ tailWord_5254322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254322).length < 2 ^ (prefixWord ++ tailWord_5254322).sum := by decide
  have hdescent : baseEnd_5254322 < baseStart_5254322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254328 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_5254328 : Nat := 118140960795 + 5254328 * 2 ^ 59
def prefixEnd_5254328 : Nat := 4983230072969 + 3 ^ 40 * 5254328 * 2
def baseEnd_5254328 : Nat := 2697995780377223651235791

theorem tailTrace_5254328 : CollatzResearch.WordTrace tailWord_5254328 prefixEnd_5254328 2697995780377223651235791 := by
  unfold tailWord_5254328
  simp only [CollatzResearch.WordTrace]
  refine ⟨95820543054237249312205819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127760724072316332416274425 95820543054237249312205819)
  ·
    refine ⟨143730814581355873968308729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95820543054237249312205819 143730814581355873968308729)
    ·
      refine ⟨107798110936016905476231547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143730814581355873968308729 107798110936016905476231547)
      ·
        refine ⟨161697166404025358214347321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107798110936016905476231547 161697166404025358214347321)
        ·
          refine ⟨121272874803019018660760491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161697166404025358214347321 121272874803019018660760491)
          ·
            refine ⟨181909312204528527991140737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121272874803019018660760491 181909312204528527991140737)
            ·
              refine ⟨136431984153396395993355553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181909312204528527991140737 136431984153396395993355553)
              ·
                refine ⟨102323988115047296995016665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136431984153396395993355553 102323988115047296995016665)
                ·
                  refine ⟨76742991086285472746262499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102323988115047296995016665 76742991086285472746262499)
                  ·
                    refine ⟨115114486629428209119393749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76742991086285472746262499 115114486629428209119393749)
                    ·
                      refine ⟨2697995780377223651235791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115114486629428209119393749 2697995780377223651235791)
                      ·
                        rfl

theorem cell23_5254328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_5254328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254328 prefixEnd_5254328 := by exact prefixLift 5254328
  have htrace : WordTrace (prefixWord ++ tailWord_5254328) baseStart_5254328 baseEnd_5254328 := by
    simpa [prefixWord, tailWord_5254328, baseEnd_5254328] using wordTrace_append hprefix tailTrace_5254328
  have hstable : (prefixWord ++ tailWord_5254328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254328).length < 2 ^ (prefixWord ++ tailWord_5254328).sum := by decide
  have hdescent : baseEnd_5254328 < baseStart_5254328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254372 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_5254372 : Nat := 118140960795 + 5254372 * 2 ^ 59
def prefixEnd_5254372 : Nat := 4983230072969 + 3 ^ 40 * 5254372 * 2
def baseEnd_5254372 : Nat := 2698018373526021479085589

theorem tailTrace_5254372 : CollatzResearch.WordTrace tailWord_5254372 prefixEnd_5254372 2698018373526021479085589 := by
  unfold tailWord_5254372
  simp only [CollatzResearch.WordTrace]
  refine ⟨95821345460157547069506685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127761793946876729426008913 95821345460157547069506685)
  ·
    refine ⟨35933004547559080151065007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95821345460157547069506685 35933004547559080151065007)
    ·
      refine ⟨53899506821338620226597511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35933004547559080151065007 53899506821338620226597511)
      ·
        refine ⟨80849260232007930339896267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53899506821338620226597511 80849260232007930339896267)
        ·
          refine ⟨121273890348011895509844401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80849260232007930339896267 121273890348011895509844401)
          ·
            refine ⟨90955417761008921632383301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121273890348011895509844401 90955417761008921632383301)
            ·
              refine ⟨17054140830189172806071869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90955417761008921632383301 17054140830189172806071869)
              ·
                refine ⟨6395302811320939802276951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17054140830189172806071869 6395302811320939802276951)
                ·
                  refine ⟨9592954216981409703415427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6395302811320939802276951 9592954216981409703415427)
                  ·
                    refine ⟨14389431325472114555123141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9592954216981409703415427 14389431325472114555123141)
                    ·
                      refine ⟨2698018373526021479085589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14389431325472114555123141 2698018373526021479085589)
                      ·
                        rfl

theorem cell23_5254372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_5254372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254372 prefixEnd_5254372 := by exact prefixLift 5254372
  have htrace : WordTrace (prefixWord ++ tailWord_5254372) baseStart_5254372 baseEnd_5254372 := by
    simpa [prefixWord, tailWord_5254372, baseEnd_5254372] using wordTrace_append hprefix tailTrace_5254372
  have hstable : (prefixWord ++ tailWord_5254372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254372).length < 2 ^ (prefixWord ++ tailWord_5254372).sum := by decide
  have hdescent : baseEnd_5254372 < baseStart_5254372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254382 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_5254382 : Nat := 118140960795 + 5254382 * 2 ^ 59
def prefixEnd_5254382 : Nat := 4983230072969 + 3 ^ 40 * 5254382 * 2
def baseEnd_5254382 : Nat := 899341169444188813320181

theorem tailTrace_5254382 : CollatzResearch.WordTrace tailWord_5254382 prefixEnd_5254382 899341169444188813320181 := by
  unfold tailWord_5254382
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955381956284858230859675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127762037100185910564584933 23955381956284858230859675)
  ·
    refine ⟨35933072934427287346289513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23955381956284858230859675 35933072934427287346289513)
    ·
      refine ⟨26949804700820465509717135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35933072934427287346289513 26949804700820465509717135)
      ·
        refine ⟨40424707051230698264575703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26949804700820465509717135 40424707051230698264575703)
        ·
          refine ⟨60637060576846047396863555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40424707051230698264575703 60637060576846047396863555)
          ·
            refine ⟨90955590865269071095295333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60637060576846047396863555 90955590865269071095295333)
            ·
              refine ⟨17054173287237950830367875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90955590865269071095295333 17054173287237950830367875)
              ·
                refine ⟨25581259930856926245551813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17054173287237950830367875 25581259930856926245551813)
                ·
                  refine ⟨4796486237035673671040965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25581259930856926245551813 4796486237035673671040965)
                  ·
                    refine ⟨899341169444188813320181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796486237035673671040965 899341169444188813320181)
                    ·
                      rfl

theorem cell23_5254382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_5254382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254382 prefixEnd_5254382 := by exact prefixLift 5254382
  have htrace : WordTrace (prefixWord ++ tailWord_5254382) baseStart_5254382 baseEnd_5254382 := by
    simpa [prefixWord, tailWord_5254382, baseEnd_5254382] using wordTrace_append hprefix tailTrace_5254382
  have hstable : (prefixWord ++ tailWord_5254382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254382).length < 2 ^ (prefixWord ++ tailWord_5254382).sum := by decide
  have hdescent : baseEnd_5254382 < baseStart_5254382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254383 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 1, 1, 3]
def baseStart_5254383 : Nat := 118140960795 + 5254383 * 2 ^ 59
def prefixEnd_5254383 : Nat := 4983230072969 + 3 ^ 40 * 5254383 * 2
def baseEnd_5254383 : Nat := 2698024021813220936048039

theorem tailTrace_5254383 : CollatzResearch.WordTrace tailWord_5254383 prefixEnd_5254383 2698024021813220936048039 := by
  unfold tailWord_5254383
  simp only [CollatzResearch.WordTrace]
  refine ⟨191643092123275243017663803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127762061415516828678442535 191643092123275243017663803)
  ·
    refine ⟨287464638184912864526495705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191643092123275243017663803 287464638184912864526495705)
    ·
      refine ⟨215598478638684648394871779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287464638184912864526495705 215598478638684648394871779)
      ·
        refine ⟨323397717958026972592307669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215598478638684648394871779 323397717958026972592307669)
        ·
          refine ⟨7579634014641257170132211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 323397717958026972592307669 7579634014641257170132211)
          ·
            refine ⟨11369451021961885755198317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7579634014641257170132211 11369451021961885755198317)
            ·
              refine ⟨4263544133235707158199369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11369451021961885755198317 4263544133235707158199369)
              ·
                refine ⟨3197658099926780368649527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4263544133235707158199369 3197658099926780368649527)
                ·
                  refine ⟨4796487149890170552974291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197658099926780368649527 4796487149890170552974291)
                  ·
                    refine ⟨7194730724835255829461437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796487149890170552974291 7194730724835255829461437)
                    ·
                      refine ⟨2698024021813220936048039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194730724835255829461437 2698024021813220936048039)
                      ·
                        rfl

theorem cell23_5254383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 1, 3].length) (baseStart_5254383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254383 prefixEnd_5254383 := by exact prefixLift 5254383
  have htrace : WordTrace (prefixWord ++ tailWord_5254383) baseStart_5254383 baseEnd_5254383 := by
    simpa [prefixWord, tailWord_5254383, baseEnd_5254383] using wordTrace_append hprefix tailTrace_5254383
  have hstable : (prefixWord ++ tailWord_5254383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254383).length < 2 ^ (prefixWord ++ tailWord_5254383).sum := by decide
  have hdescent : baseEnd_5254383 < baseStart_5254383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254399 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 2, 4]
def baseStart_5254399 : Nat := 118140960795 + 5254399 * 2 ^ 59
def prefixEnd_5254399 : Nat := 4983230072969 + 3 ^ 40 * 5254399 * 2
def baseEnd_5254399 : Nat := 899344079167897624482655

theorem tailTrace_5254399 : CollatzResearch.WordTrace tailWord_5254399 prefixEnd_5254399 899344079167897624482655 := by
  unfold tailWord_5254399
  simp only [CollatzResearch.WordTrace]
  refine ⟨191643675691217277750246251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127762450460811518500164167 191643675691217277750246251)
  ·
    refine ⟨287465513536825916625369377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191643675691217277750246251 287465513536825916625369377)
    ·
      refine ⟨215599135152619437469027033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287465513536825916625369377 215599135152619437469027033)
      ·
        refine ⟨161699351364464578101770275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215599135152619437469027033 161699351364464578101770275)
        ·
          refine ⟨242549027046696867152655413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161699351364464578101770275 242549027046696867152655413)
          ·
            refine ⟨22738971285627831295561445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242549027046696867152655413 22738971285627831295561445)
            ·
              refine ⟨4263557116055218367917771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22738971285627831295561445 4263557116055218367917771)
              ·
                refine ⟨6395335674082827551876657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263557116055218367917771 6395335674082827551876657)
                ·
                  refine ⟨4796501755562120663907493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395335674082827551876657 4796501755562120663907493)
                  ·
                    refine ⟨899344079167897624482655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796501755562120663907493 899344079167897624482655)
                    ·
                      rfl

theorem cell23_5254399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 4].length) (baseStart_5254399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254399 prefixEnd_5254399 := by exact prefixLift 5254399
  have htrace : WordTrace (prefixWord ++ tailWord_5254399) baseStart_5254399 baseEnd_5254399 := by
    simpa [prefixWord, tailWord_5254399, baseEnd_5254399] using wordTrace_append hprefix tailTrace_5254399
  have hstable : (prefixWord ++ tailWord_5254399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254399).length < 2 ^ (prefixWord ++ tailWord_5254399).sum := by decide
  have hdescent : baseEnd_5254399 < baseStart_5254399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254426 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3]
def baseStart_5254426 : Nat := 118140960795 + 5254426 * 2 ^ 59
def prefixEnd_5254426 : Nat := 4983230072969 + 3 ^ 40 * 5254426 * 2
def baseEnd_5254426 : Nat := 2698046101481364267810341

theorem tailTrace_5254426 : CollatzResearch.WordTrace tailWord_5254426 prefixEnd_5254426 2698046101481364267810341 := by
  unfold tailWord_5254426
  simp only [CollatzResearch.WordTrace]
  refine ⟨47911165115529865340369783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127763106974746307574319421 47911165115529865340369783)
  ·
    refine ⟨71866747673294798010554675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47911165115529865340369783 71866747673294798010554675)
    ·
      refine ⟨107800121509942197015832013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71866747673294798010554675 107800121509942197015832013)
      ·
        refine ⟨40425045566228323880937005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107800121509942197015832013 40425045566228323880937005)
        ·
          refine ⟨15159392087335621455351377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40425045566228323880937005 15159392087335621455351377)
          ·
            refine ⟨11369544065501716091513533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15159392087335621455351377 11369544065501716091513533)
            ·
              refine ⟨4263579024563143534317575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11369544065501716091513533 4263579024563143534317575)
              ·
                refine ⟨6395368536844715301476363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263579024563143534317575 6395368536844715301476363)
                ·
                  refine ⟨9593052805267072952214545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6395368536844715301476363 9593052805267072952214545)
                  ·
                    refine ⟨7194789603950304714160909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9593052805267072952214545 7194789603950304714160909)
                    ·
                      refine ⟨2698046101481364267810341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194789603950304714160909 2698046101481364267810341)
                      ·
                        rfl

theorem cell23_5254426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_5254426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254426 prefixEnd_5254426 := by exact prefixLift 5254426
  have htrace : WordTrace (prefixWord ++ tailWord_5254426) baseStart_5254426 baseEnd_5254426 := by
    simpa [prefixWord, tailWord_5254426, baseEnd_5254426] using wordTrace_append hprefix tailTrace_5254426
  have hstable : (prefixWord ++ tailWord_5254426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254426).length < 2 ^ (prefixWord ++ tailWord_5254426).sum := by decide
  have hdescent : baseEnd_5254426 < baseStart_5254426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254440 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_5254440 : Nat := 118140960795 + 5254440 * 2 ^ 59
def prefixEnd_5254440 : Nat := 4983230072969 + 3 ^ 40 * 5254440 * 2
def baseEnd_5254440 : Nat := 2698053290210527213035277

theorem tailTrace_5254440 : CollatzResearch.WordTrace tailWord_5254440 prefixEnd_5254440 2698053290210527213035277 := by
  unfold tailWord_5254440
  simp only [CollatzResearch.WordTrace]
  refine ⟨95822585542034370876244387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127763447389379161168325849 95822585542034370876244387)
  ·
    refine ⟨143733878313051556314366581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95822585542034370876244387 143733878313051556314366581)
    ·
      refine ⟨13475051091848583404471867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143733878313051556314366581 13475051091848583404471867)
      ·
        refine ⟨20212576637772875106707801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13475051091848583404471867 20212576637772875106707801)
        ·
          refine ⟨15159432478329656330030851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20212576637772875106707801 15159432478329656330030851)
          ·
            refine ⟨22739148717494484495046277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15159432478329656330030851 22739148717494484495046277)
            ·
              refine ⟨4263590384530215842821177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22739148717494484495046277 4263590384530215842821177)
              ·
                refine ⟨3197692788397661882115883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4263590384530215842821177 3197692788397661882115883)
                ·
                  refine ⟨4796539182596492823173825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197692788397661882115883 4796539182596492823173825)
                  ·
                    refine ⟨3597404386947369617380369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796539182596492823173825 3597404386947369617380369)
                    ·
                      refine ⟨2698053290210527213035277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597404386947369617380369 2698053290210527213035277)
                      ·
                        rfl

theorem cell23_5254440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_5254440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254440 prefixEnd_5254440 := by exact prefixLift 5254440
  have htrace : WordTrace (prefixWord ++ tailWord_5254440) baseStart_5254440 baseEnd_5254440 := by
    simpa [prefixWord, tailWord_5254440, baseEnd_5254440] using wordTrace_append hprefix tailTrace_5254440
  have hstable : (prefixWord ++ tailWord_5254440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254440).length < 2 ^ (prefixWord ++ tailWord_5254440).sum := by decide
  have hdescent : baseEnd_5254440 < baseStart_5254440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254442 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5254442 : Nat := 118140960795 + 5254442 * 2 ^ 59
def prefixEnd_5254442 : Nat := 4983230072969 + 3 ^ 40 * 5254442 * 2
def baseEnd_5254442 : Nat := 899351439057278735070089

theorem tailTrace_5254442 : CollatzResearch.WordTrace tailWord_5254442 prefixEnd_5254442 899351439057278735070089 := by
  unfold tailWord_5254442
  simp only [CollatzResearch.WordTrace]
  refine ⟨47911311007515374023515395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127763496020040997396041053 47911311007515374023515395)
  ·
    refine ⟨71866966511273061035273093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47911311007515374023515395 71866966511273061035273093)
    ·
      refine ⟨13475056220863698944113705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71866966511273061035273093 13475056220863698944113705)
      ·
        refine ⟨10106292165647774208085279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13475056220863698944113705 10106292165647774208085279)
        ·
          refine ⟨15159438248471661312127919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10106292165647774208085279 15159438248471661312127919)
          ·
            refine ⟨22739157372707491968191879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15159438248471661312127919 22739157372707491968191879)
            ·
              refine ⟨34108736059061237952287819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22739157372707491968191879 34108736059061237952287819)
              ·
                refine ⟨51163104088591856928431729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34108736059061237952287819 51163104088591856928431729)
                ·
                  refine ⟨38372328066443892696323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51163104088591856928431729 38372328066443892696323797)
                  ·
                    refine ⟨899351439057278735070089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38372328066443892696323797 899351439057278735070089)
                    ·
                      rfl

theorem cell23_5254442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5254442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254442 prefixEnd_5254442 := by exact prefixLift 5254442
  have htrace : WordTrace (prefixWord ++ tailWord_5254442) baseStart_5254442 baseEnd_5254442 := by
    simpa [prefixWord, tailWord_5254442, baseEnd_5254442] using wordTrace_append hprefix tailTrace_5254442
  have hstable : (prefixWord ++ tailWord_5254442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254442).length < 2 ^ (prefixWord ++ tailWord_5254442).sum := by decide
  have hdescent : baseEnd_5254442 < baseStart_5254442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254449 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 3, 3, 2]
def baseStart_5254449 : Nat := 118140960795 + 5254449 * 2 ^ 59
def prefixEnd_5254449 : Nat := 4983230072969 + 3 ^ 40 * 5254449 * 2
def baseEnd_5254449 : Nat := 2698057911536417677822735

theorem tailTrace_5254449 : CollatzResearch.WordTrace tailWord_5254449 prefixEnd_5254449 2698057911536417677822735 := by
  unfold tailWord_5254449
  simp only [CollatzResearch.WordTrace]
  refine ⟨191645499341036136289566401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127763666227357424193044267 191645499341036136289566401)
  ·
    refine ⟨143734124505777102217174801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191645499341036136289566401 143734124505777102217174801)
    ·
      refine ⟨107800593379332826662881101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143734124505777102217174801 107800593379332826662881101)
      ·
        refine ⟨40425222517249809998580413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107800593379332826662881101 40425222517249809998580413)
        ·
          refine ⟨15159458443968678749467655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40425222517249809998580413 15159458443968678749467655)
          ·
            refine ⟨22739187665953018124201483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15159458443968678749467655 22739187665953018124201483)
            ·
              refine ⟨34108781498929527186302225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22739187665953018124201483 34108781498929527186302225)
              ·
                refine ⟨25581586124197145389726669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34108781498929527186302225 25581586124197145389726669)
                ·
                  refine ⟨9593094796573929521147501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25581586124197145389726669 9593094796573929521147501)
                  ·
                    refine ⟨3597410548715223570430313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9593094796573929521147501 3597410548715223570430313)
                    ·
                      refine ⟨2698057911536417677822735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597410548715223570430313 2698057911536417677822735)
                      ·
                        rfl

theorem cell23_5254449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_5254449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254449 prefixEnd_5254449 := by exact prefixLift 5254449
  have htrace : WordTrace (prefixWord ++ tailWord_5254449) baseStart_5254449 baseEnd_5254449 := by
    simpa [prefixWord, tailWord_5254449, baseEnd_5254449] using wordTrace_append hprefix tailTrace_5254449
  have hstable : (prefixWord ++ tailWord_5254449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254449).length < 2 ^ (prefixWord ++ tailWord_5254449).sum := by decide
  have hdescent : baseEnd_5254449 < baseStart_5254449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254462 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5254462 : Nat := 118140960795 + 5254462 * 2 ^ 59
def prefixEnd_5254462 : Nat := 4983230072969 + 3 ^ 40 * 5254462 * 2
def baseEnd_5254462 : Nat := 2698064586784926126960175

theorem tailTrace_5254462 : CollatzResearch.WordTrace tailWord_5254462 prefixEnd_5254462 2698064586784926126960175 := by
  unfold tailWord_5254462
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955746686248629938723705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127763982326659359673193093 23955746686248629938723705)
  ·
    refine ⟨17966810014686472454042779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23955746686248629938723705 17966810014686472454042779)
    ·
      refine ⟨26950215022029708681064169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17966810014686472454042779 26950215022029708681064169)
      ·
        refine ⟨20212661266522281510798127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26950215022029708681064169 20212661266522281510798127)
        ·
          refine ⟨30318991899783422266197191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20212661266522281510798127 30318991899783422266197191)
          ·
            refine ⟨45478487849675133399295787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30318991899783422266197191 45478487849675133399295787)
            ·
              refine ⟨68217731774512700098943681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45478487849675133399295787 68217731774512700098943681)
              ·
                refine ⟨51163298830884525074207761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68217731774512700098943681 51163298830884525074207761)
                ·
                  refine ⟨38372474123163393805655821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51163298830884525074207761 38372474123163393805655821)
                  ·
                    refine ⟨14389677796186272677120933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38372474123163393805655821 14389677796186272677120933)
                    ·
                      refine ⟨2698064586784926126960175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14389677796186272677120933 2698064586784926126960175)
                      ·
                        rfl

theorem cell23_5254462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5254462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254462 prefixEnd_5254462 := by exact prefixLift 5254462
  have htrace : WordTrace (prefixWord ++ tailWord_5254462) baseStart_5254462 baseEnd_5254462 := by
    simpa [prefixWord, tailWord_5254462, baseEnd_5254462] using wordTrace_append hprefix tailTrace_5254462
  have hstable : (prefixWord ++ tailWord_5254462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254462).length < 2 ^ (prefixWord ++ tailWord_5254462).sum := by decide
  have hdescent : baseEnd_5254462 < baseStart_5254462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254477 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5254477 : Nat := 118140960795 + 5254477 * 2 ^ 59
def prefixEnd_5254477 : Nat := 4983230072969 + 3 ^ 40 * 5254477 * 2
def baseEnd_5254477 : Nat := 2698072288994743568272607

theorem tailTrace_5254477 : CollatzResearch.WordTrace tailWord_5254477 prefixEnd_5254477 2698072288994743568272607 := by
  unfold tailWord_5254477
  simp only [CollatzResearch.WordTrace]
  refine ⟨191646520584934697071585685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127764347056623131381057123 191646520584934697071585685)
  ·
    refine ⟨8983430652418813925230579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191646520584934697071585685 8983430652418813925230579)
    ·
      refine ⟨13475145978628220887845869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8983430652418813925230579 13475145978628220887845869)
      ·
        refine ⟨5053179741985582832942201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13475145978628220887845869 5053179741985582832942201)
        ·
          refine ⟨3789884806489187124706651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5053179741985582832942201 3789884806489187124706651)
          ·
            refine ⟨5684827209733780687059977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789884806489187124706651 5684827209733780687059977)
            ·
              refine ⟨4263620407300335515294983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5684827209733780687059977 4263620407300335515294983)
              ·
                refine ⟨6395430610950503272942475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263620407300335515294983 6395430610950503272942475)
                ·
                  refine ⟨9593145916425754909413713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6395430610950503272942475 9593145916425754909413713)
                  ·
                    refine ⟨7194859437319316182060285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9593145916425754909413713 7194859437319316182060285)
                    ·
                      refine ⟨2698072288994743568272607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194859437319316182060285 2698072288994743568272607)
                      ·
                        rfl

theorem cell23_5254477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5254477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254477 prefixEnd_5254477 := by exact prefixLift 5254477
  have htrace : WordTrace (prefixWord ++ tailWord_5254477) baseStart_5254477 baseEnd_5254477 := by
    simpa [prefixWord, tailWord_5254477, baseEnd_5254477] using wordTrace_append hprefix tailTrace_5254477
  have hstable : (prefixWord ++ tailWord_5254477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254477).length < 2 ^ (prefixWord ++ tailWord_5254477).sum := by decide
  have hdescent : baseEnd_5254477 < baseStart_5254477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254496 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 4, 2, 2]
def baseStart_5254496 : Nat := 118140960795 + 5254496 * 2 ^ 59
def prefixEnd_5254496 : Nat := 4983230072969 + 3 ^ 40 * 5254496 * 2
def baseEnd_5254496 : Nat := 2698082045127178993935019

theorem tailTrace_5254496 : CollatzResearch.WordTrace tailWord_5254496 prefixEnd_5254496 2698082045127178993935019 := by
  unfold tailWord_5254496
  simp only [CollatzResearch.WordTrace]
  refine ⟨95823606785932931658263671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127764809047910575544351561 95823606785932931658263671)
  ·
    refine ⟨143735410178899397487395507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95823606785932931658263671 143735410178899397487395507)
    ·
      refine ⟨215603115268349096231093261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143735410178899397487395507 215603115268349096231093261)
      ·
        refine ⟨80851168225630911086659973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215603115268349096231093261 80851168225630911086659973)
        ·
          refine ⟨15159594042305795828748745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80851168225630911086659973 15159594042305795828748745)
          ·
            refine ⟨11369695531729346871561559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15159594042305795828748745 11369695531729346871561559)
            ·
              refine ⟨17054543297594020307342339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11369695531729346871561559 17054543297594020307342339)
              ·
                refine ⟨25581814946391030461013509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17054543297594020307342339 25581814946391030461013509)
                ·
                  refine ⟨4796590302448318211440033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25581814946391030461013509 4796590302448318211440033)
                  ·
                    refine ⟨3597442726836238658580025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796590302448318211440033 3597442726836238658580025)
                    ·
                      refine ⟨2698082045127178993935019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597442726836238658580025 2698082045127178993935019)
                      ·
                        rfl

theorem cell23_5254496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_5254496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254496 prefixEnd_5254496 := by exact prefixLift 5254496
  have htrace : WordTrace (prefixWord ++ tailWord_5254496) baseStart_5254496 baseEnd_5254496 := by
    simpa [prefixWord, tailWord_5254496, baseEnd_5254496] using wordTrace_append hprefix tailTrace_5254496
  have hstable : (prefixWord ++ tailWord_5254496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254496).length < 2 ^ (prefixWord ++ tailWord_5254496).sum := by decide
  have hdescent : baseEnd_5254496 < baseStart_5254496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254512 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_5254512 : Nat := 118140960795 + 5254512 * 2 ^ 59
def prefixEnd_5254512 : Nat := 4983230072969 + 3 ^ 40 * 5254512 * 2
def baseEnd_5254512 : Nat := 2698090260817650931334945

theorem tailTrace_5254512 : CollatzResearch.WordTrace tailWord_5254512 prefixEnd_5254512 2698090260817650931334945 := by
  unfold tailWord_5254512
  simp only [CollatzResearch.WordTrace]
  refine ⟨95823898569903949024554895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127765198093205265366073193 95823898569903949024554895)
  ·
    refine ⟨143735847854855923536832343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95823898569903949024554895 143735847854855923536832343)
    ·
      refine ⟨215603771782283885305248515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143735847854855923536832343 215603771782283885305248515)
      ·
        refine ⟨323405657673425827957872773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215603771782283885305248515 323405657673425827957872773)
        ·
          refine ⟨60638560813767342742101145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323405657673425827957872773 60638560813767342742101145)
          ·
            refine ⟨45478920610325507056575859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60638560813767342742101145 45478920610325507056575859)
            ·
              refine ⟨68218380915488260584863789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45478920610325507056575859 68218380915488260584863789)
              ·
                refine ⟨25581892843308097719323921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68218380915488260584863789 25581892843308097719323921)
                ·
                  refine ⟨19186419632481073289492941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25581892843308097719323921 19186419632481073289492941)
                  ·
                    refine ⟨7194907362180402483559853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19186419632481073289492941 7194907362180402483559853)
                    ·
                      refine ⟨2698090260817650931334945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194907362180402483559853 2698090260817650931334945)
                      ·
                        rfl

theorem cell23_5254512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_5254512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254512 prefixEnd_5254512 := by exact prefixLift 5254512
  have htrace : WordTrace (prefixWord ++ tailWord_5254512) baseStart_5254512 baseEnd_5254512 := by
    simpa [prefixWord, tailWord_5254512, baseEnd_5254512] using wordTrace_append hprefix tailTrace_5254512
  have hstable : (prefixWord ++ tailWord_5254512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254512).length < 2 ^ (prefixWord ++ tailWord_5254512).sum := by decide
  have hdescent : baseEnd_5254512 < baseStart_5254512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254532 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_5254532 : Nat := 118140960795 + 5254532 * 2 ^ 59
def prefixEnd_5254532 : Nat := 4983230072969 + 3 ^ 40 * 5254532 * 2
def baseEnd_5254532 : Nat := 899366843476913617694951

theorem tailTrace_5254532 : CollatzResearch.WordTrace tailWord_5254532 prefixEnd_5254532 899366843476913617694951 := by
  unfold tailWord_5254532
  simp only [CollatzResearch.WordTrace]
  refine ⟨95824263299867720732418925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127765684399823627643225233 95824263299867720732418925)
  ·
    refine ⟨35934098737450395274657097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95824263299867720732418925 35934098737450395274657097)
    ·
      refine ⟨26950574053087796455992823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35934098737450395274657097 26950574053087796455992823)
      ·
        refine ⟨40425861079631694683989235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26950574053087796455992823 40425861079631694683989235)
        ·
          refine ⟨60638791619447542025983853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40425861079631694683989235 60638791619447542025983853)
          ·
            refine ⟨22739546857292828259743945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60638791619447542025983853 22739546857292828259743945)
            ·
              refine ⟨17054660142969621194807959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22739546857292828259743945 17054660142969621194807959)
              ·
                refine ⟨25581990214454431792211939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17054660142969621194807959 25581990214454431792211939)
                ·
                  refine ⟨38372985321681647688317909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25581990214454431792211939 38372985321681647688317909)
                  ·
                    refine ⟨899366843476913617694951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38372985321681647688317909 899366843476913617694951)
                    ·
                      rfl

theorem cell23_5254532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_5254532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254532 prefixEnd_5254532 := by exact prefixLift 5254532
  have htrace : WordTrace (prefixWord ++ tailWord_5254532) baseStart_5254532 baseEnd_5254532 := by
    simpa [prefixWord, tailWord_5254532, baseEnd_5254532] using wordTrace_append hprefix tailTrace_5254532
  have hstable : (prefixWord ++ tailWord_5254532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254532).length < 2 ^ (prefixWord ++ tailWord_5254532).sum := by decide
  have hdescent : baseEnd_5254532 < baseStart_5254532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254536 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 5]
def baseStart_5254536 : Nat := 118140960795 + 5254536 * 2 ^ 59
def prefixEnd_5254536 : Nat := 4983230072969 + 3 ^ 40 * 5254536 * 2
def baseEnd_5254536 : Nat := 299789176039262093048315

theorem tailTrace_5254536 : CollatzResearch.WordTrace tailWord_5254536 prefixEnd_5254536 299789176039262093048315 := by
  unfold tailWord_5254536
  simp only [CollatzResearch.WordTrace]
  refine ⟨95824336245860475073991731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127765781661147300098655641 95824336245860475073991731)
  ·
    refine ⟨143736504368790712610987597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95824336245860475073991731 143736504368790712610987597)
    ·
      refine ⟨53901189138296517229120349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143736504368790712610987597 53901189138296517229120349)
      ·
        refine ⟨20212945926861193960920131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53901189138296517229120349 20212945926861193960920131)
        ·
          refine ⟨30319418890291790941380197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20212945926861193960920131 30319418890291790941380197)
          ·
            refine ⟨5684891041929710801508787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30319418890291790941380197 5684891041929710801508787)
            ·
              refine ⟨8527336562894566202263181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684891041929710801508787 8527336562894566202263181)
              ·
                refine ⟨3197751211085462325848693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8527336562894566202263181 3197751211085462325848693)
                ·
                  refine ⟨299789176039262093048315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3197751211085462325848693 299789176039262093048315)
                  ·
                    rfl

theorem cell23_5254536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 5].length) (baseStart_5254536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254536 prefixEnd_5254536 := by exact prefixLift 5254536
  have htrace : WordTrace (prefixWord ++ tailWord_5254536) baseStart_5254536 baseEnd_5254536 := by
    simpa [prefixWord, tailWord_5254536, baseEnd_5254536] using wordTrace_append hprefix tailTrace_5254536
  have hstable : (prefixWord ++ tailWord_5254536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254536).length < 2 ^ (prefixWord ++ tailWord_5254536).sum := by decide
  have hdescent : baseEnd_5254536 < baseStart_5254536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254545 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_5254545 : Nat := 118140960795 + 5254545 * 2 ^ 59
def prefixEnd_5254545 : Nat := 4983230072969 + 3 ^ 40 * 5254545 * 2
def baseEnd_5254545 : Nat := 899369068559749767407431

theorem tailTrace_5254545 : CollatzResearch.WordTrace tailWord_5254545 prefixEnd_5254545 899369068559749767407431 := by
  unfold tailWord_5254545
  simp only [CollatzResearch.WordTrace]
  refine ⟨191649000748688344685061089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127766000499125563123374059 191649000748688344685061089)
  ·
    refine ⟨143736750561516258513795817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191649000748688344685061089 143736750561516258513795817)
    ·
      refine ⟨107802562921137193885346863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143736750561516258513795817 107802562921137193885346863)
      ·
        refine ⟨161703844381705790828020295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107802562921137193885346863 161703844381705790828020295)
        ·
          refine ⟨242555766572558686242030443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161703844381705790828020295 242555766572558686242030443)
          ·
            refine ⟨363833649858838029363045665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242555766572558686242030443 363833649858838029363045665)
            ·
              refine ⟨272875237394128522022284249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363833649858838029363045665 272875237394128522022284249)
              ·
                refine ⟨204656428045596391516713187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272875237394128522022284249 204656428045596391516713187)
                ·
                  refine ⟨306984642068394587275069781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204656428045596391516713187 306984642068394587275069781)
                  ·
                    refine ⟨899369068559749767407431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 306984642068394587275069781 899369068559749767407431)
                    ·
                      rfl

theorem cell23_5254545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_5254545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254545 prefixEnd_5254545 := by exact prefixLift 5254545
  have htrace : WordTrace (prefixWord ++ tailWord_5254545) baseStart_5254545 baseEnd_5254545 := by
    simpa [prefixWord, tailWord_5254545, baseEnd_5254545] using wordTrace_append hprefix tailTrace_5254545
  have hstable : (prefixWord ++ tailWord_5254545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254545).length < 2 ^ (prefixWord ++ tailWord_5254545).sum := by decide
  have hdescent : baseEnd_5254545 < baseStart_5254545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254572 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_5254572 : Nat := 118140960795 + 5254572 * 2 ^ 59
def prefixEnd_5254572 : Nat := 4983230072969 + 3 ^ 40 * 5254572 * 2
def baseEnd_5254572 : Nat := 2698121069656920696584669

theorem tailTrace_5254572 : CollatzResearch.WordTrace tailWord_5254572 prefixEnd_5254572 2698121069656920696584669 := by
  unfold tailWord_5254572
  simp only [CollatzResearch.WordTrace]
  refine ⟨95824992759795264148146985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127766657013060352197529313 95824992759795264148146985)
  ·
    refine ⟨71868744569846448111110239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95824992759795264148146985 71868744569846448111110239)
    ·
      refine ⟨107803116854769672166665359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71868744569846448111110239 107803116854769672166665359)
      ·
        refine ⟨161704675282154508249998039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107803116854769672166665359 161704675282154508249998039)
        ·
          refine ⟨242557012923231762374997059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161704675282154508249998039 242557012923231762374997059)
          ·
            refine ⟨363835519384847643562495589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242557012923231762374997059 363835519384847643562495589)
            ·
              refine ⟨68219159884658933167967923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 363835519384847643562495589 68219159884658933167967923)
              ·
                refine ⟨102328739826988399751951885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68219159884658933167967923 102328739826988399751951885)
                ·
                  refine ⟨38373277435120649906981957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102328739826988399751951885 38373277435120649906981957)
                  ·
                    refine ⟨7194989519085121857559117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38373277435120649906981957 7194989519085121857559117)
                    ·
                      refine ⟨2698121069656920696584669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7194989519085121857559117 2698121069656920696584669)
                      ·
                        rfl

theorem cell23_5254572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_5254572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254572 prefixEnd_5254572 := by exact prefixLift 5254572
  have htrace : WordTrace (prefixWord ++ tailWord_5254572) baseStart_5254572 baseEnd_5254572 := by
    simpa [prefixWord, tailWord_5254572, baseEnd_5254572] using wordTrace_append hprefix tailTrace_5254572
  have hstable : (prefixWord ++ tailWord_5254572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254572).length < 2 ^ (prefixWord ++ tailWord_5254572).sum := by decide
  have hdescent : baseEnd_5254572 < baseStart_5254572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254632 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5254632 : Nat := 118140960795 + 5254632 * 2 ^ 59
def prefixEnd_5254632 : Nat := 4983230072969 + 3 ^ 40 * 5254632 * 2
def baseEnd_5254632 : Nat := 2698151878496190461834393

theorem tailTrace_5254632 : CollatzResearch.WordTrace tailWord_5254632 prefixEnd_5254632 2698151878496190461834393 := by
  unfold tailWord_5254632
  simp only [CollatzResearch.WordTrace]
  refine ⟨95826086949686579271739075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127768115932915439028985433 95826086949686579271739075)
  ·
    refine ⟨143739130424529868907608613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95826086949686579271739075 143739130424529868907608613)
    ·
      refine ⟨26951086954599350420176615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143739130424529868907608613 26951086954599350420176615)
      ·
        refine ⟨40426630431899025630264923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26951086954599350420176615 40426630431899025630264923)
        ·
          refine ⟨60639945647848538445397385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40426630431899025630264923 60639945647848538445397385)
          ·
            refine ⟨45479959235886403834048039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60639945647848538445397385 45479959235886403834048039)
            ·
              refine ⟨68219938853829605751072059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45479959235886403834048039 68219938853829605751072059)
              ·
                refine ⟨102329908280744408626608089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68219938853829605751072059 102329908280744408626608089)
                ·
                  refine ⟨76747431210558306469956067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102329908280744408626608089 76747431210558306469956067)
                  ·
                    refine ⟨115121146815837459704934101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76747431210558306469956067 115121146815837459704934101)
                    ·
                      refine ⟨2698151878496190461834393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115121146815837459704934101 2698151878496190461834393)
                      ·
                        rfl

theorem cell23_5254632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5254632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254632 prefixEnd_5254632 := by exact prefixLift 5254632
  have htrace : WordTrace (prefixWord ++ tailWord_5254632) baseStart_5254632 baseEnd_5254632 := by
    simpa [prefixWord, tailWord_5254632, baseEnd_5254632] using wordTrace_append hprefix tailTrace_5254632
  have hstable : (prefixWord ++ tailWord_5254632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254632).length < 2 ^ (prefixWord ++ tailWord_5254632).sum := by decide
  have hdescent : baseEnd_5254632 < baseStart_5254632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254653 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_5254653 : Nat := 118140960795 + 5254653 * 2 ^ 59
def prefixEnd_5254653 : Nat := 4983230072969 + 3 ^ 40 * 5254653 * 2
def baseEnd_5254653 : Nat := 2698162661589934879671797

theorem tailTrace_5254653 : CollatzResearch.WordTrace tailWord_5254653 prefixEnd_5254653 2698162661589934879671797 := by
  unfold tailWord_5254653
  simp only [CollatzResearch.WordTrace]
  refine ⟨191652939832297079129992613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127768626554864719419995075 191652939832297079129992613)
  ·
    refine ⟨35934926218555702336873615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191652939832297079129992613 35934926218555702336873615)
    ·
      refine ⟨53902389327833553505310423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35934926218555702336873615 53902389327833553505310423)
      ·
        refine ⟨80853583991750330257965635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53902389327833553505310423 80853583991750330257965635)
        ·
          refine ⟨121280375987625495386948453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80853583991750330257965635 121280375987625495386948453)
          ·
            refine ⟨22740070497679780385052835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121280375987625495386948453 22740070497679780385052835)
            ·
              refine ⟨34110105746519670577579253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22740070497679780385052835 34110105746519670577579253)
              ·
                refine ⟨3197822413736219116648055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34110105746519670577579253 3197822413736219116648055)
                ·
                  refine ⟨4796733620604328674972083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197822413736219116648055 4796733620604328674972083)
                  ·
                    refine ⟨7195100430906493012458125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796733620604328674972083 7195100430906493012458125)
                    ·
                      refine ⟨2698162661589934879671797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195100430906493012458125 2698162661589934879671797)
                      ·
                        rfl

theorem cell23_5254653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_5254653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254653 prefixEnd_5254653 := by exact prefixLift 5254653
  have htrace : WordTrace (prefixWord ++ tailWord_5254653) baseStart_5254653 baseEnd_5254653 := by
    simpa [prefixWord, tailWord_5254653, baseEnd_5254653] using wordTrace_append hprefix tailTrace_5254653
  have hstable : (prefixWord ++ tailWord_5254653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254653).length < 2 ^ (prefixWord ++ tailWord_5254653).sum := by decide
  have hdescent : baseEnd_5254653 < baseStart_5254653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254682 : List Nat := [3, 1, 1, 3, 1, 1, 1, 12]
def baseStart_5254682 : Nat := 118140960795 + 5254682 * 2 ^ 59
def prefixEnd_5254682 : Nat := 4983230072969 + 3 ^ 40 * 5254682 * 2
def baseEnd_5254682 : Nat := 99932501945515380229969

theorem tailTrace_5254682 : CollatzResearch.WordTrace tailWord_5254682 prefixEnd_5254682 99932501945515380229969 := by
  unfold tailWord_5254682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47913499387298004270699575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127769331699461344721865533 47913499387298004270699575)
  ·
    refine ⟨71870249080947006406049363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47913499387298004270699575 71870249080947006406049363)
    ·
      refine ⟨107805373621420509609074045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71870249080947006406049363 107805373621420509609074045)
      ·
        refine ⟨40427015108032691103402767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107805373621420509609074045 40427015108032691103402767)
        ·
          refine ⟨60640522662049036655104151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40427015108032691103402767 60640522662049036655104151)
          ·
            refine ⟨90960783993073554982656227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60640522662049036655104151 90960783993073554982656227)
            ·
              refine ⟨136441175989610332473984341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90960783993073554982656227 136441175989610332473984341)
              ·
                refine ⟨99932501945515380229969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 136441175989610332473984341 99932501945515380229969)
                ·
                  rfl

theorem cell23_5254682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_5254682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254682 prefixEnd_5254682 := by exact prefixLift 5254682
  have htrace : WordTrace (prefixWord ++ tailWord_5254682) baseStart_5254682 baseEnd_5254682 := by
    simpa [prefixWord, tailWord_5254682, baseEnd_5254682] using wordTrace_append hprefix tailTrace_5254682
  have hstable : (prefixWord ++ tailWord_5254682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254682).length < 2 ^ (prefixWord ++ tailWord_5254682).sum := by decide
  have hdescent : baseEnd_5254682 < baseStart_5254682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254689 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_5254689 : Nat := 118140960795 + 5254689 * 2 ^ 59
def prefixEnd_5254689 : Nat := 4983230072969 + 3 ^ 40 * 5254689 * 2
def baseEnd_5254689 : Nat := 2698181146893496738821631

theorem tailTrace_5254689 : CollatzResearch.WordTrace tailWord_5254689 prefixEnd_5254689 2698181146893496738821631 := by
  unfold tailWord_5254689
  simp only [CollatzResearch.WordTrace]
  refine ⟨191654252860166657278303121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127769501906777771518868747 191654252860166657278303121)
  ·
    refine ⟨143740689645124992958727341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191654252860166657278303121 143740689645124992958727341)
    ·
      refine ⟨53902758616921872359522753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143740689645124992958727341 53902758616921872359522753)
      ·
        refine ⟨40427068962691404269642065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53902758616921872359522753 40427068962691404269642065)
        ·
          refine ⟨30320301722018553202231549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40427068962691404269642065 30320301722018553202231549)
          ·
            refine ⟨11370113145756957450836831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30320301722018553202231549 11370113145756957450836831)
            ·
              refine ⟨17055169718635436176255247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11370113145756957450836831 17055169718635436176255247)
              ·
                refine ⟨25582754577953154264382871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17055169718635436176255247 25582754577953154264382871)
                ·
                  refine ⟨38374131866929731396574307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25582754577953154264382871 38374131866929731396574307)
                  ·
                    refine ⟨57561197800394597094861461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38374131866929731396574307 57561197800394597094861461)
                    ·
                      refine ⟨2698181146893496738821631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57561197800394597094861461 2698181146893496738821631)
                      ·
                        rfl

theorem cell23_5254689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_5254689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254689 prefixEnd_5254689 := by exact prefixLift 5254689
  have htrace : WordTrace (prefixWord ++ tailWord_5254689) baseStart_5254689 baseEnd_5254689 := by
    simpa [prefixWord, tailWord_5254689, baseEnd_5254689] using wordTrace_append hprefix tailTrace_5254689
  have hstable : (prefixWord ++ tailWord_5254689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254689).length < 2 ^ (prefixWord ++ tailWord_5254689).sum := by decide
  have hdescent : baseEnd_5254689 < baseStart_5254689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254716 : List Nat := [2, 2, 2, 2, 5, 1, 9]
def baseStart_5254716 : Nat := 118140960795 + 5254716 * 2 ^ 59
def prefixEnd_5254716 : Nat := 4983230072969 + 3 ^ 40 * 5254716 * 2
def baseEnd_5254716 : Nat := 33311049516928001644247

theorem tailTrace_5254716 : CollatzResearch.WordTrace tailWord_5254716 prefixEnd_5254716 33311049516928001644247 := by
  unfold tailWord_5254716
  simp only [CollatzResearch.WordTrace]
  refine ⟨95827618815534420444768001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127770158420712560593024001 95827618815534420444768001)
  ·
    refine ⟨71870714111650815333576001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95827618815534420444768001 71870714111650815333576001)
    ·
      refine ⟨53903035583738111500182001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71870714111650815333576001 53903035583738111500182001)
      ·
        refine ⟨40427276687803583625136501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53903035583738111500182001 40427276687803583625136501)
        ·
          refine ⟨3790057189481585964856547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40427276687803583625136501 3790057189481585964856547)
          ·
            refine ⟨5685085784222378947284821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790057189481585964856547 5685085784222378947284821)
            ·
              refine ⟨33311049516928001644247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5685085784222378947284821 33311049516928001644247)
              ·
                rfl

theorem cell23_5254716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 9].length) (baseStart_5254716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254716 prefixEnd_5254716 := by exact prefixLift 5254716
  have htrace : WordTrace (prefixWord ++ tailWord_5254716) baseStart_5254716 baseEnd_5254716 := by
    simpa [prefixWord, tailWord_5254716, baseEnd_5254716] using wordTrace_append hprefix tailTrace_5254716
  have hstable : (prefixWord ++ tailWord_5254716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254716).length < 2 ^ (prefixWord ++ tailWord_5254716).sum := by decide
  have hdescent : baseEnd_5254716 < baseStart_5254716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254727 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_5254727 : Nat := 118140960795 + 5254727 * 2 ^ 59
def prefixEnd_5254727 : Nat := 4983230072969 + 3 ^ 40 * 5254727 * 2
def baseEnd_5254727 : Nat := 2698200659158367590146457

theorem tailTrace_5254727 : CollatzResearch.WordTrace tailWord_5254727 prefixEnd_5254727 2698200659158367590146457 := by
  unfold tailWord_5254727
  simp only [CollatzResearch.WordTrace]
  refine ⟨191655638834028989768186435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127770425889352659845457623 191655638834028989768186435)
  ·
    refine ⟨287483458251043484652279653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191655638834028989768186435 287483458251043484652279653)
    ·
      refine ⟨53903148422070653372302435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287483458251043484652279653 53903148422070653372302435)
      ·
        refine ⟨80854722633105980058453653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53903148422070653372302435 80854722633105980058453653)
        ·
          refine ⟨3790065123426842815240015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80854722633105980058453653 3790065123426842815240015)
          ·
            refine ⟨5685097685140264222860023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790065123426842815240015 5685097685140264222860023)
            ·
              refine ⟨8527646527710396334290035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685097685140264222860023 8527646527710396334290035)
              ·
                refine ⟨12791469791565594501435053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8527646527710396334290035 12791469791565594501435053)
                ·
                  refine ⟨4796801171837097938038145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12791469791565594501435053 4796801171837097938038145)
                  ·
                    refine ⟨3597600878877823453528609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796801171837097938038145 3597600878877823453528609)
                    ·
                      refine ⟨2698200659158367590146457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597600878877823453528609 2698200659158367590146457)
                      ·
                        rfl

theorem cell23_5254727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_5254727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254727 prefixEnd_5254727 := by exact prefixLift 5254727
  have htrace : WordTrace (prefixWord ++ tailWord_5254727) baseStart_5254727 baseEnd_5254727 := by
    simpa [prefixWord, tailWord_5254727, baseEnd_5254727] using wordTrace_append hprefix tailTrace_5254727
  have hstable : (prefixWord ++ tailWord_5254727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254727).length < 2 ^ (prefixWord ++ tailWord_5254727).sum := by decide
  have hdescent : baseEnd_5254727 < baseStart_5254727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254736 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 3, 3, 2]
def baseStart_5254736 : Nat := 118140960795 + 5254736 * 2 ^ 59
def prefixEnd_5254736 : Nat := 4983230072969 + 3 ^ 40 * 5254736 * 2
def baseEnd_5254736 : Nat := 2698205280484258054933915

theorem tailTrace_5254736 : CollatzResearch.WordTrace tailWord_5254736 prefixEnd_5254736 2698205280484258054933915 := by
  unfold tailWord_5254736
  simp only [CollatzResearch.WordTrace]
  refine ⟨95827983545498192152632031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127770644727330922870176041 95827983545498192152632031)
  ·
    refine ⟨143741975318247288228948047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95827983545498192152632031 143741975318247288228948047)
    ·
      refine ⟨215612962977370932343422071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143741975318247288228948047 215612962977370932343422071)
      ·
        refine ⟨323419444466056398515133107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215612962977370932343422071 323419444466056398515133107)
        ·
          refine ⟨485129166699084597772699661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323419444466056398515133107 485129166699084597772699661)
          ·
            refine ⟨181923437512156724164762373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 485129166699084597772699661 181923437512156724164762373)
            ·
              refine ⟨34110644533529385780892945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181923437512156724164762373 34110644533529385780892945)
              ·
                refine ⟨25582983400147039335669709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34110644533529385780892945 25582983400147039335669709)
                ·
                  refine ⟨9593618775055139750876141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25582983400147039335669709 9593618775055139750876141)
                  ·
                    refine ⟨3597607040645677406578553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9593618775055139750876141 3597607040645677406578553)
                    ·
                      refine ⟨2698205280484258054933915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597607040645677406578553 2698205280484258054933915)
                      ·
                        rfl

theorem cell23_5254736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 3, 2].length) (baseStart_5254736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254736 prefixEnd_5254736 := by exact prefixLift 5254736
  have htrace : WordTrace (prefixWord ++ tailWord_5254736) baseStart_5254736 baseEnd_5254736 := by
    simpa [prefixWord, tailWord_5254736, baseEnd_5254736] using wordTrace_append hprefix tailTrace_5254736
  have hstable : (prefixWord ++ tailWord_5254736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254736).length < 2 ^ (prefixWord ++ tailWord_5254736).sum := by decide
  have hdescent : baseEnd_5254736 < baseStart_5254736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254743 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_5254743 : Nat := 118140960795 + 5254743 * 2 ^ 59
def prefixEnd_5254743 : Nat := 4983230072969 + 3 ^ 40 * 5254743 * 2
def baseEnd_5254743 : Nat := 2698208874848839527546383

theorem tailTrace_5254743 : CollatzResearch.WordTrace tailWord_5254743 prefixEnd_5254743 2698208874848839527546383 := by
  unfold tailWord_5254743
  simp only [CollatzResearch.WordTrace]
  refine ⟨191656222401971024500768883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127770814934647349667179255 191656222401971024500768883)
  ·
    refine ⟨287484333602956536751153325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191656222401971024500768883 287484333602956536751153325)
    ·
      refine ⟨107806625101108701281682497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287484333602956536751153325 107806625101108701281682497)
      ·
        refine ⟨80854968825831525961261873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107806625101108701281682497 80854968825831525961261873)
        ·
          refine ⟨60641226619373644470946405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80854968825831525961261873 60641226619373644470946405)
          ·
            refine ⟨11370229991132558338302451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60641226619373644470946405 11370229991132558338302451)
            ·
              refine ⟨17055344986698837507453677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11370229991132558338302451 17055344986698837507453677)
              ·
                refine ⟨6395754370012064065295129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17055344986698837507453677 6395754370012064065295129)
                ·
                  refine ⟨4796815777509048048971347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395754370012064065295129 4796815777509048048971347)
                  ·
                    refine ⟨7195223666263572073457021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796815777509048048971347 7195223666263572073457021)
                    ·
                      refine ⟨2698208874848839527546383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195223666263572073457021 2698208874848839527546383)
                      ·
                        rfl

theorem cell23_5254743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_5254743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254743 prefixEnd_5254743 := by exact prefixLift 5254743
  have htrace : WordTrace (prefixWord ++ tailWord_5254743) baseStart_5254743 baseEnd_5254743 := by
    simpa [prefixWord, tailWord_5254743, baseEnd_5254743] using wordTrace_append hprefix tailTrace_5254743
  have hstable : (prefixWord ++ tailWord_5254743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254743).length < 2 ^ (prefixWord ++ tailWord_5254743).sum := by decide
  have hdescent : baseEnd_5254743 < baseStart_5254743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254769 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_5254769 : Nat := 118140960795 + 5254769 * 2 ^ 59
def prefixEnd_5254769 : Nat := 4983230072969 + 3 ^ 40 * 5254769 * 2
def baseEnd_5254769 : Nat := 2698222225345856425821263

theorem tailTrace_5254769 : CollatzResearch.WordTrace tailWord_5254769 prefixEnd_5254769 2698222225345856425821263 := by
  unfold tailWord_5254769
  simp only [CollatzResearch.WordTrace]
  refine ⟨191657170699876830941215361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127771447133251220627476907 191657170699876830941215361)
  ·
    refine ⟨143742878024907623205911521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191657170699876830941215361 143742878024907623205911521)
    ·
      refine ⟨107807158518680717404433641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143742878024907623205911521 107807158518680717404433641)
      ·
        refine ⟨80855368889010538053325231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107807158518680717404433641 80855368889010538053325231)
        ·
          refine ⟨121283053333515807079987847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80855368889010538053325231 121283053333515807079987847)
          ·
            refine ⟨181924580000273710619981771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121283053333515807079987847 181924580000273710619981771)
            ·
              refine ⟨272886870000410565929972657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181924580000273710619981771 272886870000410565929972657)
              ·
                refine ⟨204665152500307924447479493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272886870000410565929972657 204665152500307924447479493)
                ·
                  refine ⟨38374716093807735833902405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204665152500307924447479493 38374716093807735833902405)
                  ·
                    refine ⟨7195259267588950468856701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38374716093807735833902405 7195259267588950468856701)
                    ·
                      refine ⟨2698222225345856425821263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195259267588950468856701 2698222225345856425821263)
                      ·
                        rfl

theorem cell23_5254769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_5254769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254769 prefixEnd_5254769 := by exact prefixLift 5254769
  have htrace : WordTrace (prefixWord ++ tailWord_5254769) baseStart_5254769 baseEnd_5254769 := by
    simpa [prefixWord, tailWord_5254769, baseEnd_5254769] using wordTrace_append hprefix tailTrace_5254769
  have hstable : (prefixWord ++ tailWord_5254769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254769).length < 2 ^ (prefixWord ++ tailWord_5254769).sum := by decide
  have hdescent : baseEnd_5254769 < baseStart_5254769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254779 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4]
def baseStart_5254779 : Nat := 118140960795 + 5254779 * 2 ^ 59
def prefixEnd_5254779 : Nat := 4983230072969 + 3 ^ 40 * 5254779 * 2
def baseEnd_5254779 : Nat := 2698227360152401386696217

theorem tailTrace_5254779 : CollatzResearch.WordTrace tailWord_5254779 prefixEnd_5254779 2698227360152401386696217 := by
  unfold tailWord_5254779
  simp only [CollatzResearch.WordTrace]
  refine ⟨191657535429840602649079391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127771690286560401766052927 191657535429840602649079391)
  ·
    refine ⟨287486303144760903973619087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191657535429840602649079391 287486303144760903973619087)
    ·
      refine ⟨431229454717141355960428631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287486303144760903973619087 431229454717141355960428631)
      ·
        refine ⟨646844182075712033940642947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431229454717141355960428631 646844182075712033940642947)
        ·
          refine ⟨970266273113568050910964421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646844182075712033940642947 970266273113568050910964421)
          ·
            refine ⟨181924926208794009545805829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 970266273113568050910964421 181924926208794009545805829)
            ·
              refine ⟨34110923664148876789838593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181924926208794009545805829 34110923664148876789838593)
              ·
                refine ⟨25583192748111657592378945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34110923664148876789838593 25583192748111657592378945)
                ·
                  refine ⟨19187394561083743194284209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25583192748111657592378945 19187394561083743194284209)
                  ·
                    refine ⟨14390545920812807395713157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19187394561083743194284209 14390545920812807395713157)
                    ·
                      refine ⟨2698227360152401386696217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14390545920812807395713157 2698227360152401386696217)
                      ·
                        rfl

theorem cell23_5254779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_5254779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254779 prefixEnd_5254779 := by exact prefixLift 5254779
  have htrace : WordTrace (prefixWord ++ tailWord_5254779) baseStart_5254779 baseEnd_5254779 := by
    simpa [prefixWord, tailWord_5254779, baseEnd_5254779] using wordTrace_append hprefix tailTrace_5254779
  have hstable : (prefixWord ++ tailWord_5254779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254779).length < 2 ^ (prefixWord ++ tailWord_5254779).sum := by decide
  have hdescent : baseEnd_5254779 < baseStart_5254779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254789 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 7]
def baseStart_5254789 : Nat := 118140960795 + 5254789 * 2 ^ 59
def prefixEnd_5254789 : Nat := 4983230072969 + 3 ^ 40 * 5254789 * 2
def baseEnd_5254789 : Nat := 299803610550994038619019

theorem tailTrace_5254789 : CollatzResearch.WordTrace tailWord_5254789 prefixEnd_5254789 299803610550994038619019 := by
  unfold tailWord_5254789
  simp only [CollatzResearch.WordTrace]
  refine ⟨191657900159804374356943421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127771933439869582904628947 191657900159804374356943421)
  ·
    refine ⟨71871712559926640383853783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191657900159804374356943421 71871712559926640383853783)
    ·
      refine ⟨107807568839889960575780675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71871712559926640383853783 107807568839889960575780675)
      ·
        refine ⟨161711353259834940863671013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107807568839889960575780675 161711353259834940863671013)
        ·
          refine ⟨30320878736219051411938315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161711353259834940863671013 30320878736219051411938315)
          ·
            refine ⟨45481318104328577117907473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30320878736219051411938315 45481318104328577117907473)
            ·
              refine ⟨34110988578246432838430605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45481318104328577117907473 34110988578246432838430605)
              ·
                refine ⟨12791620716842412314411477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34110988578246432838430605 12791620716842412314411477)
                ·
                  refine ⟨299803610550994038619019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12791620716842412314411477 299803610550994038619019)
                  ·
                    rfl

theorem cell23_5254789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_5254789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254789 prefixEnd_5254789 := by exact prefixLift 5254789
  have htrace : WordTrace (prefixWord ++ tailWord_5254789) baseStart_5254789 baseEnd_5254789 := by
    simpa [prefixWord, tailWord_5254789, baseEnd_5254789] using wordTrace_append hprefix tailTrace_5254789
  have hstable : (prefixWord ++ tailWord_5254789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254789).length < 2 ^ (prefixWord ++ tailWord_5254789).sum := by decide
  have hdescent : baseEnd_5254789 < baseStart_5254789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254819 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 1, 7]
def baseStart_5254819 : Nat := 118140960795 + 5254819 * 2 ^ 59
def prefixEnd_5254819 : Nat := 4983230072969 + 3 ^ 40 * 5254819 * 2
def baseEnd_5254819 : Nat := 899415966459527076732011

theorem tailTrace_5254819 : CollatzResearch.WordTrace tailWord_5254819 prefixEnd_5254819 899415966459527076732011 := by
  unfold tailWord_5254819
  simp only [CollatzResearch.WordTrace]
  refine ⟨191658994349695689480535511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127772662899797126320357007 191658994349695689480535511)
  ·
    refine ⟨287488491524543534220803267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191658994349695689480535511 287488491524543534220803267)
    ·
      refine ⟨431232737286815301331204901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287488491524543534220803267 431232737286815301331204901)
      ·
        refine ⟨80856138241277868999600919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 431232737286815301331204901 80856138241277868999600919)
        ·
          refine ⟨121284207361916803499401379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80856138241277868999600919 121284207361916803499401379)
          ·
            refine ⟨181926311042875205249102069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121284207361916803499401379 181926311042875205249102069)
            ·
              refine ⟨17055591660269550492103319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181926311042875205249102069 17055591660269550492103319)
              ·
                refine ⟨25583387490404325738154979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17055591660269550492103319 25583387490404325738154979)
                ·
                  refine ⟨38375081235606488607232469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25583387490404325738154979 38375081235606488607232469)
                  ·
                    refine ⟨899415966459527076732011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38375081235606488607232469 899415966459527076732011)
                    ·
                      rfl

theorem cell23_5254819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 7].length) (baseStart_5254819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254819 prefixEnd_5254819 := by exact prefixLift 5254819
  have htrace : WordTrace (prefixWord ++ tailWord_5254819) baseStart_5254819 baseEnd_5254819 := by
    simpa [prefixWord, tailWord_5254819, baseEnd_5254819] using wordTrace_append hprefix tailTrace_5254819
  have hstable : (prefixWord ++ tailWord_5254819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254819).length < 2 ^ (prefixWord ++ tailWord_5254819).sum := by decide
  have hdescent : baseEnd_5254819 < baseStart_5254819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254879 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 10]
def baseStart_5254879 : Nat := 118140960795 + 5254879 * 2 ^ 59
def prefixEnd_5254879 : Nat := 4983230072969 + 3 ^ 40 * 5254879 * 2
def baseEnd_5254879 : Nat := 299808745357538999493973

theorem tailTrace_5254879 : CollatzResearch.WordTrace tailWord_5254879 prefixEnd_5254879 299808745357538999493973 := by
  unfold tailWord_5254879
  simp only [CollatzResearch.WordTrace]
  refine ⟨191661182729478319727719691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127774121819652213151813127 191661182729478319727719691)
  ·
    refine ⟨287491774094217479591579537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191661182729478319727719691 287491774094217479591579537)
    ·
      refine ⟨215618830570663109693684653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287491774094217479591579537 215618830570663109693684653)
      ·
        refine ⟨80857061463998666135131745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215618830570663109693684653 80857061463998666135131745)
        ·
          refine ⟨60642796097998999601348809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80857061463998666135131745 60642796097998999601348809)
          ·
            refine ⟨45482097073499249701011607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60642796097998999601348809 45482097073499249701011607)
            ·
              refine ⟨68223145610248874551517411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45482097073499249701011607 68223145610248874551517411)
              ·
                refine ⟨102334718415373311827276117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68223145610248874551517411 102334718415373311827276117)
                ·
                  refine ⟨299808745357538999493973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 102334718415373311827276117 299808745357538999493973)
                  ·
                    rfl

theorem cell23_5254879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 10].length) (baseStart_5254879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254879 prefixEnd_5254879 := by exact prefixLift 5254879
  have htrace : WordTrace (prefixWord ++ tailWord_5254879) baseStart_5254879 baseEnd_5254879 := by
    simpa [prefixWord, tailWord_5254879, baseEnd_5254879] using wordTrace_append hprefix tailTrace_5254879
  have hstable : (prefixWord ++ tailWord_5254879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254879).length < 2 ^ (prefixWord ++ tailWord_5254879).sum := by decide
  have hdescent : baseEnd_5254879 < baseStart_5254879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254893 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5254893 : Nat := 118140960795 + 5254893 * 2 ^ 59
def prefixEnd_5254893 : Nat := 4983230072969 + 3 ^ 40 * 5254893 * 2
def baseEnd_5254893 : Nat := 2698285896947013940670693

theorem tailTrace_5254893 : CollatzResearch.WordTrace tailWord_5254893 prefixEnd_5254893 2698285896947013940670693 := by
  unfold tailWord_5254893
  simp only [CollatzResearch.WordTrace]
  refine ⟨191661693351427600118729333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127774462234285066745819555 191661693351427600118729333)
  ·
    refine ⟨17968283751696337511130875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191661693351427600118729333 17968283751696337511130875)
    ·
      refine ⟨26952425627544506266696313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17968283751696337511130875 26952425627544506266696313)
      ·
        refine ⟨20214319220658379700022235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26952425627544506266696313 20214319220658379700022235)
        ·
          refine ⟨30321478830987569550033353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20214319220658379700022235 30321478830987569550033353)
          ·
            refine ⟨22741109123240677162525015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30321478830987569550033353 22741109123240677162525015)
            ·
              refine ⟨34111663684861015743787523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22741109123240677162525015 34111663684861015743787523)
              ·
                refine ⟨51167495527291523615681285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34111663684861015743787523 51167495527291523615681285)
                ·
                  refine ⟨9593905411367160677940241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51167495527291523615681285 9593905411367160677940241)
                  ·
                    refine ⟨7195429058525370508455181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9593905411367160677940241 7195429058525370508455181)
                    ·
                      refine ⟨2698285896947013940670693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195429058525370508455181 2698285896947013940670693)
                      ·
                        rfl

theorem cell23_5254893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5254893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254893 prefixEnd_5254893 := by exact prefixLift 5254893
  have htrace : WordTrace (prefixWord ++ tailWord_5254893) baseStart_5254893 baseEnd_5254893 := by
    simpa [prefixWord, tailWord_5254893, baseEnd_5254893] using wordTrace_append hprefix tailTrace_5254893
  have hstable : (prefixWord ++ tailWord_5254893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254893).length < 2 ^ (prefixWord ++ tailWord_5254893).sum := by decide
  have hdescent : baseEnd_5254893 < baseStart_5254893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254899 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_5254899 : Nat := 118140960795 + 5254899 * 2 ^ 59
def prefixEnd_5254899 : Nat := 4983230072969 + 3 ^ 40 * 5254899 * 2
def baseEnd_5254899 : Nat := 2698288977830940917195665

theorem tailTrace_5254899 : CollatzResearch.WordTrace tailWord_5254899 prefixEnd_5254899 2698288977830940917195665 := by
  unfold tailWord_5254899
  simp only [CollatzResearch.WordTrace]
  refine ⟨191661912189405863143447751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127774608126270575428965167 191661912189405863143447751)
  ·
    refine ⟨287492868284108794715171627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191661912189405863143447751 287492868284108794715171627)
    ·
      refine ⟨431239302426163192072757441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287492868284108794715171627 431239302426163192072757441)
      ·
        refine ⟨323429476819622394054568081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431239302426163192072757441 323429476819622394054568081)
        ·
          refine ⟨242572107614716795540926061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323429476819622394054568081 242572107614716795540926061)
          ·
            refine ⟨90964540355518798327847273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242572107614716795540926061 90964540355518798327847273)
            ·
              refine ⟨68223405266639098745885455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90964540355518798327847273 68223405266639098745885455)
              ·
                refine ⟨102335107899958648118828183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68223405266639098745885455 102335107899958648118828183)
                ·
                  refine ⟨153502661849937972178242275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102335107899958648118828183 153502661849937972178242275)
                  ·
                    refine ⟨230253992774906958267363413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153502661849937972178242275 230253992774906958267363413)
                    ·
                      refine ⟨2698288977830940917195665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230253992774906958267363413 2698288977830940917195665)
                      ·
                        rfl

theorem cell23_5254899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_5254899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254899 prefixEnd_5254899 := by exact prefixLift 5254899
  have htrace : WordTrace (prefixWord ++ tailWord_5254899) baseStart_5254899 baseEnd_5254899 := by
    simpa [prefixWord, tailWord_5254899, baseEnd_5254899] using wordTrace_append hprefix tailTrace_5254899
  have hstable : (prefixWord ++ tailWord_5254899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254899).length < 2 ^ (prefixWord ++ tailWord_5254899).sum := by decide
  have hdescent : baseEnd_5254899 < baseStart_5254899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254913 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 6]
def baseStart_5254913 : Nat := 118140960795 + 5254913 * 2 ^ 59
def prefixEnd_5254913 : Nat := 4983230072969 + 3 ^ 40 * 5254913 * 2
def baseEnd_5254913 : Nat := 299810685173344873602289

theorem tailTrace_5254913 : CollatzResearch.WordTrace tailWord_5254913 prefixEnd_5254913 299810685173344873602289 := by
  unfold tailWord_5254913
  simp only [CollatzResearch.WordTrace]
  refine ⟨191662422811355143534457393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127774948540903429022971595 191662422811355143534457393)
  ·
    refine ⟨143746817108516357650843045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191662422811355143534457393 143746817108516357650843045)
    ·
      refine ⟨26952528207846817059533071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143746817108516357650843045 26952528207846817059533071)
      ·
        refine ⟨40428792311770225589299607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26952528207846817059533071 40428792311770225589299607)
        ·
          refine ⟨60643188467655338383949411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40428792311770225589299607 60643188467655338383949411)
          ·
            refine ⟨90964782701483007575924117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60643188467655338383949411 90964782701483007575924117)
            ·
              refine ⟨4263974189132015980121443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90964782701483007575924117 4263974189132015980121443)
              ·
                refine ⟨6395961283698023970182165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263974189132015980121443 6395961283698023970182165)
                ·
                  refine ⟨299810685173344873602289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6395961283698023970182165 299810685173344873602289)
                  ·
                    rfl

theorem cell23_5254913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 6].length) (baseStart_5254913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254913 prefixEnd_5254913 := by exact prefixLift 5254913
  have htrace : WordTrace (prefixWord ++ tailWord_5254913) baseStart_5254913 baseEnd_5254913 := by
    simpa [prefixWord, tailWord_5254913, baseEnd_5254913] using wordTrace_append hprefix tailTrace_5254913
  have hstable : (prefixWord ++ tailWord_5254913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254913).length < 2 ^ (prefixWord ++ tailWord_5254913).sum := by decide
  have hdescent : baseEnd_5254913 < baseStart_5254913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254923 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 3]
def baseStart_5254923 : Nat := 118140960795 + 5254923 * 2 ^ 59
def prefixEnd_5254923 : Nat := 4983230072969 + 3 ^ 40 * 5254923 * 2
def baseEnd_5254923 : Nat := 2698301301366648823295555

theorem tailTrace_5254923 : CollatzResearch.WordTrace tailWord_5254923 prefixEnd_5254923 2698301301366648823295555 := by
  unfold tailWord_5254923
  simp only [CollatzResearch.WordTrace]
  refine ⟨191662787541318915242321423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127775191694212610161547615 191662787541318915242321423)
  ·
    refine ⟨287494181311978372863482135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191662787541318915242321423 287494181311978372863482135)
    ·
      refine ⟨431241271967967559295223203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287494181311978372863482135 431241271967967559295223203)
      ·
        refine ⟨646861907951951338942834805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431241271967967559295223203 646861907951951338942834805)
        ·
          refine ⟨60643303870495438025890763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 646861907951951338942834805 60643303870495438025890763)
          ·
            refine ⟨90964955805743157038836145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60643303870495438025890763 90964955805743157038836145)
            ·
              refine ⟨68223716854307367779127109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90964955805743157038836145 68223716854307367779127109)
              ·
                refine ⟨12791946910182631458586333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68223716854307367779127109 12791946910182631458586333)
                ·
                  refine ⟨4796980091318486796969875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12791946910182631458586333 4796980091318486796969875)
                  ·
                    refine ⟨7195470136977730195454813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796980091318486796969875 7195470136977730195454813)
                    ·
                      refine ⟨2698301301366648823295555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195470136977730195454813 2698301301366648823295555)
                      ·
                        rfl

theorem cell23_5254923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 3].length) (baseStart_5254923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254923 prefixEnd_5254923 := by exact prefixLift 5254923
  have htrace : WordTrace (prefixWord ++ tailWord_5254923) baseStart_5254923 baseEnd_5254923 := by
    simpa [prefixWord, tailWord_5254923, baseEnd_5254923] using wordTrace_append hprefix tailTrace_5254923
  have hstable : (prefixWord ++ tailWord_5254923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254923).length < 2 ^ (prefixWord ++ tailWord_5254923).sum := by decide
  have hdescent : baseEnd_5254923 < baseStart_5254923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254973 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_5254973 : Nat := 118140960795 + 5254973 * 2 ^ 59
def prefixEnd_5254973 : Nat := 4983230072969 + 3 ^ 40 * 5254973 * 2
def baseEnd_5254973 : Nat := 899442325133124542556775

theorem tailTrace_5254973 : CollatzResearch.WordTrace tailWord_5254973 prefixEnd_5254973 899442325133124542556775 := by
  unfold tailWord_5254973
  simp only [CollatzResearch.WordTrace]
  refine ⟨191664611191137773781641573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127776407460758515854427715 191664611191137773781641573)
  ·
    refine ⟨35937114598338332584057795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191664611191137773781641573 35937114598338332584057795)
    ·
      refine ⟨53905671897507498876086693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35937114598338332584057795 53905671897507498876086693)
      ·
        refine ⟨10107313480782656039266255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53905671897507498876086693 10107313480782656039266255)
        ·
          refine ⟨15160970221173984058899383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10107313480782656039266255 15160970221173984058899383)
          ·
            refine ⟨22741455331760976088349075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15160970221173984058899383 22741455331760976088349075)
            ·
              refine ⟨34112182997641464132523613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22741455331760976088349075 34112182997641464132523613)
              ·
                refine ⟨12792068624115549049696355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34112182997641464132523613 12792068624115549049696355)
                ·
                  refine ⟨19188102936173323574544533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12792068624115549049696355 19188102936173323574544533)
                  ·
                    refine ⟨899442325133124542556775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19188102936173323574544533 899442325133124542556775)
                    ·
                      rfl

theorem cell23_5254973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_5254973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254973 prefixEnd_5254973 := by exact prefixLift 5254973
  have htrace : WordTrace (prefixWord ++ tailWord_5254973) baseStart_5254973 baseEnd_5254973 := by
    simpa [prefixWord, tailWord_5254973, baseEnd_5254973] using wordTrace_append hprefix tailTrace_5254973
  have hstable : (prefixWord ++ tailWord_5254973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254973).length < 2 ^ (prefixWord ++ tailWord_5254973).sum := by decide
  have hdescent : baseEnd_5254973 < baseStart_5254973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254983 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_5254983 : Nat := 118140960795 + 5254983 * 2 ^ 59
def prefixEnd_5254983 : Nat := 4983230072969 + 3 ^ 40 * 5254983 * 2
def baseEnd_5254983 : Nat := 2698332110205918588545279

theorem tailTrace_5254983 : CollatzResearch.WordTrace tailWord_5254983 prefixEnd_5254983 2698332110205918588545279 := by
  unfold tailWord_5254983
  simp only [CollatzResearch.WordTrace]
  refine ⟨191664975921101545489505603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127776650614067696993003735 191664975921101545489505603)
  ·
    refine ⟨287497463881652318234258405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191664975921101545489505603 287497463881652318234258405)
    ·
      refine ⟨53905774477809809668923451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287497463881652318234258405 53905774477809809668923451)
      ·
        refine ⟨80858661716714714503385177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53905774477809809668923451 80858661716714714503385177)
        ·
          refine ⟨60643996287536035877538883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80858661716714714503385177 60643996287536035877538883)
          ·
            refine ⟨90965994431304053816308325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60643996287536035877538883 90965994431304053816308325)
            ·
              refine ⟨17056123955869510090557811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90965994431304053816308325 17056123955869510090557811)
              ·
                refine ⟨25584185933804265135836717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17056123955869510090557811 25584185933804265135836717)
                ·
                  refine ⟨9594069725176599425938769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25584185933804265135836717 9594069725176599425938769)
                  ·
                    refine ⟨7195552293882449569454077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9594069725176599425938769 7195552293882449569454077)
                    ·
                      refine ⟨2698332110205918588545279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195552293882449569454077 2698332110205918588545279)
                      ·
                        rfl

theorem cell23_5254983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_5254983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254983 prefixEnd_5254983 := by exact prefixLift 5254983
  have htrace : WordTrace (prefixWord ++ tailWord_5254983) baseStart_5254983 baseEnd_5254983 := by
    simpa [prefixWord, tailWord_5254983, baseEnd_5254983] using wordTrace_append hprefix tailTrace_5254983
  have hstable : (prefixWord ++ tailWord_5254983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254983).length < 2 ^ (prefixWord ++ tailWord_5254983).sum := by decide
  have hdescent : baseEnd_5254983 < baseStart_5254983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254993 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_5254993 : Nat := 118140960795 + 5254993 * 2 ^ 59
def prefixEnd_5254993 : Nat := 4983230072969 + 3 ^ 40 * 5254993 * 2
def baseEnd_5254993 : Nat := 2698337245012463549420233

theorem tailTrace_5254993 : CollatzResearch.WordTrace tailWord_5254993 prefixEnd_5254993 2698337245012463549420233 := by
  unfold tailWord_5254993
  simp only [CollatzResearch.WordTrace]
  refine ⟨191665340651065317197369633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127776893767376878131579755 191665340651065317197369633)
  ·
    refine ⟨143749005488298987898027225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191665340651065317197369633 143749005488298987898027225)
    ·
      refine ⟨107811754116224240923520419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143749005488298987898027225 107811754116224240923520419)
      ·
        refine ⟨161717631174336361385280629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107811754116224240923520419 161717631174336361385280629)
        ·
          refine ⟨15161027922594033879870059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161717631174336361385280629 15161027922594033879870059)
          ·
            refine ⟨22741541883891050819805089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15161027922594033879870059 22741541883891050819805089)
            ·
              refine ⟨17056156412918288114853817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22741541883891050819805089 17056156412918288114853817)
              ·
                refine ⟨12792117309688716086140363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17056156412918288114853817 12792117309688716086140363)
                ·
                  refine ⟨19188175964533074129210545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12792117309688716086140363 19188175964533074129210545)
                  ·
                    refine ⟨14391131973399805596907909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19188175964533074129210545 14391131973399805596907909)
                    ·
                      refine ⟨2698337245012463549420233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14391131973399805596907909 2698337245012463549420233)
                      ·
                        rfl

theorem cell23_5254993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_5254993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254993 prefixEnd_5254993 := by exact prefixLift 5254993
  have htrace : WordTrace (prefixWord ++ tailWord_5254993) baseStart_5254993 baseEnd_5254993 := by
    simpa [prefixWord, tailWord_5254993, baseEnd_5254993] using wordTrace_append hprefix tailTrace_5254993
  have hstable : (prefixWord ++ tailWord_5254993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254993).length < 2 ^ (prefixWord ++ tailWord_5254993).sum := by decide
  have hdescent : baseEnd_5254993 < baseStart_5254993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5254997 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_5254997 : Nat := 118140960795 + 5254997 * 2 ^ 59
def prefixEnd_5254997 : Nat := 4983230072969 + 3 ^ 40 * 5254997 * 2
def baseEnd_5254997 : Nat := 2698339298935081533770215

theorem tailTrace_5254997 : CollatzResearch.WordTrace tailWord_5254997 prefixEnd_5254997 2698339298935081533770215 := by
  unfold tailWord_5254997
  simp only [CollatzResearch.WordTrace]
  refine ⟨191665486543050825880515245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127776991028700550587010163 191665486543050825880515245)
  ·
    refine ⟨71874557453644059705193217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191665486543050825880515245 71874557453644059705193217)
    ·
      refine ⟨53905918090233044778894913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71874557453644059705193217 53905918090233044778894913)
      ·
        refine ⟨40429438567674783584171185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53905918090233044778894913 40429438567674783584171185)
        ·
          refine ⟨30322078925756087688128389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40429438567674783584171185 30322078925756087688128389)
          ·
            refine ⟨5685389798579266441524073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30322078925756087688128389 5685389798579266441524073)
            ·
              refine ⟨4264042348934449831143055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5685389798579266441524073 4264042348934449831143055)
              ·
                refine ⟨6396063523401674746714583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4264042348934449831143055 6396063523401674746714583)
                ·
                  refine ⟨9594095285102512120071875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396063523401674746714583 9594095285102512120071875)
                  ·
                    refine ⟨14391142927653768180107813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9594095285102512120071875 14391142927653768180107813)
                    ·
                      refine ⟨2698339298935081533770215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14391142927653768180107813 2698339298935081533770215)
                      ·
                        rfl

theorem cell23_5254997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_5254997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5254997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5254997 prefixEnd_5254997 := by exact prefixLift 5254997
  have htrace : WordTrace (prefixWord ++ tailWord_5254997) baseStart_5254997 baseEnd_5254997 := by
    simpa [prefixWord, tailWord_5254997, baseEnd_5254997] using wordTrace_append hprefix tailTrace_5254997
  have hstable : (prefixWord ++ tailWord_5254997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5254997).length < 2 ^ (prefixWord ++ tailWord_5254997).sum := by decide
  have hdescent : baseEnd_5254997 < baseStart_5254997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5254997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255048 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_5255048 : Nat := 118140960795 + 5255048 * 2 ^ 59
def prefixEnd_5255048 : Nat := 4983230072969 + 3 ^ 40 * 5255048 * 2
def baseEnd_5255048 : Nat := 2698365486448460834232481

theorem tailTrace_5255048 : CollatzResearch.WordTrace tailWord_5255048 prefixEnd_5255048 2698365486448460834232481 := by
  unfold tailWord_5255048
  simp only [CollatzResearch.WordTrace]
  refine ⟨95833673332933030795310899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127778231110577374393747865 95833673332933030795310899)
  ·
    refine ⟨143750509999399546192966349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95833673332933030795310899 143750509999399546192966349)
    ·
      refine ⟨53906441249774829822362381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143750509999399546192966349 53906441249774829822362381)
      ·
        refine ⟨20214915468665561183385893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53906441249774829822362381 20214915468665561183385893)
        ·
          refine ⟨3790296650374792721884855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20214915468665561183385893 3790296650374792721884855)
          ·
            refine ⟨5685444975562189082827283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790296650374792721884855 5685444975562189082827283)
            ·
              refine ⟨8528167463343283624240925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685444975562189082827283 8528167463343283624240925)
              ·
                refine ⟨3198062798753731359090347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8528167463343283624240925 3198062798753731359090347)
                ·
                  refine ⟨4797094198130597038635521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198062798753731359090347 4797094198130597038635521)
                  ·
                    refine ⟨3597820648597947778976641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4797094198130597038635521 3597820648597947778976641)
                    ·
                      refine ⟨2698365486448460834232481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597820648597947778976641 2698365486448460834232481)
                      ·
                        rfl

theorem cell23_5255048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_5255048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255048 prefixEnd_5255048 := by exact prefixLift 5255048
  have htrace : WordTrace (prefixWord ++ tailWord_5255048) baseStart_5255048 baseEnd_5255048 := by
    simpa [prefixWord, tailWord_5255048, baseEnd_5255048] using wordTrace_append hprefix tailTrace_5255048
  have hstable : (prefixWord ++ tailWord_5255048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255048).length < 2 ^ (prefixWord ++ tailWord_5255048).sum := by decide
  have hdescent : baseEnd_5255048 < baseStart_5255048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255056 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_5255056 : Nat := 118140960795 + 5255056 * 2 ^ 59
def prefixEnd_5255056 : Nat := 4983230072969 + 3 ^ 40 * 5255056 * 2
def baseEnd_5255056 : Nat := 2698369594293696802932443

theorem tailTrace_5255056 : CollatzResearch.WordTrace tailWord_5255056 prefixEnd_5255056 2698369594293696802932443 := by
  unfold tailWord_5255056
  simp only [CollatzResearch.WordTrace]
  refine ⟨95833819224918539478456511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127778425633224719304608681 95833819224918539478456511)
  ·
    refine ⟨143750728837377809217684767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95833819224918539478456511 143750728837377809217684767)
    ·
      refine ⟨215626093256066713826527151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143750728837377809217684767 215626093256066713826527151)
      ·
        refine ⟨323439139884100070739790727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215626093256066713826527151 323439139884100070739790727)
        ·
          refine ⟨485158709826150106109686091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323439139884100070739790727 485158709826150106109686091)
          ·
            refine ⟨727738064739225159164529137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485158709826150106109686091 727738064739225159164529137)
            ·
              refine ⟨545803548554418869373396853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727738064739225159164529137 545803548554418869373396853)
              ·
                refine ⟨51169082676976769003755955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 545803548554418869373396853 51169082676976769003755955)
                ·
                  refine ⟨76753624015465153505633933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51169082676976769003755955 76753624015465153505633933)
                  ·
                    refine ⟨28782609005799432564612725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76753624015465153505633933 28782609005799432564612725)
                    ·
                      refine ⟨2698369594293696802932443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28782609005799432564612725 2698369594293696802932443)
                      ·
                        rfl

theorem cell23_5255056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_5255056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255056 prefixEnd_5255056 := by exact prefixLift 5255056
  have htrace : WordTrace (prefixWord ++ tailWord_5255056) baseStart_5255056 baseEnd_5255056 := by
    simpa [prefixWord, tailWord_5255056, baseEnd_5255056] using wordTrace_append hprefix tailTrace_5255056
  have hstable : (prefixWord ++ tailWord_5255056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255056).length < 2 ^ (prefixWord ++ tailWord_5255056).sum := by decide
  have hdescent : baseEnd_5255056 < baseStart_5255056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255087 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 2, 2, 2]
def baseStart_5255087 : Nat := 118140960795 + 5255087 * 2 ^ 59
def prefixEnd_5255087 : Nat := 4983230072969 + 3 ^ 40 * 5255087 * 2
def baseEnd_5255087 : Nat := 2698385512193986181644801

theorem tailTrace_5255087 : CollatzResearch.WordTrace tailWord_5255087 prefixEnd_5255087 2698385512193986181644801 := by
  unfold tailWord_5255087
  simp only [CollatzResearch.WordTrace]
  refine ⟨191668769112724771251291515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127779179408483180834194343 191668769112724771251291515)
  ·
    refine ⟨287503153669087156876937273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191668769112724771251291515 287503153669087156876937273)
    ·
      refine ⟨215627365251815367657702955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287503153669087156876937273 215627365251815367657702955)
      ·
        refine ⟨323441047877723051486554433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215627365251815367657702955 323441047877723051486554433)
        ·
          refine ⟨242580785908292288614915825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323441047877723051486554433 242580785908292288614915825)
          ·
            refine ⟨181935589431219216461186869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242580785908292288614915825 181935589431219216461186869)
            ·
              refine ⟨17056461509176801543236269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181935589431219216461186869 17056461509176801543236269)
              ·
                refine ⟨6396173065941300578713601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17056461509176801543236269 6396173065941300578713601)
                ·
                  refine ⟨4797129799455975434035201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6396173065941300578713601 4797129799455975434035201)
                  ·
                    refine ⟨3597847349591981575526401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4797129799455975434035201 3597847349591981575526401)
                    ·
                      refine ⟨2698385512193986181644801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3597847349591981575526401 2698385512193986181644801)
                      ·
                        rfl

theorem cell23_5255087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 2, 2].length) (baseStart_5255087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255087 prefixEnd_5255087 := by exact prefixLift 5255087
  have htrace : WordTrace (prefixWord ++ tailWord_5255087) baseStart_5255087 baseEnd_5255087 := by
    simpa [prefixWord, tailWord_5255087, baseEnd_5255087] using wordTrace_append hprefix tailTrace_5255087
  have hstable : (prefixWord ++ tailWord_5255087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255087).length < 2 ^ (prefixWord ++ tailWord_5255087).sum := by decide
  have hdescent : baseEnd_5255087 < baseStart_5255087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255160 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_5255160 : Nat := 118140960795 + 5255160 * 2 ^ 59
def prefixEnd_5255160 : Nat := 4983230072969 + 3 ^ 40 * 5255160 * 2
def baseEnd_5255160 : Nat := 2698422996281764396031965

theorem tailTrace_5255160 : CollatzResearch.WordTrace tailWord_5255160 prefixEnd_5255160 2698422996281764396031965 := by
  unfold tailWord_5255160
  simp only [CollatzResearch.WordTrace]
  refine ⟨95835715820730152359349467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127780954427640203145799289 95835715820730152359349467)
  ·
    refine ⟨143753573731095228539024201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95835715820730152359349467 143753573731095228539024201)
    ·
      refine ⟨107815180298321421404268151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143753573731095228539024201 107815180298321421404268151)
      ·
        refine ⟨161722770447482132106402227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107815180298321421404268151 161722770447482132106402227)
        ·
          refine ⟨242584155671223198159603341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161722770447482132106402227 242584155671223198159603341)
          ·
            refine ⟨90969058376708699309851253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242584155671223198159603341 90969058376708699309851253)
            ·
              refine ⟨8528349222816440560298555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90969058376708699309851253 8528349222816440560298555)
              ·
                refine ⟨12792523834224660840447833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8528349222816440560298555 12792523834224660840447833)
                ·
                  refine ⟨9594392875668495630335875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12792523834224660840447833 9594392875668495630335875)
                  ·
                    refine ⟨14391589313502743445503813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9594392875668495630335875 14391589313502743445503813)
                    ·
                      refine ⟨2698422996281764396031965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14391589313502743445503813 2698422996281764396031965)
                      ·
                        rfl

theorem cell23_5255160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_5255160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255160 prefixEnd_5255160 := by exact prefixLift 5255160
  have htrace : WordTrace (prefixWord ++ tailWord_5255160) baseStart_5255160 baseEnd_5255160 := by
    simpa [prefixWord, tailWord_5255160, baseEnd_5255160] using wordTrace_append hprefix tailTrace_5255160
  have hstable : (prefixWord ++ tailWord_5255160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255160).length < 2 ^ (prefixWord ++ tailWord_5255160).sum := by decide
  have hdescent : baseEnd_5255160 < baseStart_5255160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255173 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_5255173 : Nat := 118140960795 + 5255173 * 2 ^ 59
def prefixEnd_5255173 : Nat := 4983230072969 + 3 ^ 40 * 5255173 * 2
def baseEnd_5255173 : Nat := 2698429671530272845169405

theorem tailTrace_5255173 : CollatzResearch.WordTrace tailWord_5255173 prefixEnd_5255173 2698429671530272845169405 := by
  unfold tailWord_5255173
  simp only [CollatzResearch.WordTrace]
  refine ⟨191671905790413207938922173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127781270526942138625948115 191671905790413207938922173)
  ·
    refine ⟨71876964671404952977095815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191671905790413207938922173 71876964671404952977095815)
    ·
      refine ⟨107815447007107429465643723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71876964671404952977095815 107815447007107429465643723)
      ·
        refine ⟨161723170510661144198465585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107815447007107429465643723 161723170510661144198465585)
        ·
          refine ⟨121292377882995858148849189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161723170510661144198465585 121292377882995858148849189)
          ·
            refine ⟨22742320853061723402909223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121292377882995858148849189 22742320853061723402909223)
            ·
              refine ⟨34113481279592585104363835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22742320853061723402909223 34113481279592585104363835)
              ·
                refine ⟨51170221919388877656545753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34113481279592585104363835 51170221919388877656545753)
                ·
                  refine ⟨38377666439541658242409315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51170221919388877656545753 38377666439541658242409315)
                  ·
                    refine ⟨57566499659312487363613973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38377666439541658242409315 57566499659312487363613973)
                    ·
                      refine ⟨2698429671530272845169405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57566499659312487363613973 2698429671530272845169405)
                      ·
                        rfl

theorem cell23_5255173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_5255173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255173 prefixEnd_5255173 := by exact prefixLift 5255173
  have htrace : WordTrace (prefixWord ++ tailWord_5255173) baseStart_5255173 baseEnd_5255173 := by
    simpa [prefixWord, tailWord_5255173, baseEnd_5255173] using wordTrace_append hprefix tailTrace_5255173
  have hstable : (prefixWord ++ tailWord_5255173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255173).length < 2 ^ (prefixWord ++ tailWord_5255173).sum := by decide
  have hdescent : baseEnd_5255173 < baseStart_5255173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255180 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_5255180 : Nat := 118140960795 + 5255180 * 2 ^ 59
def prefixEnd_5255180 : Nat := 4983230072969 + 3 ^ 40 * 5255180 * 2
def baseEnd_5255180 : Nat := 2698433265894854317781873

theorem tailTrace_5255180 : CollatzResearch.WordTrace tailWord_5255180 prefixEnd_5255180 2698433265894854317781873 := by
  unfold tailWord_5255180
  simp only [CollatzResearch.WordTrace]
  refine ⟨95836080550693924067213497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127781440734258565422951329 95836080550693924067213497)
  ·
    refine ⟨71877060413020443050410123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95836080550693924067213497 71877060413020443050410123)
    ·
      refine ⟨107815590619530664575615185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71877060413020443050410123 107815590619530664575615185)
      ·
        refine ⟨80861692964647998431711389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107815590619530664575615185 80861692964647998431711389)
        ·
          refine ⟨30323134861742999411891771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80861692964647998431711389 30323134861742999411891771)
          ·
            refine ⟨45484702292614499117837657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30323134861742999411891771 45484702292614499117837657)
            ·
              refine ⟨34113526719460874338378243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45484702292614499117837657 34113526719460874338378243)
              ·
                refine ⟨51170290079191311507567365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34113526719460874338378243 51170290079191311507567365)
                ·
                  refine ⟨9594429389848370907668881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51170290079191311507567365 9594429389848370907668881)
                  ·
                    refine ⟨7195822042386278180751661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9594429389848370907668881 7195822042386278180751661)
                    ·
                      refine ⟨2698433265894854317781873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195822042386278180751661 2698433265894854317781873)
                      ·
                        rfl

theorem cell23_5255180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_5255180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255180 prefixEnd_5255180 := by exact prefixLift 5255180
  have htrace : WordTrace (prefixWord ++ tailWord_5255180) baseStart_5255180 baseEnd_5255180 := by
    simpa [prefixWord, tailWord_5255180, baseEnd_5255180] using wordTrace_append hprefix tailTrace_5255180
  have hstable : (prefixWord ++ tailWord_5255180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255180).length < 2 ^ (prefixWord ++ tailWord_5255180).sum := by decide
  have hdescent : baseEnd_5255180 < baseStart_5255180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255187 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 1, 4]
def baseStart_5255187 : Nat := 118140960795 + 5255187 * 2 ^ 59
def prefixEnd_5255187 : Nat := 4983230072969 + 3 ^ 40 * 5255187 * 2
def baseEnd_5255187 : Nat := 899478953419811930131447

theorem tailTrace_5255187 : CollatzResearch.WordTrace tailWord_5255187 prefixEnd_5255187 899478953419811930131447 := by
  unfold tailWord_5255187
  simp only [CollatzResearch.WordTrace]
  refine ⟨191672416412362488329931815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127781610941574992219954543 191672416412362488329931815)
  ·
    refine ⟨287508624618543732494897723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191672416412362488329931815 287508624618543732494897723)
    ·
      refine ⟨431262936927815598742346585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287508624618543732494897723 431262936927815598742346585)
      ·
        refine ⟨323447202695861699056759939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431262936927815598742346585 323447202695861699056759939)
        ·
          refine ⟨485170804043792548585139909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323447202695861699056759939 485170804043792548585139909)
          ·
            refine ⟨90969525758211102859713733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485170804043792548585139909 90969525758211102859713733)
            ·
              refine ⟨17056786079664581786196325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90969525758211102859713733 17056786079664581786196325)
              ·
                refine ⟨3198147389937109084911811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17056786079664581786196325 3198147389937109084911811)
                ·
                  refine ⟨4797221084905663627367717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198147389937109084911811 4797221084905663627367717)
                  ·
                    refine ⟨899478953419811930131447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797221084905663627367717 899478953419811930131447)
                    ·
                      rfl

theorem cell23_5255187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 4].length) (baseStart_5255187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255187 prefixEnd_5255187 := by exact prefixLift 5255187
  have htrace : WordTrace (prefixWord ++ tailWord_5255187) baseStart_5255187 baseEnd_5255187 := by
    simpa [prefixWord, tailWord_5255187, baseEnd_5255187] using wordTrace_append hprefix tailTrace_5255187
  have hstable : (prefixWord ++ tailWord_5255187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255187).length < 2 ^ (prefixWord ++ tailWord_5255187).sum := by decide
  have hdescent : baseEnd_5255187 < baseStart_5255187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255203 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5255203 : Nat := 118140960795 + 5255203 * 2 ^ 59
def prefixEnd_5255203 : Nat := 4983230072969 + 3 ^ 40 * 5255203 * 2
def baseEnd_5255203 : Nat := 2698445075949907727794267

theorem tailTrace_5255203 : CollatzResearch.WordTrace tailWord_5255203 prefixEnd_5255203 2698445075949907727794267 := by
  unfold tailWord_5255203
  simp only [CollatzResearch.WordTrace]
  refine ⟨191672999980304523062514263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127781999986869682041676175 191672999980304523062514263)
  ·
    refine ⟨287509499970456784593771395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191672999980304523062514263 287509499970456784593771395)
    ·
      refine ⟨431264249955685176890657093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287509499970456784593771395 431264249955685176890657093)
      ·
        refine ⟨80862046866690970666998205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 431264249955685176890657093 80862046866690970666998205)
        ·
          refine ⟨30323267575009114000124327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80862046866690970666998205 30323267575009114000124327)
          ·
            refine ⟨45484901362513671000186491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30323267575009114000124327 45484901362513671000186491)
            ·
              refine ⟨68227352043770506500279737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45484901362513671000186491 68227352043770506500279737)
              ·
                refine ⟨51170514032827879875209803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68227352043770506500279737 51170514032827879875209803)
                ·
                  refine ⟨76755771049241819812814705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51170514032827879875209803 76755771049241819812814705)
                  ·
                    refine ⟨57566828286931364859611029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76755771049241819812814705 57566828286931364859611029)
                    ·
                      refine ⟨2698445075949907727794267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57566828286931364859611029 2698445075949907727794267)
                      ·
                        rfl

theorem cell23_5255203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5255203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255203 prefixEnd_5255203 := by exact prefixLift 5255203
  have htrace : WordTrace (prefixWord ++ tailWord_5255203) baseStart_5255203 baseEnd_5255203 := by
    simpa [prefixWord, tailWord_5255203, baseEnd_5255203] using wordTrace_append hprefix tailTrace_5255203
  have hstable : (prefixWord ++ tailWord_5255203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255203).length < 2 ^ (prefixWord ++ tailWord_5255203).sum := by decide
  have hdescent : baseEnd_5255203 < baseStart_5255203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255238 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_5255238 : Nat := 118140960795 + 5255238 * 2 ^ 59
def prefixEnd_5255238 : Nat := 4983230072969 + 3 ^ 40 * 5255238 * 2
def baseEnd_5255238 : Nat := 899487682590938363618869

theorem tailTrace_5255238 : CollatzResearch.WordTrace tailWord_5255238 prefixEnd_5255238 899487682590938363618869 := by
  unfold tailWord_5255238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989821141724303876251199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127782851023451816026692245 5989821141724303876251199)
  ·
    refine ⟨8984731712586455814376799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5989821141724303876251199 8984731712586455814376799)
    ·
      refine ⟨13477097568879683721565199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8984731712586455814376799 13477097568879683721565199)
      ·
        refine ⟨20215646353319525582347799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13477097568879683721565199 20215646353319525582347799)
        ·
          refine ⟨30323469529979288373521699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20215646353319525582347799 30323469529979288373521699)
          ·
            refine ⟨45485204294968932560282549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30323469529979288373521699 45485204294968932560282549)
            ·
              refine ⟨4264237902653337427526489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45485204294968932560282549 4264237902653337427526489)
              ·
                refine ⟨3198178426990003070644867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264237902653337427526489 3198178426990003070644867)
                ·
                  refine ⟨4797267640485004605967301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198178426990003070644867 4797267640485004605967301)
                  ·
                    refine ⟨899487682590938363618869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797267640485004605967301 899487682590938363618869)
                    ·
                      rfl

theorem cell23_5255238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_5255238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255238 prefixEnd_5255238 := by exact prefixLift 5255238
  have htrace : WordTrace (prefixWord ++ tailWord_5255238) baseStart_5255238 baseEnd_5255238 := by
    simpa [prefixWord, tailWord_5255238, baseEnd_5255238] using wordTrace_append hprefix tailTrace_5255238
  have hstable : (prefixWord ++ tailWord_5255238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255238).length < 2 ^ (prefixWord ++ tailWord_5255238).sum := by decide
  have hdescent : baseEnd_5255238 < baseStart_5255238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255243 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 3, 6]
def baseStart_5255243 : Nat := 118140960795 + 5255243 * 2 ^ 59
def prefixEnd_5255243 : Nat := 4983230072969 + 3 ^ 40 * 5255243 * 2
def baseEnd_5255243 : Nat := 899488538392029190431361

theorem tailTrace_5255243 : CollatzResearch.WordTrace tailWord_5255243 prefixEnd_5255243 899488538392029190431361 := by
  unfold tailWord_5255243
  simp only [CollatzResearch.WordTrace]
  refine ⟨191674458900159609893970383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127782972600106406595980255 191674458900159609893970383)
  ·
    refine ⟨287511688350239414840955575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191674458900159609893970383 287511688350239414840955575)
    ·
      refine ⟨431267532525359122261433363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287511688350239414840955575 431267532525359122261433363)
      ·
        refine ⟨646901298788038683392150045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431267532525359122261433363 646901298788038683392150045)
        ·
          refine ⟨242587987045514506272056267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 646901298788038683392150045 242587987045514506272056267)
          ·
            refine ⟨363881980568271759408084401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242587987045514506272056267 363881980568271759408084401)
            ·
              refine ⟨272911485426203819556063301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363881980568271759408084401 272911485426203819556063301)
              ·
                refine ⟨51170903517413216166761869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272911485426203819556063301 51170903517413216166761869)
                ·
                  refine ⟨19189088819029956062535701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51170903517413216166761869 19189088819029956062535701)
                  ·
                    refine ⟨899488538392029190431361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19189088819029956062535701 899488538392029190431361)
                    ·
                      rfl

theorem cell23_5255243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_5255243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255243 prefixEnd_5255243 := by exact prefixLift 5255243
  have htrace : WordTrace (prefixWord ++ tailWord_5255243) baseStart_5255243 baseEnd_5255243 := by
    simpa [prefixWord, tailWord_5255243, baseEnd_5255243] using wordTrace_append hprefix tailTrace_5255243
  have hstable : (prefixWord ++ tailWord_5255243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255243).length < 2 ^ (prefixWord ++ tailWord_5255243).sum := by decide
  have hdescent : baseEnd_5255243 < baseStart_5255243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255244 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5255244 : Nat := 118140960795 + 5255244 * 2 ^ 59
def prefixEnd_5255244 : Nat := 4983230072969 + 3 ^ 40 * 5255244 * 2
def baseEnd_5255244 : Nat := 2698466128656742067381579

theorem tailTrace_5255244 : CollatzResearch.WordTrace tailWord_5255244 prefixEnd_5255244 2698466128656742067381579 := by
  unfold tailWord_5255244
  simp only [CollatzResearch.WordTrace]
  refine ⟨95837247686577993532378393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127782996915437324709837857 95837247686577993532378393)
  ·
    refine ⟨71877935764933495149283795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95837247686577993532378393 71877935764933495149283795)
    ·
      refine ⟨107816903647400242723925693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71877935764933495149283795 107816903647400242723925693)
      ·
        refine ⟨40431338867775091021472135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107816903647400242723925693 40431338867775091021472135)
        ·
          refine ⟨60647008301662636532208203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40431338867775091021472135 60647008301662636532208203)
          ·
            refine ⟨90970512452493954798312305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60647008301662636532208203 90970512452493954798312305)
            ·
              refine ⟨68227884339370466098734229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90970512452493954798312305 68227884339370466098734229)
              ·
                refine ⟨3198182078407990598378167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68227884339370466098734229 3198182078407990598378167)
                ·
                  refine ⟨4797273117611985897567251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198182078407990598378167 4797273117611985897567251)
                  ·
                    refine ⟨7195909676417978846350877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4797273117611985897567251 7195909676417978846350877)
                    ·
                      refine ⟨2698466128656742067381579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7195909676417978846350877 2698466128656742067381579)
                      ·
                        rfl

theorem cell23_5255244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5255244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255244 prefixEnd_5255244 := by exact prefixLift 5255244
  have htrace : WordTrace (prefixWord ++ tailWord_5255244) baseStart_5255244 baseEnd_5255244 := by
    simpa [prefixWord, tailWord_5255244, baseEnd_5255244] using wordTrace_append hprefix tailTrace_5255244
  have hstable : (prefixWord ++ tailWord_5255244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255244).length < 2 ^ (prefixWord ++ tailWord_5255244).sum := by decide
  have hdescent : baseEnd_5255244 < baseStart_5255244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255267 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 4]
def baseStart_5255267 : Nat := 118140960795 + 5255267 * 2 ^ 59
def prefixEnd_5255267 : Nat := 4983230072969 + 3 ^ 40 * 5255267 * 2
def baseEnd_5255267 : Nat := 2698477938711795477393973

theorem tailTrace_5255267 : CollatzResearch.WordTrace tailWord_5255267 prefixEnd_5255267 2698477938711795477393973 := by
  unfold tailWord_5255267
  simp only [CollatzResearch.WordTrace]
  refine ⟨191675334252072661992844055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127783556168048441328562703 191675334252072661992844055)
  ·
    refine ⟨287513001378108992989266083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191675334252072661992844055 287513001378108992989266083)
    ·
      refine ⟨431269502067163489483899125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287513001378108992989266083 431269502067163489483899125)
      ·
        refine ⟨40431515818796577139115543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 431269502067163489483899125 40431515818796577139115543)
        ·
          refine ⟨60647273728194865708673315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40431515818796577139115543 60647273728194865708673315)
          ·
            refine ⟨90970910592292298563009973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60647273728194865708673315 90970910592292298563009973)
            ·
              refine ⟨8528522868027402990282185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90970910592292298563009973 8528522868027402990282185)
              ·
                refine ⟨6396392151020552242711639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8528522868027402990282185 6396392151020552242711639)
                ·
                  refine ⟨9594588226530828364067459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396392151020552242711639 9594588226530828364067459)
                  ·
                    refine ⟨14391882339796242546101189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9594588226530828364067459 14391882339796242546101189)
                    ·
                      refine ⟨2698477938711795477393973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14391882339796242546101189 2698477938711795477393973)
                      ·
                        rfl

theorem cell23_5255267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_5255267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255267 prefixEnd_5255267 := by exact prefixLift 5255267
  have htrace : WordTrace (prefixWord ++ tailWord_5255267) baseStart_5255267 baseEnd_5255267 := by
    simpa [prefixWord, tailWord_5255267, baseEnd_5255267] using wordTrace_append hprefix tailTrace_5255267
  have hstable : (prefixWord ++ tailWord_5255267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255267).length < 2 ^ (prefixWord ++ tailWord_5255267).sum := by decide
  have hdescent : baseEnd_5255267 < baseStart_5255267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255273 : List Nat := [1, 2, 1, 1, 1, 5, 1, 11]
def baseStart_5255273 : Nat := 118140960795 + 5255273 * 2 ^ 59
def prefixEnd_5255273 : Nat := 4983230072969 + 3 ^ 40 * 5255273 * 2
def baseEnd_5255273 : Nat := 99943741466508239034035

theorem tailTrace_5255273 : CollatzResearch.WordTrace tailWord_5255273 prefixEnd_5255273 99943741466508239034035 := by
  unfold tailWord_5255273
  simp only [CollatzResearch.WordTrace]
  refine ⟨191675553090050925017562473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127783702060033950011708315 191675553090050925017562473)
  ·
    refine ⟨143756664817538193763171855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191675553090050925017562473 143756664817538193763171855)
    ·
      refine ⟨215634997226307290644757783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143756664817538193763171855 215634997226307290644757783)
      ·
        refine ⟨323452495839460935967136675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215634997226307290644757783 323452495839460935967136675)
        ·
          refine ⟨485178743759191403950705013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323452495839460935967136675 485178743759191403950705013)
          ·
            refine ⟨45485507227424194120378595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 485178743759191403950705013 45485507227424194120378595)
            ·
              refine ⟨68228260841136291180567893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45485507227424194120378595 68228260841136291180567893)
              ·
                refine ⟨99943741466508239034035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 68228260841136291180567893 99943741466508239034035)
                ·
                  rfl

theorem cell23_5255273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 11].length) (baseStart_5255273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255273 prefixEnd_5255273 := by exact prefixLift 5255273
  have htrace : WordTrace (prefixWord ++ tailWord_5255273) baseStart_5255273 baseEnd_5255273 := by
    simpa [prefixWord, tailWord_5255273, baseEnd_5255273] using wordTrace_append hprefix tailTrace_5255273
  have hstable : (prefixWord ++ tailWord_5255273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255273).length < 2 ^ (prefixWord ++ tailWord_5255273).sum := by decide
  have hdescent : baseEnd_5255273 < baseStart_5255273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255280 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_5255280 : Nat := 118140960795 + 5255280 * 2 ^ 59
def prefixEnd_5255280 : Nat := 4983230072969 + 3 ^ 40 * 5255280 * 2
def baseEnd_5255280 : Nat := 2698484613960303926531413

theorem tailTrace_5255280 : CollatzResearch.WordTrace tailWord_5255280 prefixEnd_5255280 2698484613960303926531413 := by
  unfold tailWord_5255280
  simp only [CollatzResearch.WordTrace]
  refine ⟨95837904200512782606533647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127783872267350376808711529 95837904200512782606533647)
  ·
    refine ⟨143756856300769173909800471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95837904200512782606533647 143756856300769173909800471)
    ·
      refine ⟨215635284451153760864700707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143756856300769173909800471 215635284451153760864700707)
      ·
        refine ⟨323452926676730641297051061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215635284451153760864700707 323452926676730641297051061)
        ·
          refine ⟨30323711875943497621598537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 323452926676730641297051061 30323711875943497621598537)
          ·
            refine ⟨22742783906957623216198903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30323711875943497621598537 22742783906957623216198903)
            ·
              refine ⟨34114175860436434824298355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22742783906957623216198903 34114175860436434824298355)
              ·
                refine ⟨51171263790654652236447533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34114175860436434824298355 51171263790654652236447533)
                ·
                  refine ⟨19189223921495494588667825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51171263790654652236447533 19189223921495494588667825)
                  ·
                    refine ⟨14391917941121620941500869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19189223921495494588667825 14391917941121620941500869)
                    ·
                      refine ⟨2698484613960303926531413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14391917941121620941500869 2698484613960303926531413)
                      ·
                        rfl

theorem cell23_5255280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_5255280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255280 prefixEnd_5255280 := by exact prefixLift 5255280
  have htrace : WordTrace (prefixWord ++ tailWord_5255280) baseStart_5255280 baseEnd_5255280 := by
    simpa [prefixWord, tailWord_5255280, baseEnd_5255280] using wordTrace_append hprefix tailTrace_5255280
  have hstable : (prefixWord ++ tailWord_5255280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255280).length < 2 ^ (prefixWord ++ tailWord_5255280).sum := by decide
  have hdescent : baseEnd_5255280 < baseStart_5255280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255287 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_5255287 : Nat := 118140960795 + 5255287 * 2 ^ 59
def prefixEnd_5255287 : Nat := 4983230072969 + 3 ^ 40 * 5255287 * 2
def baseEnd_5255287 : Nat := 2698488208324885399143881

theorem tailTrace_5255287 : CollatzResearch.WordTrace tailWord_5255287 prefixEnd_5255287 2698488208324885399143881 := by
  unfold tailWord_5255287
  simp only [CollatzResearch.WordTrace]
  refine ⟨191676063712000205408572115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127784042474666803605714743 191676063712000205408572115)
  ·
    refine ⟨287514095568000308112858173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191676063712000205408572115 287514095568000308112858173)
    ·
      refine ⟨107817785838000115542321815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287514095568000308112858173 107817785838000115542321815)
      ·
        refine ⟨161726678757000173313482723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107817785838000115542321815 161726678757000173313482723)
        ·
          refine ⟨242590018135500259970224085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161726678757000173313482723 242590018135500259970224085)
          ·
            refine ⟨5685703550050787343052127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 242590018135500259970224085 5685703550050787343052127)
            ·
              refine ⟨8528555325076181014578191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685703550050787343052127 8528555325076181014578191)
              ·
                refine ⟨12792832987614271521867287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8528555325076181014578191 12792832987614271521867287)
                ·
                  refine ⟨19189249481421407282800931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12792832987614271521867287 19189249481421407282800931)
                  ·
                    refine ⟨28783874222132110924201397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19189249481421407282800931 28783874222132110924201397)
                    ·
                      refine ⟨2698488208324885399143881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28783874222132110924201397 2698488208324885399143881)
                      ·
                        rfl

theorem cell23_5255287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_5255287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255287 prefixEnd_5255287 := by exact prefixLift 5255287
  have htrace : WordTrace (prefixWord ++ tailWord_5255287) baseStart_5255287 baseEnd_5255287 := by
    simpa [prefixWord, tailWord_5255287, baseEnd_5255287] using wordTrace_append hprefix tailTrace_5255287
  have hstable : (prefixWord ++ tailWord_5255287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255287).length < 2 ^ (prefixWord ++ tailWord_5255287).sum := by decide
  have hdescent : baseEnd_5255287 < baseStart_5255287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255317 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_5255317 : Nat := 118140960795 + 5255317 * 2 ^ 59
def prefixEnd_5255317 : Nat := 4983230072969 + 3 ^ 40 * 5255317 * 2
def baseEnd_5255317 : Nat := 2698503612744520281768743

theorem tailTrace_5255317 : CollatzResearch.WordTrace tailWord_5255317 prefixEnd_5255317 2698503612744520281768743 := by
  unfold tailWord_5255317
  simp only [CollatzResearch.WordTrace]
  refine ⟨191677157901891520532164205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127784771934594347021442803 191677157901891520532164205)
  ·
    refine ⟨71878934213209320199561577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191677157901891520532164205 71878934213209320199561577)
    ·
      refine ⟨53909200659906990149671183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71878934213209320199561577 53909200659906990149671183)
      ·
        refine ⟨80863800989860485224506775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53909200659906990149671183 80863800989860485224506775)
        ·
          refine ⟨121295701484790727836760163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80863800989860485224506775 121295701484790727836760163)
          ·
            refine ⟨181943552227186091755140245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121295701484790727836760163 181943552227186091755140245)
            ·
              refine ⟨8528604010649348051022199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 181943552227186091755140245 8528604010649348051022199)
              ·
                refine ⟨12792906015974022076533299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8528604010649348051022199 12792906015974022076533299)
                ·
                  refine ⟨19189359023961033114799949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12792906015974022076533299 19189359023961033114799949)
                  ·
                    refine ⟨7196009633985387418049981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19189359023961033114799949 7196009633985387418049981)
                    ·
                      refine ⟨2698503612744520281768743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7196009633985387418049981 2698503612744520281768743)
                      ·
                        rfl

theorem cell23_5255317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_5255317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255317 prefixEnd_5255317 := by exact prefixLift 5255317
  have htrace : WordTrace (prefixWord ++ tailWord_5255317) baseStart_5255317 baseEnd_5255317 := by
    simpa [prefixWord, tailWord_5255317, baseEnd_5255317] using wordTrace_append hprefix tailTrace_5255317
  have hstable : (prefixWord ++ tailWord_5255317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255317).length < 2 ^ (prefixWord ++ tailWord_5255317).sum := by decide
  have hdescent : baseEnd_5255317 < baseStart_5255317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255335 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_5255335 : Nat := 118140960795 + 5255335 * 2 ^ 59
def prefixEnd_5255335 : Nat := 4983230072969 + 3 ^ 40 * 5255335 * 2
def baseEnd_5255335 : Nat := 2698512855396301211343661

theorem tailTrace_5255335 : CollatzResearch.WordTrace tailWord_5255335 prefixEnd_5255335 2698512855396301211343661 := by
  unfold tailWord_5255335
  simp only [CollatzResearch.WordTrace]
  refine ⟨191677814415826309606319459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127785209610550873070879639 191677814415826309606319459)
  ·
    refine ⟨287516721623739464409479189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191677814415826309606319459 287516721623739464409479189)
    ·
      refine ⟨13477346326112787394194337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 287516721623739464409479189 13477346326112787394194337)
      ·
        refine ⟨10108009744584590545645753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13477346326112787394194337 10108009744584590545645753)
        ·
          refine ⟨7581007308438442909234315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10108009744584590545645753 7581007308438442909234315)
          ·
            refine ⟨11371510962657664363851473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581007308438442909234315 11371510962657664363851473)
            ·
              refine ⟨8528633221993248272888605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11371510962657664363851473 8528633221993248272888605)
              ·
                refine ⟨3198237458247468102333227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8528633221993248272888605 3198237458247468102333227)
                ·
                  refine ⟨4797356187371202153499841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198237458247468102333227 4797356187371202153499841)
                  ·
                    refine ⟨3598017140528401615124881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4797356187371202153499841 3598017140528401615124881)
                    ·
                      refine ⟨2698512855396301211343661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598017140528401615124881 2698512855396301211343661)
                      ·
                        rfl

theorem cell23_5255335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_5255335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255335 prefixEnd_5255335 := by exact prefixLift 5255335
  have htrace : WordTrace (prefixWord ++ tailWord_5255335) baseStart_5255335 baseEnd_5255335 := by
    simpa [prefixWord, tailWord_5255335, baseEnd_5255335] using wordTrace_append hprefix tailTrace_5255335
  have hstable : (prefixWord ++ tailWord_5255335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255335).length < 2 ^ (prefixWord ++ tailWord_5255335).sum := by decide
  have hdescent : baseEnd_5255335 < baseStart_5255335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255351 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_5255351 : Nat := 118140960795 + 5255351 * 2 ^ 59
def prefixEnd_5255351 : Nat := 4983230072969 + 3 ^ 40 * 5255351 * 2
def baseEnd_5255351 : Nat := 2698521071086773148743587

theorem tailTrace_5255351 : CollatzResearch.WordTrace tailWord_5255351 prefixEnd_5255351 2698521071086773148743587 := by
  unfold tailWord_5255351
  simp only [CollatzResearch.WordTrace]
  refine ⟨191678397983768344338901907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127785598655845562892601271 191678397983768344338901907)
  ·
    refine ⟨287517596975652516508352861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191678397983768344338901907 287517596975652516508352861)
    ·
      refine ⟨107819098865869693690632323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 287517596975652516508352861 107819098865869693690632323)
      ·
        refine ⟨161728648298804540535948485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107819098865869693690632323 161728648298804540535948485)
        ·
          refine ⟨30324121556025851350490341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161728648298804540535948485 30324121556025851350490341)
          ·
            refine ⟨5685772791754847128216939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30324121556025851350490341 5685772791754847128216939)
            ·
              refine ⟨8528659187632270692325409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685772791754847128216939 8528659187632270692325409)
              ·
                refine ⟨6396494390724203019244057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8528659187632270692325409 6396494390724203019244057)
                ·
                  refine ⟨4797370793043152264433043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6396494390724203019244057 4797370793043152264433043)
                  ·
                    refine ⟨7196056189564728396649565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4797370793043152264433043 7196056189564728396649565)
                    ·
                      refine ⟨2698521071086773148743587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7196056189564728396649565 2698521071086773148743587)
                      ·
                        rfl

theorem cell23_5255351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_5255351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255351 prefixEnd_5255351 := by exact prefixLift 5255351
  have htrace : WordTrace (prefixWord ++ tailWord_5255351) baseStart_5255351 baseEnd_5255351 := by
    simpa [prefixWord, tailWord_5255351, baseEnd_5255351] using wordTrace_append hprefix tailTrace_5255351
  have hstable : (prefixWord ++ tailWord_5255351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255351).length < 2 ^ (prefixWord ++ tailWord_5255351).sum := by decide
  have hdescent : baseEnd_5255351 < baseStart_5255351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255414 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_5255414 : Nat := 118140960795 + 5255414 * 2 ^ 59
def prefixEnd_5255414 : Nat := 4983230072969 + 3 ^ 40 * 5255414 * 2
def baseEnd_5255414 : Nat := 299839268929778489139533

theorem tailTrace_5255414 : CollatzResearch.WordTrace tailWord_5255414 prefixEnd_5255414 299839268929778489139533 := by
  unfold tailWord_5255414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980043486408756631152831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127787130521693404065630197 11980043486408756631152831)
  ·
    refine ⟨17970065229613134946729247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11980043486408756631152831 17970065229613134946729247)
    ·
      refine ⟨26955097844419702420093871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17970065229613134946729247 26955097844419702420093871)
      ·
        refine ⟨40432646766629553630140807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26955097844419702420093871 40432646766629553630140807)
        ·
          refine ⟨60648970149944330445211211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40432646766629553630140807 60648970149944330445211211)
          ·
            refine ⟨90973455224916495667816817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60648970149944330445211211 90973455224916495667816817)
            ·
              refine ⟨68230091418687371750862613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90973455224916495667816817 68230091418687371750862613)
              ·
                refine ⟨3198285535250970550821685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68230091418687371750862613 3198285535250970550821685)
                ·
                  refine ⟨299839268929778489139533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3198285535250970550821685 299839268929778489139533)
                  ·
                    rfl

theorem cell23_5255414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_5255414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255414 prefixEnd_5255414 := by exact prefixLift 5255414
  have htrace : WordTrace (prefixWord ++ tailWord_5255414) baseStart_5255414 baseEnd_5255414 := by
    simpa [prefixWord, tailWord_5255414, baseEnd_5255414] using wordTrace_append hprefix tailTrace_5255414
  have hstable : (prefixWord ++ tailWord_5255414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255414).length < 2 ^ (prefixWord ++ tailWord_5255414).sum := by decide
  have hdescent : baseEnd_5255414 < baseStart_5255414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255481 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5255481 : Nat := 118140960795 + 5255481 * 2 ^ 59
def prefixEnd_5255481 : Nat := 4983230072969 + 3 ^ 40 * 5255481 * 2
def baseEnd_5255481 : Nat := 2698587823571857640117989

theorem tailTrace_5255481 : CollatzResearch.WordTrace tailWord_5255481 prefixEnd_5255481 2698587823571857640117989 := by
  unfold tailWord_5255481
  simp only [CollatzResearch.WordTrace]
  refine ⟨191683139473297376541134297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127788759648864917694089531 191683139473297376541134297)
  ·
    refine ⟨143762354604973032405850723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191683139473297376541134297 143762354604973032405850723)
    ·
      refine ⟨215643531907459548608776085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143762354604973032405850723 215643531907459548608776085)
      ·
        refine ⟨10108290558162166341036379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215643531907459548608776085 10108290558162166341036379)
        ·
          refine ⟨15162435837243249511554569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10108290558162166341036379 15162435837243249511554569)
          ·
            refine ⟨11371826877932437133665927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15162435837243249511554569 11371826877932437133665927)
            ·
              refine ⟨17057740316898655700498891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11371826877932437133665927 17057740316898655700498891)
              ·
                refine ⟨25586610475347983550748337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17057740316898655700498891 25586610475347983550748337)
                ·
                  refine ⟨19189957856510987663061253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25586610475347983550748337 19189957856510987663061253)
                  ·
                    refine ⟨3598117098095810186823985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19189957856510987663061253 3598117098095810186823985)
                    ·
                      refine ⟨2698587823571857640117989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3598117098095810186823985 2698587823571857640117989)
                      ·
                        rfl

theorem cell23_5255481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5255481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255481 prefixEnd_5255481 := by exact prefixLift 5255481
  have htrace : WordTrace (prefixWord ++ tailWord_5255481) baseStart_5255481 baseEnd_5255481 := by
    simpa [prefixWord, tailWord_5255481, baseEnd_5255481] using wordTrace_append hprefix tailTrace_5255481
  have hstable : (prefixWord ++ tailWord_5255481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255481).length < 2 ^ (prefixWord ++ tailWord_5255481).sum := by decide
  have hdescent : baseEnd_5255481 < baseStart_5255481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255487 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 6]
def baseStart_5255487 : Nat := 118140960795 + 5255487 * 2 ^ 59
def prefixEnd_5255487 : Nat := 4983230072969 + 3 ^ 40 * 5255487 * 2
def baseEnd_5255487 : Nat := 299843433828420512960329

theorem tailTrace_5255487 : CollatzResearch.WordTrace tailWord_5255487 prefixEnd_5255487 299843433828420512960329 := by
  unfold tailWord_5255487
  simp only [CollatzResearch.WordTrace]
  refine ⟨191683358311275639565852715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127788905540850426377235143 191683358311275639565852715)
  ·
    refine ⟨287525037466913459348779073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191683358311275639565852715 287525037466913459348779073)
    ·
      refine ⟨215643778100185094511584305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287525037466913459348779073 215643778100185094511584305)
      ·
        refine ⟨161732833575138820883688229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215643778100185094511584305 161732833575138820883688229)
        ·
          refine ⟨30324906295338528915691543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161732833575138820883688229 30324906295338528915691543)
          ·
            refine ⟨45487359443007793373537315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30324906295338528915691543 45487359443007793373537315)
            ·
              refine ⟨68231039164511690060305973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45487359443007793373537315 68231039164511690060305973)
              ·
                refine ⟨6396659921672970943153685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68231039164511690060305973 6396659921672970943153685)
                ·
                  refine ⟨299843433828420512960329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6396659921672970943153685 299843433828420512960329)
                  ·
                    rfl

theorem cell23_5255487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 6].length) (baseStart_5255487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255487 prefixEnd_5255487 := by exact prefixLift 5255487
  have htrace : WordTrace (prefixWord ++ tailWord_5255487) baseStart_5255487 baseEnd_5255487 := by
    simpa [prefixWord, tailWord_5255487, baseEnd_5255487] using wordTrace_append hprefix tailTrace_5255487
  have hstable : (prefixWord ++ tailWord_5255487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255487).length < 2 ^ (prefixWord ++ tailWord_5255487).sum := by decide
  have hdescent : baseEnd_5255487 < baseStart_5255487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255508 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_5255508 : Nat := 118140960795 + 5255508 * 2 ^ 59
def prefixEnd_5255508 : Nat := 4983230072969 + 3 ^ 40 * 5255508 * 2
def baseEnd_5255508 : Nat := 899533895849843011493455

theorem tailTrace_5255508 : CollatzResearch.WordTrace tailWord_5255508 prefixEnd_5255508 899533895849843011493455 := by
  unfold tailWord_5255508
  simp only [CollatzResearch.WordTrace]
  refine ⟨95842062122099780076183589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127789416162799706768244785 95842062122099780076183589)
  ·
    refine ⟨17970386647893708764284423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95842062122099780076183589 17970386647893708764284423)
    ·
      refine ⟨26955579971840563146426635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17970386647893708764284423 26955579971840563146426635)
      ·
        refine ⟨40433369957760844719639953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26955579971840563146426635 40433369957760844719639953)
        ·
          refine ⟨30325027468320633539729965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40433369957760844719639953 30325027468320633539729965)
          ·
            refine ⟨11371885300620237577398737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30325027468320633539729965 11371885300620237577398737)
            ·
              refine ⟨8528913975465178183049053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11371885300620237577398737 8528913975465178183049053)
              ·
                refine ⟨3198342740799441818643395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8528913975465178183049053 3198342740799441818643395)
                ·
                  refine ⟨4797514111199162727965093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198342740799441818643395 4797514111199162727965093)
                  ·
                    refine ⟨899533895849843011493455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797514111199162727965093 899533895849843011493455)
                    ·
                      rfl

theorem cell23_5255508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_5255508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255508 prefixEnd_5255508 := by exact prefixLift 5255508
  have htrace : WordTrace (prefixWord ++ tailWord_5255508) baseStart_5255508 baseEnd_5255508 := by
    simpa [prefixWord, tailWord_5255508, baseEnd_5255508] using wordTrace_append hprefix tailTrace_5255508
  have hstable : (prefixWord ++ tailWord_5255508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255508).length < 2 ^ (prefixWord ++ tailWord_5255508).sum := by decide
  have hdescent : baseEnd_5255508 < baseStart_5255508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5255514 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_5255514 : Nat := 118140960795 + 5255514 * 2 ^ 59
def prefixEnd_5255514 : Nat := 4983230072969 + 3 ^ 40 * 5255514 * 2
def baseEnd_5255514 : Nat := 2698604768433456011005337

theorem tailTrace_5255514 : CollatzResearch.WordTrace tailWord_5255514 prefixEnd_5255514 2698604768433456011005337 := by
  unfold tailWord_5255514
  simp only [CollatzResearch.WordTrace]
  refine ⟨47921085770544455794271399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127789562054785215451390397 47921085770544455794271399)
  ·
    refine ⟨71881628655816683691407099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47921085770544455794271399 71881628655816683691407099)
    ·
      refine ⟨107822442983725025537110649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71881628655816683691407099 107822442983725025537110649)
      ·
        refine ⟨80866832237793769152832987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107822442983725025537110649 80866832237793769152832987)
        ·
          refine ⟨121300248356690653729249481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80866832237793769152832987 121300248356690653729249481)
          ·
            refine ⟨90975186267517990296937111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121300248356690653729249481 90975186267517990296937111)
            ·
              refine ⟨136462779401276985445405667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90975186267517990296937111 136462779401276985445405667)
              ·
                refine ⟨204694169101915478168108501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136462779401276985445405667 204694169101915478168108501)
                ·
                  refine ⟨4797519588326144019565043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 204694169101915478168108501 4797519588326144019565043)
                  ·
                    refine ⟨7196279382489216029347565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4797519588326144019565043 7196279382489216029347565)
                    ·
                      refine ⟨2698604768433456011005337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7196279382489216029347565 2698604768433456011005337)
                      ·
                        rfl

theorem cell23_5255514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_5255514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5255514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5255514 prefixEnd_5255514 := by exact prefixLift 5255514
  have htrace : WordTrace (prefixWord ++ tailWord_5255514) baseStart_5255514 baseEnd_5255514 := by
    simpa [prefixWord, tailWord_5255514, baseEnd_5255514] using wordTrace_append hprefix tailTrace_5255514
  have hstable : (prefixWord ++ tailWord_5255514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5255514).length < 2 ^ (prefixWord ++ tailWord_5255514).sum := by decide
  have hdescent : baseEnd_5255514 < baseStart_5255514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5255514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
