import V185TrunkScan23Chunk0179

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1065607 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_1065607 : Nat := 118140960795 + 1065607 * 2 ^ 59
def prefixEnd_1065607 : Nat := 4983230072969 + 3 ^ 40 * 1065607 * 2
def baseEnd_1065607 : Nat := 547168579795717541411869

theorem tailTrace_1065607 : CollatzResearch.WordTrace tailWord_1065607 prefixEnd_1065607 547168579795717541411869 := by
  unfold tailWord_1065607
  simp only [CollatzResearch.WordTrace]
  refine ⟨38865880250495305031651075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25910586833663536687767383 38865880250495305031651075)
  ·
    refine ⟨58298820375742957547476613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38865880250495305031651075 58298820375742957547476613)
    ·
      refine ⟨10931028820451804540151865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58298820375742957547476613 10931028820451804540151865)
      ·
        refine ⟨8198271615338853405113899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10931028820451804540151865 8198271615338853405113899)
        ·
          refine ⟨12297407423008280107670849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8198271615338853405113899 12297407423008280107670849)
          ·
            refine ⟨9223055567256210080753137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12297407423008280107670849 9223055567256210080753137)
            ·
              refine ⟨6917291675442157560564853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9223055567256210080753137 6917291675442157560564853)
              ·
                refine ⟨648496094572702271302955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6917291675442157560564853 648496094572702271302955)
                ·
                  refine ⟨972744141859053406954433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648496094572702271302955 972744141859053406954433)
                  ·
                    refine ⟨729558106394290055215825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 972744141859053406954433 729558106394290055215825)
                    ·
                      refine ⟨547168579795717541411869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729558106394290055215825 547168579795717541411869)
                      ·
                        rfl

theorem cell23_1065607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_1065607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065607 prefixEnd_1065607 := by exact prefixLift 1065607
  have htrace : WordTrace (prefixWord ++ tailWord_1065607) baseStart_1065607 baseEnd_1065607 := by
    simpa [prefixWord, tailWord_1065607, baseEnd_1065607] using wordTrace_append hprefix tailTrace_1065607
  have hstable : (prefixWord ++ tailWord_1065607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065607).length < 2 ^ (prefixWord ++ tailWord_1065607).sum := by decide
  have hdescent : baseEnd_1065607 < baseStart_1065607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065610 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1065610 : Nat := 118140960795 + 1065610 * 2 ^ 59
def prefixEnd_1065610 : Nat := 4983230072969 + 3 ^ 40 * 1065610 * 2
def baseEnd_1065610 : Nat := 547170120237681029674355

theorem tailTrace_1065610 : CollatzResearch.WordTrace tailWord_1065610 prefixEnd_1065610 547170120237681029674355 := by
  unfold tailWord_1065610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9716497417371109136002571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25910659779656291029340189 9716497417371109136002571)
  ·
    refine ⟨14574746126056663704003857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9716497417371109136002571 14574746126056663704003857)
    ·
      refine ⟨10931059594542497778002893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14574746126056663704003857 10931059594542497778002893)
      ·
        refine ⟨4099147347953436666751085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10931059594542497778002893 4099147347953436666751085)
        ·
          refine ⟨1537180255482538750031657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4099147347953436666751085 1537180255482538750031657)
          ·
            refine ⟨1152885191611904062523743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1537180255482538750031657 1152885191611904062523743)
            ·
              refine ⟨1729327787417856093785615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152885191611904062523743 1729327787417856093785615)
              ·
                refine ⟨2593991681126784140678423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729327787417856093785615 2593991681126784140678423)
                ·
                  refine ⟨3890987521690176211017635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593991681126784140678423 3890987521690176211017635)
                  ·
                    refine ⟨5836481282535264316526453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3890987521690176211017635 5836481282535264316526453)
                    ·
                      refine ⟨547170120237681029674355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5836481282535264316526453 547170120237681029674355)
                      ·
                        rfl

theorem cell23_1065610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1065610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065610 prefixEnd_1065610 := by exact prefixLift 1065610
  have htrace : WordTrace (prefixWord ++ tailWord_1065610) baseStart_1065610 baseEnd_1065610 := by
    simpa [prefixWord, tailWord_1065610, baseEnd_1065610] using wordTrace_append hprefix tailTrace_1065610
  have hstable : (prefixWord ++ tailWord_1065610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065610).length < 2 ^ (prefixWord ++ tailWord_1065610).sum := by decide
  have hdescent : baseEnd_1065610 < baseStart_1065610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065650 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_1065650 : Nat := 118140960795 + 1065650 * 2 ^ 59
def prefixEnd_1065650 : Nat := 4983230072969 + 3 ^ 40 * 1065650 * 2
def baseEnd_1065650 : Nat := 547190659463860873174171

theorem tailTrace_1065650 : CollatzResearch.WordTrace tailWord_1065650 prefixEnd_1065650 547190659463860873174171 := by
  unfold tailWord_1065650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9716862147334880843866601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25911632392893015583644269 9716862147334880843866601)
  ·
    refine ⟨7287646610501160632899951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9716862147334880843866601 7287646610501160632899951)
    ·
      refine ⟨10931469915751740949349927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7287646610501160632899951 10931469915751740949349927)
      ·
        refine ⟨16397204873627611424024891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10931469915751740949349927 16397204873627611424024891)
        ·
          refine ⟨24595807310441417136037337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16397204873627611424024891 24595807310441417136037337)
          ·
            refine ⟨18446855482831062852028003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24595807310441417136037337 18446855482831062852028003)
            ·
              refine ⟨27670283224246594278042005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18446855482831062852028003 27670283224246594278042005)
              ·
                refine ⟨1297044526136559106783219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27670283224246594278042005 1297044526136559106783219)
                ·
                  refine ⟨1945566789204838660174829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297044526136559106783219 1945566789204838660174829)
                  ·
                    refine ⟨729587545951814497565561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945566789204838660174829 729587545951814497565561)
                    ·
                      refine ⟨547190659463860873174171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729587545951814497565561 547190659463860873174171)
                      ·
                        rfl

theorem cell23_1065650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_1065650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065650 prefixEnd_1065650 := by exact prefixLift 1065650
  have htrace : WordTrace (prefixWord ++ tailWord_1065650) baseStart_1065650 baseEnd_1065650 := by
    simpa [prefixWord, tailWord_1065650, baseEnd_1065650] using wordTrace_append hprefix tailTrace_1065650
  have hstable : (prefixWord ++ tailWord_1065650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065650).length < 2 ^ (prefixWord ++ tailWord_1065650).sum := by decide
  have hdescent : baseEnd_1065650 < baseStart_1065650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065697 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_1065697 : Nat := 118140960795 + 1065697 * 2 ^ 59
def prefixEnd_1065697 : Nat := 4983230072969 + 3 ^ 40 * 1065697 * 2
def baseEnd_1065697 : Nat := 547214793054622189286455

theorem tailTrace_1065697 : CollatzResearch.WordTrace tailWord_1065697 prefixEnd_1065697 547214793054622189286455 := by
  unfold tailWord_1065697
  simp only [CollatzResearch.WordTrace]
  refine ⟨38869162820169250402427345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25912775213446166934951563 38869162820169250402427345)
  ·
    refine ⟨29151872115126937801820509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38869162820169250402427345 29151872115126937801820509)
    ·
      refine ⟨10931952043172601675682691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29151872115126937801820509 10931952043172601675682691)
      ·
        refine ⟨16397928064758902513524037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10931952043172601675682691 16397928064758902513524037)
        ·
          refine ⟨3074611512142294221285757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16397928064758902513524037 3074611512142294221285757)
          ·
            refine ⟨1152979317053360332982159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3074611512142294221285757 1152979317053360332982159)
            ·
              refine ⟨1729468975580040499473239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152979317053360332982159 1729468975580040499473239)
              ·
                refine ⟨2594203463370060749209859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729468975580040499473239 2594203463370060749209859)
                ·
                  refine ⟨3891305195055091123814789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594203463370060749209859 3891305195055091123814789)
                  ·
                    refine ⟨729619724072829585715273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3891305195055091123814789 729619724072829585715273)
                    ·
                      refine ⟨547214793054622189286455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729619724072829585715273 547214793054622189286455)
                      ·
                        rfl

theorem cell23_1065697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_1065697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065697 prefixEnd_1065697 := by exact prefixLift 1065697
  have htrace : WordTrace (prefixWord ++ tailWord_1065697) baseStart_1065697 baseEnd_1065697 := by
    simpa [prefixWord, tailWord_1065697, baseEnd_1065697] using wordTrace_append hprefix tailTrace_1065697
  have hstable : (prefixWord ++ tailWord_1065697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065697).length < 2 ^ (prefixWord ++ tailWord_1065697).sum := by decide
  have hdescent : baseEnd_1065697 < baseStart_1065697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065763 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 5, 4]
def baseStart_1065763 : Nat := 118140960795 + 1065763 * 2 ^ 59
def prefixEnd_1065763 : Nat := 4983230072969 + 3 ^ 40 * 1065763 * 2
def baseEnd_1065763 : Nat := 182416227592606310353717

theorem tailTrace_1065763 : CollatzResearch.WordTrace tailWord_1065763 prefixEnd_1065763 182416227592606310353717 := by
  unfold tailWord_1065763
  simp only [CollatzResearch.WordTrace]
  refine ⟨38871570037930143674329943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25914380025286762449553295 38871570037930143674329943)
  ·
    refine ⟨58307355056895215511494915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38871570037930143674329943 58307355056895215511494915)
    ·
      refine ⟨87461032585342823267242373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58307355056895215511494915 87461032585342823267242373)
      ·
        refine ⟨16398943609751779362607945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87461032585342823267242373 16398943609751779362607945)
        ·
          refine ⟨12299207707313834521955959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16398943609751779362607945 12299207707313834521955959)
          ·
            refine ⟨18448811560970751782933939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12299207707313834521955959 18448811560970751782933939)
            ·
              refine ⟨27673217341456127674400909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18448811560970751782933939 27673217341456127674400909)
              ·
                refine ⟨10377456503046047877900341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27673217341456127674400909 10377456503046047877900341)
                ·
                  refine ⟨972886547160566988553157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10377456503046047877900341 972886547160566988553157)
                  ·
                    refine ⟨182416227592606310353717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972886547160566988553157 182416227592606310353717)
                    ·
                      rfl

theorem cell23_1065763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 4].length) (baseStart_1065763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065763 prefixEnd_1065763 := by exact prefixLift 1065763
  have htrace : WordTrace (prefixWord ++ tailWord_1065763) baseStart_1065763 baseEnd_1065763 := by
    simpa [prefixWord, tailWord_1065763, baseEnd_1065763] using wordTrace_append hprefix tailTrace_1065763
  have hstable : (prefixWord ++ tailWord_1065763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065763).length < 2 ^ (prefixWord ++ tailWord_1065763).sum := by decide
  have hdescent : baseEnd_1065763 < baseStart_1065763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065776 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 10]
def baseStart_1065776 : Nat := 118140960795 + 1065776 * 2 ^ 59
def prefixEnd_1065776 : Nat := 4983230072969 + 3 ^ 40 * 1065776 * 2
def baseEnd_1065776 : Nat := 60806150891814153355399

theorem tailTrace_1065776 : CollatzResearch.WordTrace tailWord_1065776 prefixEnd_1065776 60806150891814153355399 := by
  unfold tailWord_1065776
  simp only [CollatzResearch.WordTrace]
  refine ⟨19436022093441523447276591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25914696124588697929702121 19436022093441523447276591)
  ·
    refine ⟨29154033140162285170914887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19436022093441523447276591 29154033140162285170914887)
    ·
      refine ⟨43731049710243427756372331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29154033140162285170914887 43731049710243427756372331)
      ·
        refine ⟨65596574565365141634558497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43731049710243427756372331 65596574565365141634558497)
        ·
          refine ⟨49197430924023856225918873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65596574565365141634558497 49197430924023856225918873)
          ·
            refine ⟨36898073193017892169439155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49197430924023856225918873 36898073193017892169439155)
            ·
              refine ⟨55347109789526838254158733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36898073193017892169439155 55347109789526838254158733)
              ·
                refine ⟨20755166171072564345309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55347109789526838254158733 20755166171072564345309525)
                ·
                  refine ⟨60806150891814153355399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20755166171072564345309525 60806150891814153355399)
                  ·
                    rfl

theorem cell23_1065776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_1065776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065776 prefixEnd_1065776 := by exact prefixLift 1065776
  have htrace : WordTrace (prefixWord ++ tailWord_1065776) baseStart_1065776 baseEnd_1065776 := by
    simpa [prefixWord, tailWord_1065776, baseEnd_1065776] using wordTrace_append hprefix tailTrace_1065776
  have hstable : (prefixWord ++ tailWord_1065776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065776).length < 2 ^ (prefixWord ++ tailWord_1065776).sum := by decide
  have hdescent : baseEnd_1065776 < baseStart_1065776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065823 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 3, 5]
def baseStart_1065823 : Nat := 118140960795 + 1065823 * 2 ^ 59
def prefixEnd_1065823 : Nat := 4983230072969 + 3 ^ 40 * 1065823 * 2
def baseEnd_1065823 : Nat := 182426497205696232103625

theorem tailTrace_1065823 : CollatzResearch.WordTrace tailWord_1065823 prefixEnd_1065823 182426497205696232103625 := by
  unfold tailWord_1065823
  simp only [CollatzResearch.WordTrace]
  refine ⟨38873758417712773921514123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25915838945141849281009415 38873758417712773921514123)
  ·
    refine ⟨58310637626569160882271185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38873758417712773921514123 58310637626569160882271185)
    ·
      refine ⟨43732978219926870661703389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58310637626569160882271185 43732978219926870661703389)
      ·
        refine ⟨16399866832472576498138771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43732978219926870661703389 16399866832472576498138771)
        ·
          refine ⟨24599800248708864747208157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16399866832472576498138771 24599800248708864747208157)
          ·
            refine ⟨9224925093265824280203059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24599800248708864747208157 9224925093265824280203059)
            ·
              refine ⟨13837387639898736420304589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9224925093265824280203059 13837387639898736420304589)
              ·
                refine ⟨5189020364962026157614221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13837387639898736420304589 5189020364962026157614221)
                ·
                  refine ⟨1945882636860759809105333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5189020364962026157614221 1945882636860759809105333)
                  ·
                    refine ⟨182426497205696232103625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1945882636860759809105333 182426497205696232103625)
                    ·
                      rfl

theorem cell23_1065823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_1065823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065823 prefixEnd_1065823 := by exact prefixLift 1065823
  have htrace : WordTrace (prefixWord ++ tailWord_1065823) baseStart_1065823 baseEnd_1065823 := by
    simpa [prefixWord, tailWord_1065823, baseEnd_1065823] using wordTrace_append hprefix tailTrace_1065823
  have hstable : (prefixWord ++ tailWord_1065823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065823).length < 2 ^ (prefixWord ++ tailWord_1065823).sum := by decide
  have hdescent : baseEnd_1065823 < baseStart_1065823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065853 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1065853 : Nat := 118140960795 + 1065853 * 2 ^ 59
def prefixEnd_1065853 : Nat := 4983230072969 + 3 ^ 40 * 1065853 * 2
def baseEnd_1065853 : Nat := 182431632012241192978579

theorem tailTrace_1065853 : CollatzResearch.WordTrace tailWord_1065853 prefixEnd_1065853 182431632012241192978579 := by
  unfold tailWord_1065853
  simp only [CollatzResearch.WordTrace]
  refine ⟨38874852607604089045106213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25916568405069392696737475 38874852607604089045106213)
  ·
    refine ⟨7289034863925766695957415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38874852607604089045106213 7289034863925766695957415)
    ·
      refine ⟨10933552295888650043936123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7289034863925766695957415 10933552295888650043936123)
      ·
        refine ⟨16400328443832975065904185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10933552295888650043936123 16400328443832975065904185)
        ·
          refine ⟨12300246332874731299428139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16400328443832975065904185 12300246332874731299428139)
          ·
            refine ⟨18450369499312096949142209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300246332874731299428139 18450369499312096949142209)
            ·
              refine ⟨13837777124484072711856657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18450369499312096949142209 13837777124484072711856657)
              ·
                refine ⟨10378332843363054533892493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13837777124484072711856657 10378332843363054533892493)
                ·
                  refine ⟨3891874816261145450209685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10378332843363054533892493 3891874816261145450209685)
                  ·
                    refine ⟨182431632012241192978579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3891874816261145450209685 182431632012241192978579)
                    ·
                      rfl

theorem cell23_1065853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1065853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065853 prefixEnd_1065853 := by exact prefixLift 1065853
  have htrace : WordTrace (prefixWord ++ tailWord_1065853) baseStart_1065853 baseEnd_1065853 := by
    simpa [prefixWord, tailWord_1065853, baseEnd_1065853] using wordTrace_append hprefix tailTrace_1065853
  have hstable : (prefixWord ++ tailWord_1065853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065853).length < 2 ^ (prefixWord ++ tailWord_1065853).sum := by decide
  have hdescent : baseEnd_1065853 < baseStart_1065853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065874 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1065874 : Nat := 118140960795 + 1065874 * 2 ^ 59
def prefixEnd_1065874 : Nat := 4983230072969 + 3 ^ 40 * 1065874 * 2
def baseEnd_1065874 : Nat := 182435226376822665591047

theorem tailTrace_1065874 : CollatzResearch.WordTrace tailWord_1065874 prefixEnd_1065874 182435226376822665591047 := by
  unfold tailWord_1065874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718904635132002407905169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25917079027018673087747117 9718904635132002407905169)
  ·
    refine ⟨7289178476349001805928877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9718904635132002407905169 7289178476349001805928877)
    ·
      refine ⟨2733441928630875677223329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7289178476349001805928877 2733441928630875677223329)
      ·
        refine ⟨2050081446473156757917497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2733441928630875677223329 2050081446473156757917497)
        ·
          refine ⟨1537561084854867568438123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2050081446473156757917497 1537561084854867568438123)
          ·
            refine ⟨2306341627282301352657185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537561084854867568438123 2306341627282301352657185)
            ·
              refine ⟨1729756220461726014492889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306341627282301352657185 1729756220461726014492889)
              ·
                refine ⟨1297317165346294510869667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729756220461726014492889 1297317165346294510869667)
                ·
                  refine ⟨1945975748019441766304501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297317165346294510869667 1945975748019441766304501)
                  ·
                    refine ⟨182435226376822665591047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1945975748019441766304501 182435226376822665591047)
                    ·
                      rfl

theorem cell23_1065874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1065874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065874 prefixEnd_1065874 := by exact prefixLift 1065874
  have htrace : WordTrace (prefixWord ++ tailWord_1065874) baseStart_1065874 baseEnd_1065874 := by
    simpa [prefixWord, tailWord_1065874, baseEnd_1065874] using wordTrace_append hprefix tailTrace_1065874
  have hstable : (prefixWord ++ tailWord_1065874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065874).length < 2 ^ (prefixWord ++ tailWord_1065874).sum := by decide
  have hdescent : baseEnd_1065874 < baseStart_1065874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065877 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1065877 : Nat := 118140960795 + 1065877 * 2 ^ 59
def prefixEnd_1065877 : Nat := 4983230072969 + 3 ^ 40 * 1065877 * 2
def baseEnd_1065877 : Nat := 547307219572431485035627

theorem tailTrace_1065877 : CollatzResearch.WordTrace tailWord_1065877 prefixEnd_1065877 547307219572431485035627 := by
  unfold tailWord_1065877
  simp only [CollatzResearch.WordTrace]
  refine ⟨38875727959517141143979885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25917151973011427429319923 38875727959517141143979885)
  ·
    refine ⟨14578397984818927928992457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38875727959517141143979885 14578397984818927928992457)
    ·
      refine ⟨10933798488614195946744343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14578397984818927928992457 10933798488614195946744343)
      ·
        refine ⟨16400697732921293920116515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10933798488614195946744343 16400697732921293920116515)
        ·
          refine ⟨24601046599381940880174773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16400697732921293920116515 24601046599381940880174773)
          ·
            refine ⟨2306348118692056957516385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24601046599381940880174773 2306348118692056957516385)
            ·
              refine ⟨1729761089019042718137289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306348118692056957516385 1729761089019042718137289)
              ·
                refine ⟨1297320816764282038602967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729761089019042718137289 1297320816764282038602967)
                ·
                  refine ⟨1945981225146423057904451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297320816764282038602967 1945981225146423057904451)
                  ·
                    refine ⟨2918971837719634586856677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945981225146423057904451 2918971837719634586856677)
                    ·
                      refine ⟨547307219572431485035627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2918971837719634586856677 547307219572431485035627)
                      ·
                        rfl

theorem cell23_1065877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1065877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065877 prefixEnd_1065877 := by exact prefixLift 1065877
  have htrace : WordTrace (prefixWord ++ tailWord_1065877) baseStart_1065877 baseEnd_1065877 := by
    simpa [prefixWord, tailWord_1065877, baseEnd_1065877] using wordTrace_append hprefix tailTrace_1065877
  have hstable : (prefixWord ++ tailWord_1065877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065877).length < 2 ^ (prefixWord ++ tailWord_1065877).sum := by decide
  have hdescent : baseEnd_1065877 < baseStart_1065877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065923 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_1065923 : Nat := 118140960795 + 1065923 * 2 ^ 59
def prefixEnd_1065923 : Nat := 4983230072969 + 3 ^ 40 * 1065923 * 2
def baseEnd_1065923 : Nat := 547330839682538305060415

theorem tailTrace_1065923 : CollatzResearch.WordTrace tailWord_1065923 prefixEnd_1065923 547330839682538305060415 := by
  unfold tailWord_1065923
  simp only [CollatzResearch.WordTrace]
  refine ⟨38877405717350491000154423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25918270478233660666769615 38877405717350491000154423)
  ·
    refine ⟨58316108576025736500231635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38877405717350491000154423 58316108576025736500231635)
    ·
      refine ⟨87474162864038604750347453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58316108576025736500231635 87474162864038604750347453)
      ·
        refine ⟨32802811074014476781380295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87474162864038604750347453 32802811074014476781380295)
        ·
          refine ⟨49204216611021715172070443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32802811074014476781380295 49204216611021715172070443)
          ·
            refine ⟨73806324916532572758105665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49204216611021715172070443 73806324916532572758105665)
            ·
              refine ⟨55354743687399429568579249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73806324916532572758105665 55354743687399429568579249)
              ·
                refine ⟨41516057765549572176434437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55354743687399429568579249 41516057765549572176434437)
                ·
                  refine ⟨7784260831040544783081457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41516057765549572176434437 7784260831040544783081457)
                  ·
                    refine ⟨5838195623280408587311093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7784260831040544783081457 5838195623280408587311093)
                    ·
                      refine ⟨547330839682538305060415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5838195623280408587311093 547330839682538305060415)
                      ·
                        rfl

theorem cell23_1065923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_1065923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065923 prefixEnd_1065923 := by exact prefixLift 1065923
  have htrace : WordTrace (prefixWord ++ tailWord_1065923) baseStart_1065923 baseEnd_1065923 := by
    simpa [prefixWord, tailWord_1065923, baseEnd_1065923] using wordTrace_append hprefix tailTrace_1065923
  have hstable : (prefixWord ++ tailWord_1065923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065923).length < 2 ^ (prefixWord ++ tailWord_1065923).sum := by decide
  have hdescent : baseEnd_1065923 < baseStart_1065923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065937 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 3, 3, 2]
def baseStart_1065937 : Nat := 118140960795 + 1065937 * 2 ^ 59
def prefixEnd_1065937 : Nat := 4983230072969 + 3 ^ 40 * 1065937 * 2
def baseEnd_1065937 : Nat := 547338028411701250285351

theorem tailTrace_1065937 : CollatzResearch.WordTrace tailWord_1065937 prefixEnd_1065937 547338028411701250285351 := by
  unfold tailWord_1065937
  simp only [CollatzResearch.WordTrace]
  refine ⟨38877916339299771391164065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25918610892866514260776043 38877916339299771391164065)
  ·
    refine ⟨29158437254474828543373049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38877916339299771391164065 29158437254474828543373049)
    ·
      refine ⟨21868827940856121407529787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29158437254474828543373049 21868827940856121407529787)
      ·
        refine ⟨32803241911284182111294681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21868827940856121407529787 32803241911284182111294681)
        ·
          refine ⟨24602431433463136583471011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32803241911284182111294681 24602431433463136583471011)
          ·
            refine ⟨36903647150194704875206517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24602431433463136583471011 36903647150194704875206517)
            ·
              refine ⟨3459716920330753582050611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36903647150194704875206517 3459716920330753582050611)
              ·
                refine ⟨5189575380496130373075917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459716920330753582050611 5189575380496130373075917)
                ·
                  refine ⟨1946090767686048889903469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5189575380496130373075917 1946090767686048889903469)
                  ·
                    refine ⟨729784037882268333713801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946090767686048889903469 729784037882268333713801)
                    ·
                      refine ⟨547338028411701250285351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729784037882268333713801 547338028411701250285351)
                      ·
                        rfl

theorem cell23_1065937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_1065937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065937 prefixEnd_1065937 := by exact prefixLift 1065937
  have htrace : WordTrace (prefixWord ++ tailWord_1065937) baseStart_1065937 baseEnd_1065937 := by
    simpa [prefixWord, tailWord_1065937, baseEnd_1065937] using wordTrace_append hprefix tailTrace_1065937
  have hstable : (prefixWord ++ tailWord_1065937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065937).length < 2 ^ (prefixWord ++ tailWord_1065937).sum := by decide
  have hdescent : baseEnd_1065937 < baseStart_1065937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065943 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 8]
def baseStart_1065943 : Nat := 118140960795 + 1065943 * 2 ^ 59
def prefixEnd_1065943 : Nat := 4983230072969 + 3 ^ 40 * 1065943 * 2
def baseEnd_1065943 : Nat := 182447036431876075603441

theorem tailTrace_1065943 : CollatzResearch.WordTrace tailWord_1065943 prefixEnd_1065943 182447036431876075603441 := by
  unfold tailWord_1065943
  simp only [CollatzResearch.WordTrace]
  refine ⟨38878135177278034415882483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25918756784852022943921655 38878135177278034415882483)
  ·
    refine ⟨58317202765917051623823725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38878135177278034415882483 58317202765917051623823725)
    ·
      refine ⟨21868951037218894358933897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58317202765917051623823725 21868951037218894358933897)
      ·
        refine ⟨16401713277914170769200423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21868951037218894358933897 16401713277914170769200423)
        ·
          refine ⟨24602569916871256153800635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16401713277914170769200423 24602569916871256153800635)
          ·
            refine ⟨36903854875306884230700953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24602569916871256153800635 36903854875306884230700953)
            ·
              refine ⟨27677891156480163173025715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36903854875306884230700953 27677891156480163173025715)
              ·
                refine ⟨41516836734720244759538573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27677891156480163173025715 41516836734720244759538573)
                ·
                  refine ⟨15568813775520091784826965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41516836734720244759538573 15568813775520091784826965)
                  ·
                    refine ⟨182447036431876075603441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15568813775520091784826965 182447036431876075603441)
                    ·
                      rfl

theorem cell23_1065943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_1065943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065943 prefixEnd_1065943 := by exact prefixLift 1065943
  have htrace : WordTrace (prefixWord ++ tailWord_1065943) baseStart_1065943 baseEnd_1065943 := by
    simpa [prefixWord, tailWord_1065943, baseEnd_1065943] using wordTrace_append hprefix tailTrace_1065943
  have hstable : (prefixWord ++ tailWord_1065943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065943).length < 2 ^ (prefixWord ++ tailWord_1065943).sum := by decide
  have hdescent : baseEnd_1065943 < baseStart_1065943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065963 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_1065963 : Nat := 118140960795 + 1065963 * 2 ^ 59
def prefixEnd_1065963 : Nat := 4983230072969 + 3 ^ 40 * 1065963 * 2
def baseEnd_1065963 : Nat := 547351378908718148560231

theorem tailTrace_1065963 : CollatzResearch.WordTrace tailWord_1065963 prefixEnd_1065963 547351378908718148560231 := by
  unfold tailWord_1065963
  simp only [CollatzResearch.WordTrace]
  refine ⟨38878864637205577831610543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25919243091470385221073695 38878864637205577831610543)
  ·
    refine ⟨58318296955808366747415815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38878864637205577831610543 58318296955808366747415815)
    ·
      refine ⟨87477445433712550121123723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58318296955808366747415815 87477445433712550121123723)
      ·
        refine ⟨131216168150568825181685585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87477445433712550121123723 131216168150568825181685585)
        ·
          refine ⟨98412126112926618886264189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131216168150568825181685585 98412126112926618886264189)
          ·
            refine ⟨36904547292347482082349071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98412126112926618886264189 36904547292347482082349071)
            ·
              refine ⟨55356820938521223123523607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36904547292347482082349071 55356820938521223123523607)
              ·
                refine ⟨83035231407781834685285411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55356820938521223123523607 83035231407781834685285411)
                ·
                  refine ⟨124552847111672752027928117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83035231407781834685285411 124552847111672752027928117)
                  ·
                    refine ⟨11676829416719320502618261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124552847111672752027928117 11676829416719320502618261)
                    ·
                      refine ⟨547351378908718148560231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11676829416719320502618261 547351378908718148560231)
                      ·
                        rfl

theorem cell23_1065963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_1065963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065963 prefixEnd_1065963 := by exact prefixLift 1065963
  have htrace : WordTrace (prefixWord ++ tailWord_1065963) baseStart_1065963 baseEnd_1065963 := by
    simpa [prefixWord, tailWord_1065963, baseEnd_1065963] using wordTrace_append hprefix tailTrace_1065963
  have hstable : (prefixWord ++ tailWord_1065963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065963).length < 2 ^ (prefixWord ++ tailWord_1065963).sum := by decide
  have hdescent : baseEnd_1065963 < baseStart_1065963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065980 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_1065980 : Nat := 118140960795 + 1065980 * 2 ^ 59
def prefixEnd_1065980 : Nat := 4983230072969 + 3 ^ 40 * 1065980 * 2
def baseEnd_1065980 : Nat := 547360108079844582047653

theorem tailTrace_1065980 : CollatzResearch.WordTrace tailWord_1065980 prefixEnd_1065980 547360108079844582047653 := by
  unfold tailWord_1065980
  simp only [CollatzResearch.WordTrace]
  refine ⟨19439742339071994867489697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25919656452095993156652929 19439742339071994867489697)
  ·
    refine ⟨14579806754303996150617273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19439742339071994867489697 14579806754303996150617273)
    ·
      refine ⟨10934855065727997112962955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14579806754303996150617273 10934855065727997112962955)
      ·
        refine ⟨16402282598591995669444433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10934855065727997112962955 16402282598591995669444433)
        ·
          refine ⟨12301711948943996752083325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16402282598591995669444433 12301711948943996752083325)
          ·
            refine ⟨4613141980853998782031247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12301711948943996752083325 4613141980853998782031247)
            ·
              refine ⟨6919712971280998173046871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613141980853998782031247 6919712971280998173046871)
              ·
                refine ⟨10379569456921497259570307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6919712971280998173046871 10379569456921497259570307)
                ·
                  refine ⟨15569354185382245889355461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10379569456921497259570307 15569354185382245889355461)
                  ·
                    refine ⟨2919253909759171104254149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15569354185382245889355461 2919253909759171104254149)
                    ·
                      refine ⟨547360108079844582047653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2919253909759171104254149 547360108079844582047653)
                      ·
                        rfl

theorem cell23_1065980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_1065980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065980 prefixEnd_1065980 := by exact prefixLift 1065980
  have htrace : WordTrace (prefixWord ++ tailWord_1065980) baseStart_1065980 baseEnd_1065980 := by
    simpa [prefixWord, tailWord_1065980, baseEnd_1065980] using wordTrace_append hprefix tailTrace_1065980
  have hstable : (prefixWord ++ tailWord_1065980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065980).length < 2 ^ (prefixWord ++ tailWord_1065980).sum := by decide
  have hdescent : baseEnd_1065980 < baseStart_1065980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066000 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_1066000 : Nat := 118140960795 + 1066000 * 2 ^ 59
def prefixEnd_1066000 : Nat := 4983230072969 + 3 ^ 40 * 1066000 * 2
def baseEnd_1066000 : Nat := 547370377692934503797561

theorem tailTrace_1066000 : CollatzResearch.WordTrace tailWord_1066000 prefixEnd_1066000 547370377692934503797561 := by
  unfold tailWord_1066000
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440107069035766575353727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25920142758714355433804969 19440107069035766575353727)
  ·
    refine ⟨29160160603553649863030591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19440107069035766575353727 29160160603553649863030591)
    ·
      refine ⟨43740240905330474794545887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29160160603553649863030591 43740240905330474794545887)
      ·
        refine ⟨65610361357995712191818831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43740240905330474794545887 65610361357995712191818831)
        ·
          refine ⟨98415542036993568287728247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65610361357995712191818831 98415542036993568287728247)
          ·
            refine ⟨147623313055490352431592371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98415542036993568287728247 147623313055490352431592371)
            ·
              refine ⟨221434969583235528647388557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147623313055490352431592371 221434969583235528647388557)
              ·
                refine ⟨83038113593713323242770709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221434969583235528647388557 83038113593713323242770709)
                ·
                  refine ⟨3892411574705312027004877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83038113593713323242770709 3892411574705312027004877)
                  ·
                    refine ⟨1459654340514492010126829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3892411574705312027004877 1459654340514492010126829)
                    ·
                      refine ⟨547370377692934503797561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1459654340514492010126829 547370377692934503797561)
                      ·
                        rfl

theorem cell23_1066000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_1066000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066000 prefixEnd_1066000 := by exact prefixLift 1066000
  have htrace : WordTrace (prefixWord ++ tailWord_1066000) baseStart_1066000 baseEnd_1066000 := by
    simpa [prefixWord, tailWord_1066000, baseEnd_1066000] using wordTrace_append hprefix tailTrace_1066000
  have hstable : (prefixWord ++ tailWord_1066000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066000).length < 2 ^ (prefixWord ++ tailWord_1066000).sum := by decide
  have hdescent : baseEnd_1066000 < baseStart_1066000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066017 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1066017 : Nat := 118140960795 + 1066017 * 2 ^ 59
def prefixEnd_1066017 : Nat := 4983230072969 + 3 ^ 40 * 1066017 * 2
def baseEnd_1066017 : Nat := 547379106864060937284983

theorem tailTrace_1066017 : CollatzResearch.WordTrace tailWord_1066017 prefixEnd_1066017 547379106864060937284983 := by
  unfold tailWord_1066017
  simp only [CollatzResearch.WordTrace]
  refine ⟨38880834179009945054076305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25920556119339963369384203 38880834179009945054076305)
  ·
    refine ⟨29160625634257458790557229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38880834179009945054076305 29160625634257458790557229)
    ·
      refine ⟨10935234612846547046458961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29160625634257458790557229 10935234612846547046458961)
      ·
        refine ⟨8201425959634910284844221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10935234612846547046458961 8201425959634910284844221)
        ·
          refine ⟨3075534734863091356816583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8201425959634910284844221 3075534734863091356816583)
          ·
            refine ⟨4613302102294637035224875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075534734863091356816583 4613302102294637035224875)
            ·
              refine ⟨6919953153441955552837313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613302102294637035224875 6919953153441955552837313)
              ·
                refine ⟨5189964865081466664627985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6919953153441955552837313 5189964865081466664627985)
                ·
                  refine ⟨3892473648811099998470989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5189964865081466664627985 3892473648811099998470989)
                  ·
                    refine ⟨1459677618304162499426621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3892473648811099998470989 1459677618304162499426621)
                    ·
                      refine ⟨547379106864060937284983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1459677618304162499426621 547379106864060937284983)
                      ·
                        rfl

theorem cell23_1066017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1066017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066017 prefixEnd_1066017 := by exact prefixLift 1066017
  have htrace : WordTrace (prefixWord ++ tailWord_1066017) baseStart_1066017 baseEnd_1066017 := by
    simpa [prefixWord, tailWord_1066017, baseEnd_1066017] using wordTrace_append hprefix tailTrace_1066017
  have hstable : (prefixWord ++ tailWord_1066017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066017).length < 2 ^ (prefixWord ++ tailWord_1066017).sum := by decide
  have hdescent : baseEnd_1066017 < baseStart_1066017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066018 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_1066018 : Nat := 118140960795 + 1066018 * 2 ^ 59
def prefixEnd_1066018 : Nat := 4983230072969 + 3 ^ 40 * 1066018 * 2
def baseEnd_1066018 : Nat := 547379620344715433372479

theorem tailTrace_1066018 : CollatzResearch.WordTrace tailWord_1066018 prefixEnd_1066018 547379620344715433372479 := by
  unfold tailWord_1066018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720217663001580556215677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25920580434670881483241805 9720217663001580556215677)
  ·
    refine ⟨3645081623625592708580879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9720217663001580556215677 3645081623625592708580879)
    ·
      refine ⟨5467622435438389062871319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645081623625592708580879 5467622435438389062871319)
      ·
        refine ⟨8201433653157583594306979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5467622435438389062871319 8201433653157583594306979)
        ·
          refine ⟨12302150479736375391460469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8201433653157583594306979 12302150479736375391460469)
          ·
            refine ⟨1153326607475285192949419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12302150479736375391460469 1153326607475285192949419)
            ·
              refine ⟨1729989911212927789424129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153326607475285192949419 1729989911212927789424129)
              ·
                refine ⟨1297492433409695842068097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729989911212927789424129 1297492433409695842068097)
                ·
                  refine ⟨973119325057271881551073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1297492433409695842068097 973119325057271881551073)
                  ·
                    refine ⟨729839493792953911163305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 973119325057271881551073 729839493792953911163305)
                    ·
                      refine ⟨547379620344715433372479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729839493792953911163305 547379620344715433372479)
                      ·
                        rfl

theorem cell23_1066018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_1066018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066018 prefixEnd_1066018 := by exact prefixLift 1066018
  have htrace : WordTrace (prefixWord ++ tailWord_1066018) baseStart_1066018 baseEnd_1066018 := by
    simpa [prefixWord, tailWord_1066018, baseEnd_1066018] using wordTrace_append hprefix tailTrace_1066018
  have hstable : (prefixWord ++ tailWord_1066018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066018).length < 2 ^ (prefixWord ++ tailWord_1066018).sum := by decide
  have hdescent : baseEnd_1066018 < baseStart_1066018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066054 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1066054 : Nat := 118140960795 + 1066054 * 2 ^ 59
def prefixEnd_1066054 : Nat := 4983230072969 + 3 ^ 40 * 1066054 * 2
def baseEnd_1066054 : Nat := 182466035216092430840771

theorem tailTrace_1066054 : CollatzResearch.WordTrace tailWord_1066054 prefixEnd_1066054 182466035216092430840771 := by
  unfold tailWord_1066054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215068239996121886661663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25921455786583933582115477 1215068239996121886661663)
  ·
    refine ⟨1822602359994182829992495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215068239996121886661663 1822602359994182829992495)
    ·
      refine ⟨2733903539991274244988743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1822602359994182829992495 2733903539991274244988743)
      ·
        refine ⟨4100855309986911367483115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2733903539991274244988743 4100855309986911367483115)
        ·
          refine ⟨6151282964980367051224673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100855309986911367483115 6151282964980367051224673)
          ·
            refine ⟨4613462223735275288418505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6151282964980367051224673 4613462223735275288418505)
            ·
              refine ⟨3460096667801456466313879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613462223735275288418505 3460096667801456466313879)
              ·
                refine ⟨5190145001702184699470819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460096667801456466313879 5190145001702184699470819)
                ·
                  refine ⟨7785217502553277049206229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5190145001702184699470819 7785217502553277049206229)
                  ·
                    refine ⟨182466035216092430840771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7785217502553277049206229 182466035216092430840771)
                    ·
                      rfl

theorem cell23_1066054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1066054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066054 prefixEnd_1066054 := by exact prefixLift 1066054
  have htrace : WordTrace (prefixWord ++ tailWord_1066054) baseStart_1066054 baseEnd_1066054 := by
    simpa [prefixWord, tailWord_1066054, baseEnd_1066054] using wordTrace_append hprefix tailTrace_1066054
  have hstable : (prefixWord ++ tailWord_1066054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066054).length < 2 ^ (prefixWord ++ tailWord_1066054).sum := by decide
  have hdescent : baseEnd_1066054 < baseStart_1066054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066057 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 4, 4, 2]
def baseStart_1066057 : Nat := 118140960795 + 1066057 * 2 ^ 59
def prefixEnd_1066057 : Nat := 4983230072969 + 3 ^ 40 * 1066057 * 2
def baseEnd_1066057 : Nat := 547399646090240780784799

theorem tailTrace_1066057 : CollatzResearch.WordTrace tailWord_1066057 prefixEnd_1066057 547399646090240780784799 := by
  unfold tailWord_1066057
  simp only [CollatzResearch.WordTrace]
  refine ⟨38882293098865031885532425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25921528732576687923688283 38882293098865031885532425)
  ·
    refine ⟨29161719824148773914149319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38882293098865031885532425 29161719824148773914149319)
    ·
      refine ⟨43742579736223160871223979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29161719824148773914149319 43742579736223160871223979)
      ·
        refine ⟨65613869604334741306835969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43742579736223160871223979 65613869604334741306835969)
        ·
          refine ⟨49210402203251055980126977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65613869604334741306835969 49210402203251055980126977)
          ·
            refine ⟨36907801652438291985095233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49210402203251055980126977 36907801652438291985095233)
            ·
              refine ⟨27680851239328718988821425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36907801652438291985095233 27680851239328718988821425)
              ·
                refine ⟨20760638429496539241616069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27680851239328718988821425 20760638429496539241616069)
                ·
                  refine ⟨3892619705530601107803013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20760638429496539241616069 3892619705530601107803013)
                  ·
                    refine ⟨729866194786987707713065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892619705530601107803013 729866194786987707713065)
                    ·
                      refine ⟨547399646090240780784799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729866194786987707713065 547399646090240780784799)
                      ·
                        rfl

theorem cell23_1066057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 4, 2].length) (baseStart_1066057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066057 prefixEnd_1066057 := by exact prefixLift 1066057
  have htrace : WordTrace (prefixWord ++ tailWord_1066057) baseStart_1066057 baseEnd_1066057 := by
    simpa [prefixWord, tailWord_1066057, baseEnd_1066057] using wordTrace_append hprefix tailTrace_1066057
  have hstable : (prefixWord ++ tailWord_1066057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066057).length < 2 ^ (prefixWord ++ tailWord_1066057).sum := by decide
  have hdescent : baseEnd_1066057 < baseStart_1066057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066060 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1066060 : Nat := 118140960795 + 1066060 * 2 ^ 59
def prefixEnd_1066060 : Nat := 4983230072969 + 3 ^ 40 * 1066060 * 2
def baseEnd_1066060 : Nat := 547401186532204269047285

theorem tailTrace_1066060 : CollatzResearch.WordTrace tailWord_1066060 prefixEnd_1066060 547401186532204269047285 := by
  unfold tailWord_1066060
  simp only [CollatzResearch.WordTrace]
  refine ⟨19441201258927081698945817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25921601678569442265261089 19441201258927081698945817)
  ·
    refine ⟨14580900944195311274209363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19441201258927081698945817 14580900944195311274209363)
    ·
      refine ⟨21871351416292966911314045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14580900944195311274209363 21871351416292966911314045)
      ·
        refine ⟨8201756781109862591742767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21871351416292966911314045 8201756781109862591742767)
        ·
          refine ⟨12302635171664793887614151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8201756781109862591742767 12302635171664793887614151)
          ·
            refine ⟨18453952757497190831421227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12302635171664793887614151 18453952757497190831421227)
            ·
              refine ⟨27680929136245786247131841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18453952757497190831421227 27680929136245786247131841)
              ·
                refine ⟨20760696852184339685348881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27680929136245786247131841 20760696852184339685348881)
                ·
                  refine ⟨15570522639138254764011661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20760696852184339685348881 15570522639138254764011661)
                  ·
                    refine ⟨5838945989676845536504373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15570522639138254764011661 5838945989676845536504373)
                    ·
                      refine ⟨547401186532204269047285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5838945989676845536504373 547401186532204269047285)
                      ·
                        rfl

theorem cell23_1066060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1066060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066060 prefixEnd_1066060 := by exact prefixLift 1066060
  have htrace : WordTrace (prefixWord ++ tailWord_1066060) baseStart_1066060 baseEnd_1066060 := by
    simpa [prefixWord, tailWord_1066060, baseEnd_1066060] using wordTrace_append hprefix tailTrace_1066060
  have hstable : (prefixWord ++ tailWord_1066060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066060).length < 2 ^ (prefixWord ++ tailWord_1066060).sum := by decide
  have hdescent : baseEnd_1066060 < baseStart_1066060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066080 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 8]
def baseStart_1066080 : Nat := 118140960795 + 1066080 * 2 ^ 59
def prefixEnd_1066080 : Nat := 4983230072969 + 3 ^ 40 * 1066080 * 2
def baseEnd_1066080 : Nat := 60823495127254910088577

theorem tailTrace_1066080 : CollatzResearch.WordTrace tailWord_1066080 prefixEnd_1066080 60823495127254910088577 := by
  unfold tailWord_1066080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19441565988890853406809847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25922087985187804542413129 19441565988890853406809847)
  ·
    refine ⟨29162348983336280110214771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19441565988890853406809847 29162348983336280110214771)
    ·
      refine ⟨43743523475004420165322157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29162348983336280110214771 43743523475004420165322157)
      ·
        refine ⟨16403821303126657561995809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43743523475004420165322157 16403821303126657561995809)
        ·
          refine ⟨12302865977344993171496857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16403821303126657561995809 12302865977344993171496857)
          ·
            refine ⟨9227149483008744878622643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12302865977344993171496857 9227149483008744878622643)
            ·
              refine ⟨13840724224513117317933965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9227149483008744878622643 13840724224513117317933965)
              ·
                refine ⟨5190271584192418994225237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13840724224513117317933965 5190271584192418994225237)
                ·
                  refine ⟨60823495127254910088577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5190271584192418994225237 60823495127254910088577)
                  ·
                    rfl

theorem cell23_1066080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_1066080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066080 prefixEnd_1066080 := by exact prefixLift 1066080
  have htrace : WordTrace (prefixWord ++ tailWord_1066080) baseStart_1066080 baseEnd_1066080 := by
    simpa [prefixWord, tailWord_1066080, baseEnd_1066080] using wordTrace_append hprefix tailTrace_1066080
  have hstable : (prefixWord ++ tailWord_1066080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066080).length < 2 ^ (prefixWord ++ tailWord_1066080).sum := by decide
  have hdescent : baseEnd_1066080 < baseStart_1066080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066174 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1066174 : Nat := 118140960795 + 1066174 * 2 ^ 59
def prefixEnd_1066174 : Nat := 4983230072969 + 3 ^ 40 * 1066174 * 2
def baseEnd_1066174 : Nat := 182486574442272274340587

theorem tailTrace_1066174 : CollatzResearch.WordTrace tailWord_1066174 prefixEnd_1066174 182486574442272274340587 := by
  unfold tailWord_1066174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860820054930145108442697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25924373626294107245027717 4860820054930145108442697)
  ·
    refine ⟨3645615041197608831332023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4860820054930145108442697 3645615041197608831332023)
    ·
      refine ⟨5468422561796413246998035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645615041197608831332023 5468422561796413246998035)
      ·
        refine ⟨8202633842694619870497053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5468422561796413246998035 8202633842694619870497053)
        ·
          refine ⟨3075987691010482451436395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8202633842694619870497053 3075987691010482451436395)
          ·
            refine ⟨4613981536515723677154593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075987691010482451436395 4613981536515723677154593)
            ·
              refine ⟨3460486152386792757865945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613981536515723677154593 3460486152386792757865945)
              ·
                refine ⟨2595364614290094568399459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460486152386792757865945 2595364614290094568399459)
                ·
                  refine ⟨3893046921435141852599189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595364614290094568399459 3893046921435141852599189)
                  ·
                    refine ⟨182486574442272274340587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3893046921435141852599189 182486574442272274340587)
                    ·
                      rfl

theorem cell23_1066174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1066174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066174 prefixEnd_1066174 := by exact prefixLift 1066174
  have htrace : WordTrace (prefixWord ++ tailWord_1066174) baseStart_1066174 baseEnd_1066174 := by
    simpa [prefixWord, tailWord_1066174, baseEnd_1066174] using wordTrace_append hprefix tailTrace_1066174
  have hstable : (prefixWord ++ tailWord_1066174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066174).length < 2 ^ (prefixWord ++ tailWord_1066174).sum := by decide
  have hdescent : baseEnd_1066174 < baseStart_1066174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066182 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1066182 : Nat := 118140960795 + 1066182 * 2 ^ 59
def prefixEnd_1066182 : Nat := 4983230072969 + 3 ^ 40 * 1066182 * 2
def baseEnd_1066182 : Nat := 60829314574672532413525

theorem tailTrace_1066182 : CollatzResearch.WordTrace tailWord_1066182 prefixEnd_1066182 60829314574672532413525 := by
  unfold tailWord_1066182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215214131981630569807275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25924568148941452155888533 1215214131981630569807275)
  ·
    refine ⟨1822821197972445854710913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215214131981630569807275 1822821197972445854710913)
    ·
      refine ⟨1367115898479334391033185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1822821197972445854710913 1367115898479334391033185)
      ·
        refine ⟨1025336923859500793274889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1367115898479334391033185 1025336923859500793274889)
        ·
          refine ⟨769002692894625594956167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025336923859500793274889 769002692894625594956167)
          ·
            refine ⟨1153504039341938392434251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769002692894625594956167 1153504039341938392434251)
            ·
              refine ⟨1730256059012907588651377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153504039341938392434251 1730256059012907588651377)
              ·
                refine ⟨1297692044259680691488533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730256059012907588651377 1297692044259680691488533)
                ·
                  refine ⟨60829314574672532413525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1297692044259680691488533 60829314574672532413525)
                  ·
                    rfl

theorem cell23_1066182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1066182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066182 prefixEnd_1066182 := by exact prefixLift 1066182
  have htrace : WordTrace (prefixWord ++ tailWord_1066182) baseStart_1066182 baseEnd_1066182 := by
    simpa [prefixWord, tailWord_1066182, baseEnd_1066182] using wordTrace_append hprefix tailTrace_1066182
  have hstable : (prefixWord ++ tailWord_1066182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066182).length < 2 ^ (prefixWord ++ tailWord_1066182).sum := by decide
  have hdescent : baseEnd_1066182 < baseStart_1066182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066221 : List Nat := [1, 5, 1, 2, 2, 3, 2, 7]
def baseStart_1066221 : Nat := 118140960795 + 1066221 * 2 ^ 59
def prefixEnd_1066221 : Nat := 4983230072969 + 3 ^ 40 * 1066221 * 2
def baseEnd_1066221 : Nat := 20277179885836227375335

theorem tailTrace_1066221 : CollatzResearch.WordTrace tailWord_1066221 prefixEnd_1066221 20277179885836227375335 := by
  unfold tailWord_1066221
  simp only [CollatzResearch.WordTrace]
  refine ⟨38888274670270887894502517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25925516446847258596335011 38888274670270887894502517)
  ·
    refine ⟨3645775750337895740109611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38888274670270887894502517 3645775750337895740109611)
    ·
      refine ⟨5468663625506843610164417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645775750337895740109611 5468663625506843610164417)
      ·
        refine ⟨4101497719130132707623313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5468663625506843610164417 4101497719130132707623313)
        ·
          refine ⟨3076123289347599530717485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4101497719130132707623313 3076123289347599530717485)
          ·
            refine ⟨1153546233505349824019057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3076123289347599530717485 1153546233505349824019057)
            ·
              refine ⟨865159675129012368014293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153546233505349824019057 865159675129012368014293)
              ·
                refine ⟨20277179885836227375335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 865159675129012368014293 20277179885836227375335)
                ·
                  rfl

theorem cell23_1066221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 7].length) (baseStart_1066221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066221 prefixEnd_1066221 := by exact prefixLift 1066221
  have htrace : WordTrace (prefixWord ++ tailWord_1066221) baseStart_1066221 baseEnd_1066221 := by
    simpa [prefixWord, tailWord_1066221, baseEnd_1066221] using wordTrace_append hprefix tailTrace_1066221
  have hstable : (prefixWord ++ tailWord_1066221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066221).length < 2 ^ (prefixWord ++ tailWord_1066221).sum := by decide
  have hdescent : baseEnd_1066221 < baseStart_1066221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066227 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5]
def baseStart_1066227 : Nat := 118140960795 + 1066227 * 2 ^ 59
def prefixEnd_1066227 : Nat := 4983230072969 + 3 ^ 40 * 1066227 * 2
def baseEnd_1066227 : Nat := 547486937801505115659017

theorem tailTrace_1066227 : CollatzResearch.WordTrace tailWord_1066227 prefixEnd_1066227 547486937801505115659017 := by
  unfold tailWord_1066227
  simp only [CollatzResearch.WordTrace]
  refine ⟨38888493508249150919220935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25925662338832767279480623 38888493508249150919220935)
  ·
    refine ⟨58332740262373726378831403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38888493508249150919220935 58332740262373726378831403)
    ·
      refine ⟨87499110393560589568247105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58332740262373726378831403 87499110393560589568247105)
      ·
        refine ⟨65624332795170442176185329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87499110393560589568247105 65624332795170442176185329)
        ·
          refine ⟨49218249596377831632138997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65624332795170442176185329 49218249596377831632138997)
          ·
            refine ⟨4614210899660421715513031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49218249596377831632138997 4614210899660421715513031)
            ·
              refine ⟨6921316349490632573269547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614210899660421715513031 6921316349490632573269547)
              ·
                refine ⟨10381974524235948859904321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6921316349490632573269547 10381974524235948859904321)
                ·
                  refine ⟨7786480893176961644928241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10381974524235948859904321 7786480893176961644928241)
                  ·
                    refine ⟨5839860669882721233696181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7786480893176961644928241 5839860669882721233696181)
                    ·
                      refine ⟨547486937801505115659017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5839860669882721233696181 547486937801505115659017)
                      ·
                        rfl

theorem cell23_1066227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_1066227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066227 prefixEnd_1066227 := by exact prefixLift 1066227
  have htrace : WordTrace (prefixWord ++ tailWord_1066227) baseStart_1066227 baseEnd_1066227 := by
    simpa [prefixWord, tailWord_1066227, baseEnd_1066227] using wordTrace_append hprefix tailTrace_1066227
  have hstable : (prefixWord ++ tailWord_1066227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066227).length < 2 ^ (prefixWord ++ tailWord_1066227).sum := by decide
  have hdescent : baseEnd_1066227 < baseStart_1066227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066237 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1066237 : Nat := 118140960795 + 1066237 * 2 ^ 59
def prefixEnd_1066237 : Nat := 4983230072969 + 3 ^ 40 * 1066237 * 2
def baseEnd_1066237 : Nat := 547492072608050076533971

theorem tailTrace_1066237 : CollatzResearch.WordTrace tailWord_1066237 prefixEnd_1066237 547492072608050076533971 := by
  unfold tailWord_1066237
  simp only [CollatzResearch.WordTrace]
  refine ⟨38888858238212922627084965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25925905492141948418056643 38888858238212922627084965)
  ·
    refine ⟨7291660919664922992578431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38888858238212922627084965 7291660919664922992578431)
    ·
      refine ⟨10937491379497384488867647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7291660919664922992578431 10937491379497384488867647)
      ·
        refine ⟨16406237069246076733301471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10937491379497384488867647 16406237069246076733301471)
        ·
          refine ⟨24609355603869115099952207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16406237069246076733301471 24609355603869115099952207)
          ·
            refine ⟨36914033405803672649928311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24609355603869115099952207 36914033405803672649928311)
            ·
              refine ⟨55371050108705508974892467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36914033405803672649928311 55371050108705508974892467)
              ·
                refine ⟨83056575163058263462338701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55371050108705508974892467 83056575163058263462338701)
                ·
                  refine ⟨31146215686146848798377013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83056575163058263462338701 31146215686146848798377013)
                  ·
                    refine ⟨2919957720576267074847845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31146215686146848798377013 2919957720576267074847845)
                    ·
                      refine ⟨547492072608050076533971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2919957720576267074847845 547492072608050076533971)
                      ·
                        rfl

theorem cell23_1066237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1066237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066237 prefixEnd_1066237 := by exact prefixLift 1066237
  have htrace : WordTrace (prefixWord ++ tailWord_1066237) baseStart_1066237 baseEnd_1066237 := by
    simpa [prefixWord, tailWord_1066237, baseEnd_1066237] using wordTrace_append hprefix tailTrace_1066237
  have hstable : (prefixWord ++ tailWord_1066237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066237).length < 2 ^ (prefixWord ++ tailWord_1066237).sum := by decide
  have hdescent : baseEnd_1066237 < baseStart_1066237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066257 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_1066257 : Nat := 118140960795 + 1066257 * 2 ^ 59
def prefixEnd_1066257 : Nat := 4983230072969 + 3 ^ 40 * 1066257 * 2
def baseEnd_1066257 : Nat := 547502342221139998283879

theorem tailTrace_1066257 : CollatzResearch.WordTrace tailWord_1066257 prefixEnd_1066257 547502342221139998283879 := by
  unfold tailWord_1066257
  simp only [CollatzResearch.WordTrace]
  refine ⟨38889587698140466042813025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25926391798760310695208683 38889587698140466042813025)
  ·
    refine ⟨29167190773605349532109769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38889587698140466042813025 29167190773605349532109769)
    ·
      refine ⟨21875393080204012149082327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29167190773605349532109769 21875393080204012149082327)
      ·
        refine ⟨32813089620306018223623491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21875393080204012149082327 32813089620306018223623491)
        ·
          refine ⟨49219634430459027335435237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32813089620306018223623491 49219634430459027335435237)
          ·
            refine ⟨9228681455711067625394107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49219634430459027335435237 9228681455711067625394107)
            ·
              refine ⟨13843022183566601438091161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9228681455711067625394107 13843022183566601438091161)
              ·
                refine ⟨10382266637674951078568371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13843022183566601438091161 10382266637674951078568371)
                ·
                  refine ⟨15573399956512426617852557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382266637674951078568371 15573399956512426617852557)
                  ·
                    refine ⟨5840024983692159981694709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15573399956512426617852557 5840024983692159981694709)
                    ·
                      refine ⟨547502342221139998283879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5840024983692159981694709 547502342221139998283879)
                      ·
                        rfl

theorem cell23_1066257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_1066257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066257 prefixEnd_1066257 := by exact prefixLift 1066257
  have htrace : WordTrace (prefixWord ++ tailWord_1066257) baseStart_1066257 baseEnd_1066257 := by
    simpa [prefixWord, tailWord_1066257, baseEnd_1066257] using wordTrace_append hprefix tailTrace_1066257
  have hstable : (prefixWord ++ tailWord_1066257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066257).length < 2 ^ (prefixWord ++ tailWord_1066257).sum := by decide
  have hdescent : baseEnd_1066257 < baseStart_1066257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066267 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4]
def baseStart_1066267 : Nat := 118140960795 + 1066267 * 2 ^ 59
def prefixEnd_1066267 : Nat := 4983230072969 + 3 ^ 40 * 1066267 * 2
def baseEnd_1066267 : Nat := 547507477027684959158833

theorem tailTrace_1066267 : CollatzResearch.WordTrace tailWord_1066267 prefixEnd_1066267 547507477027684959158833 := by
  unfold tailWord_1066267
  simp only [CollatzResearch.WordTrace]
  refine ⟨38889952428104237750677055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25926634952069491833784703 38889952428104237750677055)
  ·
    refine ⟨58334928642156356626015583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38889952428104237750677055 58334928642156356626015583)
    ·
      refine ⟨87502392963234534939023375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58334928642156356626015583 87502392963234534939023375)
      ·
        refine ⟨131253589444851802408535063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87502392963234534939023375 131253589444851802408535063)
        ·
          refine ⟨196880384167277703612802595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131253589444851802408535063 196880384167277703612802595)
          ·
            refine ⟨295320576250916555419203893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196880384167277703612802595 295320576250916555419203893)
            ·
              refine ⟨27686304023523427070550365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 295320576250916555419203893 27686304023523427070550365)
              ·
                refine ⟨10382364008821285151456387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27686304023523427070550365 10382364008821285151456387)
                ·
                  refine ⟨15573546013231927727184581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10382364008821285151456387 15573546013231927727184581)
                  ·
                    refine ⟨2920039877480986448847109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15573546013231927727184581 2920039877480986448847109)
                    ·
                      refine ⟨547507477027684959158833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2920039877480986448847109 547507477027684959158833)
                      ·
                        rfl

theorem cell23_1066267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_1066267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066267 prefixEnd_1066267 := by exact prefixLift 1066267
  have htrace : WordTrace (prefixWord ++ tailWord_1066267) baseStart_1066267 baseEnd_1066267 := by
    simpa [prefixWord, tailWord_1066267, baseEnd_1066267] using wordTrace_append hprefix tailTrace_1066267
  have hstable : (prefixWord ++ tailWord_1066267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066267).length < 2 ^ (prefixWord ++ tailWord_1066267).sum := by decide
  have hdescent : baseEnd_1066267 < baseStart_1066267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066304 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_1066304 : Nat := 118140960795 + 1066304 * 2 ^ 59
def prefixEnd_1066304 : Nat := 4983230072969 + 3 ^ 40 * 1066304 * 2
def baseEnd_1066304 : Nat := 547526475811901314396163

theorem tailTrace_1066304 : CollatzResearch.WordTrace tailWord_1066304 prefixEnd_1066304 547526475811901314396163 := by
  unfold tailWord_1066304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19445650964485096534886983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25927534619313462046515977 19445650964485096534886983)
  ·
    refine ⟨29168476446727644802330475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19445650964485096534886983 29168476446727644802330475)
    ·
      refine ⟨43752714670091467203495713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29168476446727644802330475 43752714670091467203495713)
      ·
        refine ⟨32814536002568600402621785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43752714670091467203495713 32814536002568600402621785)
        ·
          refine ⟨24610902001926450301966339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32814536002568600402621785 24610902001926450301966339)
          ·
            refine ⟨36916353002889675452949509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24610902001926450301966339 36916353002889675452949509)
            ·
              refine ⟨6921816188041814147428033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36916353002889675452949509 6921816188041814147428033)
              ·
                refine ⟨5191362141031360610571025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6921816188041814147428033 5191362141031360610571025)
                ·
                  refine ⟨3893521605773520457928269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191362141031360610571025 3893521605773520457928269)
                  ·
                    refine ⟨1460070602165070171723101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3893521605773520457928269 1460070602165070171723101)
                    ·
                      refine ⟨547526475811901314396163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1460070602165070171723101 547526475811901314396163)
                      ·
                        rfl

theorem cell23_1066304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_1066304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066304 prefixEnd_1066304 := by exact prefixLift 1066304
  have htrace : WordTrace (prefixWord ++ tailWord_1066304) baseStart_1066304 baseEnd_1066304 := by
    simpa [prefixWord, tailWord_1066304, baseEnd_1066304] using wordTrace_append hprefix tailTrace_1066304
  have hstable : (prefixWord ++ tailWord_1066304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066304).length < 2 ^ (prefixWord ++ tailWord_1066304).sum := by decide
  have hdescent : baseEnd_1066304 < baseStart_1066304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066305 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1066305 : Nat := 118140960795 + 1066305 * 2 ^ 59
def prefixEnd_1066305 : Nat := 4983230072969 + 3 ^ 40 * 1066305 * 2
def baseEnd_1066305 : Nat := 547526989292555810483659

theorem tailTrace_1066305 : CollatzResearch.WordTrace tailWord_1066305 prefixEnd_1066305 547526989292555810483659 := by
  unfold tailWord_1066305
  simp only [CollatzResearch.WordTrace]
  refine ⟨38891338401966570240560369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25927558934644380160373579 38891338401966570240560369)
  ·
    refine ⟨29168503801474927680420277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38891338401966570240560369 29168503801474927680420277)
    ·
      refine ⟨2734547231388274470039401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29168503801474927680420277 2734547231388274470039401)
      ·
        refine ⟨2050910423541205852529551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734547231388274470039401 2050910423541205852529551)
        ·
          refine ⟨3076365635311808778794327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050910423541205852529551 3076365635311808778794327)
          ·
            refine ⟨4614548452967713168191491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076365635311808778794327 4614548452967713168191491)
            ·
              refine ⟨6921822679451569752287237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614548452967713168191491 6921822679451569752287237)
              ·
                refine ⟨1297841752397169328553857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6921822679451569752287237 1297841752397169328553857)
                ·
                  refine ⟨973381314297876996415393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1297841752397169328553857 973381314297876996415393)
                  ·
                    refine ⟨730035985723407747311545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 973381314297876996415393 730035985723407747311545)
                    ·
                      refine ⟨547526989292555810483659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730035985723407747311545 547526989292555810483659)
                      ·
                        rfl

theorem cell23_1066305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1066305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066305 prefixEnd_1066305 := by exact prefixLift 1066305
  have htrace : WordTrace (prefixWord ++ tailWord_1066305) baseStart_1066305 baseEnd_1066305 := by
    simpa [prefixWord, tailWord_1066305, baseEnd_1066305] using wordTrace_append hprefix tailTrace_1066305
  have hstable : (prefixWord ++ tailWord_1066305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066305).length < 2 ^ (prefixWord ++ tailWord_1066305).sum := by decide
  have hdescent : baseEnd_1066305 < baseStart_1066305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066307 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 3, 7]
def baseStart_1066307 : Nat := 118140960795 + 1066307 * 2 ^ 59
def prefixEnd_1066307 : Nat := 4983230072969 + 3 ^ 40 * 1066307 * 2
def baseEnd_1066307 : Nat := 182509338751288267552883

theorem tailTrace_1066307 : CollatzResearch.WordTrace tailWord_1066307 prefixEnd_1066307 182509338751288267552883 := by
  unfold tailWord_1066307
  simp only [CollatzResearch.WordTrace]
  refine ⟨38891411347959324582133175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25927607565306216388088783 38891411347959324582133175)
  ·
    refine ⟨58337117021938986873199763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38891411347959324582133175 58337117021938986873199763)
    ·
      refine ⟨87505675532908480309799645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58337117021938986873199763 87505675532908480309799645)
      ·
        refine ⟨32814628324840680116174867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87505675532908480309799645 32814628324840680116174867)
        ·
          refine ⟨49221942487261020174262301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32814628324840680116174867 49221942487261020174262301)
          ·
            refine ⟨18458228432722882565348363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49221942487261020174262301 18458228432722882565348363)
            ·
              refine ⟨27687342649084323848022545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18458228432722882565348363 27687342649084323848022545)
              ·
                refine ⟨20765506986813242886016909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27687342649084323848022545 20765506986813242886016909)
                ·
                  refine ⟨7787065120054966082256341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20765506986813242886016909 7787065120054966082256341)
                  ·
                    refine ⟨182509338751288267552883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7787065120054966082256341 182509338751288267552883)
                    ·
                      rfl

theorem cell23_1066307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_1066307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066307 prefixEnd_1066307 := by exact prefixLift 1066307
  have htrace : WordTrace (prefixWord ++ tailWord_1066307) baseStart_1066307 baseEnd_1066307 := by
    simpa [prefixWord, tailWord_1066307, baseEnd_1066307] using wordTrace_append hprefix tailTrace_1066307
  have hstable : (prefixWord ++ tailWord_1066307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066307).length < 2 ^ (prefixWord ++ tailWord_1066307).sum := by decide
  have hdescent : baseEnd_1066307 < baseStart_1066307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066311 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 5]
def baseStart_1066311 : Nat := 118140960795 + 1066311 * 2 ^ 59
def prefixEnd_1066311 : Nat := 4983230072969 + 3 ^ 40 * 1066311 * 2
def baseEnd_1066311 : Nat := 60836674464053643000959

theorem tailTrace_1066311 : CollatzResearch.WordTrace tailWord_1066311 prefixEnd_1066311 60836674464053643000959 := by
  unfold tailWord_1066311
  simp only [CollatzResearch.WordTrace]
  refine ⟨38891557239944833265278787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25927704826629888843519191 38891557239944833265278787)
  ·
    refine ⟨58337335859917249897918181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38891557239944833265278787 58337335859917249897918181)
    ·
      refine ⟨10938250473734484355859659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58337335859917249897918181 10938250473734484355859659)
      ·
        refine ⟨16407375710601726533789489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10938250473734484355859659 16407375710601726533789489)
        ·
          refine ⟨12305531782951294900342117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16407375710601726533789489 12305531782951294900342117)
          ·
            refine ⟨2307287209303367793814147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12305531782951294900342117 2307287209303367793814147)
            ·
              refine ⟨3460930813955051690721221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307287209303367793814147 3460930813955051690721221)
              ·
                refine ⟨648924527616572192010229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3460930813955051690721221 648924527616572192010229)
                ·
                  refine ⟨60836674464053643000959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 648924527616572192010229 60836674464053643000959)
                  ·
                    rfl

theorem cell23_1066311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 5].length) (baseStart_1066311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066311 prefixEnd_1066311 := by exact prefixLift 1066311
  have htrace : WordTrace (prefixWord ++ tailWord_1066311) baseStart_1066311 baseEnd_1066311 := by
    simpa [prefixWord, tailWord_1066311, baseEnd_1066311] using wordTrace_append hprefix tailTrace_1066311
  have hstable : (prefixWord ++ tailWord_1066311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066311).length < 2 ^ (prefixWord ++ tailWord_1066311).sum := by decide
  have hdescent : baseEnd_1066311 < baseStart_1066311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066324 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1066324 : Nat := 118140960795 + 1066324 * 2 ^ 59
def prefixEnd_1066324 : Nat := 4983230072969 + 3 ^ 40 * 1066324 * 2
def baseEnd_1066324 : Nat := 182512248474997078715357

theorem tailTrace_1066324 : CollatzResearch.WordTrace tailWord_1066324 prefixEnd_1066324 182512248474997078715357 := by
  unfold tailWord_1066324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19446015694448868242751013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25928020925931824323668017 19446015694448868242751013)
  ·
    refine ⟨3646127942709162795515815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19446015694448868242751013 3646127942709162795515815)
    ·
      refine ⟨5469191914063744193273723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3646127942709162795515815 5469191914063744193273723)
      ·
        refine ⟨8203787871095616289910585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469191914063744193273723 8203787871095616289910585)
        ·
          refine ⟨6152840903321712217432939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8203787871095616289910585 6152840903321712217432939)
          ·
            refine ⟨9229261354982568326149409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152840903321712217432939 9229261354982568326149409)
            ·
              refine ⟨6921946016236926244612057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9229261354982568326149409 6921946016236926244612057)
              ·
                refine ⟨5191459512177694683459043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6921946016236926244612057 5191459512177694683459043)
                ·
                  refine ⟨7787189268266542025188565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5191459512177694683459043 7787189268266542025188565)
                  ·
                    refine ⟨182512248474997078715357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7787189268266542025188565 182512248474997078715357)
                    ·
                      rfl

theorem cell23_1066324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1066324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066324 prefixEnd_1066324 := by exact prefixLift 1066324
  have htrace : WordTrace (prefixWord ++ tailWord_1066324) baseStart_1066324 baseEnd_1066324 := by
    simpa [prefixWord, tailWord_1066324, baseEnd_1066324] using wordTrace_append hprefix tailTrace_1066324
  have hstable : (prefixWord ++ tailWord_1066324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066324).length < 2 ^ (prefixWord ++ tailWord_1066324).sum := by decide
  have hdescent : baseEnd_1066324 < baseStart_1066324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066347 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_1066347 : Nat := 118140960795 + 1066347 * 2 ^ 59
def prefixEnd_1066347 : Nat := 4983230072969 + 3 ^ 40 * 1066347 * 2
def baseEnd_1066347 : Nat := 547548555480044646158465

theorem tailTrace_1066347 : CollatzResearch.WordTrace tailWord_1066347 prefixEnd_1066347 547548555480044646158465 := by
  unfold tailWord_1066347
  simp only [CollatzResearch.WordTrace]
  refine ⟨38892870267814411413589295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25928580178542940942392863 38892870267814411413589295)
  ·
    refine ⟨58339305401721617120383943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38892870267814411413589295 58339305401721617120383943)
    ·
      refine ⟨87508958102582425680575915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58339305401721617120383943 87508958102582425680575915)
      ·
        refine ⟨131263437153873638520863873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87508958102582425680575915 131263437153873638520863873)
        ·
          refine ⟨98447577865405228890647905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131263437153873638520863873 98447577865405228890647905)
          ·
            refine ⟨73835683399053921667985929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98447577865405228890647905 73835683399053921667985929)
            ·
              refine ⟨55376762549290441250989447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73835683399053921667985929 55376762549290441250989447)
              ·
                refine ⟨83065143823935661876484171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55376762549290441250989447 83065143823935661876484171)
                ·
                  refine ⟨124597715735903492814726257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83065143823935661876484171 124597715735903492814726257)
                  ·
                    refine ⟨93448286801927619611044693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124597715735903492814726257 93448286801927619611044693)
                    ·
                      refine ⟨547548555480044646158465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 93448286801927619611044693 547548555480044646158465)
                      ·
                        rfl

theorem cell23_1066347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_1066347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066347 prefixEnd_1066347 := by exact prefixLift 1066347
  have htrace : WordTrace (prefixWord ++ tailWord_1066347) baseStart_1066347 baseEnd_1066347 := by
    simpa [prefixWord, tailWord_1066347, baseEnd_1066347] using wordTrace_append hprefix tailTrace_1066347
  have hstable : (prefixWord ++ tailWord_1066347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066347).length < 2 ^ (prefixWord ++ tailWord_1066347).sum := by decide
  have hdescent : baseEnd_1066347 < baseStart_1066347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066361 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 2, 4, 2]
def baseStart_1066361 : Nat := 118140960795 + 1066361 * 2 ^ 59
def prefixEnd_1066361 : Nat := 4983230072969 + 3 ^ 40 * 1066361 * 2
def baseEnd_1066361 : Nat := 547555744209207591383401

theorem tailTrace_1066361 : CollatzResearch.WordTrace tailWord_1066361 prefixEnd_1066361 547555744209207591383401 := by
  unfold tailWord_1066361
  simp only [CollatzResearch.WordTrace]
  refine ⟨38893380889763691804598937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25928920593175794536399291 38893380889763691804598937)
  ·
    refine ⟨29170035667322768853449203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38893380889763691804598937 29170035667322768853449203)
    ·
      refine ⟨43755053500984153280173805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29170035667322768853449203 43755053500984153280173805)
      ·
        refine ⟨16408145062869057480065177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43755053500984153280173805 16408145062869057480065177)
        ·
          refine ⟨12306108797151793110048883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16408145062869057480065177 12306108797151793110048883)
          ·
            refine ⟨18459163195727689665073325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12306108797151793110048883 18459163195727689665073325)
            ·
              refine ⟨6922186198397883624402497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18459163195727689665073325 6922186198397883624402497)
              ·
                refine ⟨5191639648798412718301873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6922186198397883624402497 5191639648798412718301873)
                ·
                  refine ⟨3893729736598809538726405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5191639648798412718301873 3893729736598809538726405)
                  ·
                    refine ⟨730074325612276788511201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893729736598809538726405 730074325612276788511201)
                    ·
                      refine ⟨547555744209207591383401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730074325612276788511201 547555744209207591383401)
                      ·
                        rfl

theorem cell23_1066361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_1066361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066361 prefixEnd_1066361 := by exact prefixLift 1066361
  have htrace : WordTrace (prefixWord ++ tailWord_1066361) baseStart_1066361 baseEnd_1066361 := by
    simpa [prefixWord, tailWord_1066361, baseEnd_1066361] using wordTrace_append hprefix tailTrace_1066361
  have hstable : (prefixWord ++ tailWord_1066361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066361).length < 2 ^ (prefixWord ++ tailWord_1066361).sum := by decide
  have hdescent : baseEnd_1066361 < baseStart_1066361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066371 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 3, 4]
def baseStart_1066371 : Nat := 118140960795 + 1066371 * 2 ^ 59
def prefixEnd_1066371 : Nat := 4983230072969 + 3 ^ 40 * 1066371 * 2
def baseEnd_1066371 : Nat := 182520293005250850752785

theorem tailTrace_1066371 : CollatzResearch.WordTrace tailWord_1066371 prefixEnd_1066371 182520293005250850752785 := by
  unfold tailWord_1066371
  simp only [CollatzResearch.WordTrace]
  refine ⟨38893745619727463512462967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25929163746484975674975311 38893745619727463512462967)
  ·
    refine ⟨58340618429591195268694451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38893745619727463512462967 58340618429591195268694451)
    ·
      refine ⟨87510927644386792903041677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58340618429591195268694451 87510927644386792903041677)
      ·
        refine ⟨32816597866645047338640629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87510927644386792903041677 32816597866645047338640629)
        ·
          refine ⟨3076556049997973187997559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32816597866645047338640629 3076556049997973187997559)
          ·
            refine ⟨4614834074996959781996339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076556049997973187997559 4614834074996959781996339)
            ·
              refine ⟨6922251112495439672994509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614834074996959781996339 6922251112495439672994509)
              ·
                refine ⟨2595844167185789877372941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6922251112495439672994509 2595844167185789877372941)
                ·
                  refine ⟨973441562694671204014853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2595844167185789877372941 973441562694671204014853)
                  ·
                    refine ⟨182520293005250850752785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 973441562694671204014853 182520293005250850752785)
                    ·
                      rfl

theorem cell23_1066371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 4].length) (baseStart_1066371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066371 prefixEnd_1066371 := by exact prefixLift 1066371
  have htrace : WordTrace (prefixWord ++ tailWord_1066371) baseStart_1066371 baseEnd_1066371 := by
    simpa [prefixWord, tailWord_1066371, baseEnd_1066371] using wordTrace_append hprefix tailTrace_1066371
  have hstable : (prefixWord ++ tailWord_1066371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066371).length < 2 ^ (prefixWord ++ tailWord_1066371).sum := by decide
  have hdescent : baseEnd_1066371 < baseStart_1066371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066388 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1066388 : Nat := 118140960795 + 1066388 * 2 ^ 59
def prefixEnd_1066388 : Nat := 4983230072969 + 3 ^ 40 * 1066388 * 2
def baseEnd_1066388 : Nat := 182523202728959661915259

theorem tailTrace_1066388 : CollatzResearch.WordTrace tailWord_1066388 prefixEnd_1066388 182523202728959661915259 := by
  unfold tailWord_1066388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19447182830332937707915909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25929577107110583610554545 19447182830332937707915909)
  ·
    refine ⟨3646346780687425820234233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19447182830332937707915909 3646346780687425820234233)
    ·
      refine ⟨2734760085515569365175675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3646346780687425820234233 2734760085515569365175675)
      ·
        refine ⟨4102140128273354047763513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734760085515569365175675 4102140128273354047763513)
        ·
          refine ⟨3076605096205015535822635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4102140128273354047763513 3076605096205015535822635)
          ·
            refine ⟨4614907644307523303733953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076605096205015535822635 4614907644307523303733953)
            ·
              refine ⟨3461180733230642477800465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4614907644307523303733953 3461180733230642477800465)
              ·
                refine ⟨2595885549922981858350349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461180733230642477800465 2595885549922981858350349)
                ·
                  refine ⟨973457081221118196881381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2595885549922981858350349 973457081221118196881381)
                  ·
                    refine ⟨182523202728959661915259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 973457081221118196881381 182523202728959661915259)
                    ·
                      rfl

theorem cell23_1066388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1066388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066388 prefixEnd_1066388 := by exact prefixLift 1066388
  have htrace : WordTrace (prefixWord ++ tailWord_1066388) baseStart_1066388 baseEnd_1066388 := by
    simpa [prefixWord, tailWord_1066388, baseEnd_1066388] using wordTrace_append hprefix tailTrace_1066388
  have hstable : (prefixWord ++ tailWord_1066388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066388).length < 2 ^ (prefixWord ++ tailWord_1066388).sum := by decide
  have hdescent : baseEnd_1066388 < baseStart_1066388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066461 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1066461 : Nat := 118140960795 + 1066461 * 2 ^ 59
def prefixEnd_1066461 : Nat := 4983230072969 + 3 ^ 40 * 1066461 * 2
def baseEnd_1066461 : Nat := 182535697424885733377647

theorem tailTrace_1066461 : CollatzResearch.WordTrace tailWord_1066461 prefixEnd_1066461 182535697424885733377647 := by
  unfold tailWord_1066461
  simp only [CollatzResearch.WordTrace]
  refine ⟨38897028189401408883239237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25931352126267605922159491 38897028189401408883239237)
  ·
    refine ⟨7293192785512764165607357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38897028189401408883239237 7293192785512764165607357)
    ·
      refine ⟨2734947294567286562102759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7293192785512764165607357 2734947294567286562102759)
      ·
        refine ⟨4102420941850929843154139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734947294567286562102759 4102420941850929843154139)
        ·
          refine ⟨6153631412776394764731209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102420941850929843154139 6153631412776394764731209)
          ·
            refine ⟨4615223559582296073548407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153631412776394764731209 4615223559582296073548407)
            ·
              refine ⟨6922835339373444110322611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615223559582296073548407 6922835339373444110322611)
              ·
                refine ⟨10384253009060166165483917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6922835339373444110322611 10384253009060166165483917)
                ·
                  refine ⟨3894094878397562312056469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10384253009060166165483917 3894094878397562312056469)
                  ·
                    refine ⟨182535697424885733377647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3894094878397562312056469 182535697424885733377647)
                    ·
                      rfl

theorem cell23_1066461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1066461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066461 prefixEnd_1066461 := by exact prefixLift 1066461
  have htrace : WordTrace (prefixWord ++ tailWord_1066461) baseStart_1066461 baseEnd_1066461 := by
    simpa [prefixWord, tailWord_1066461, baseEnd_1066461] using wordTrace_append hprefix tailTrace_1066461
  have hstable : (prefixWord ++ tailWord_1066461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066461).length < 2 ^ (prefixWord ++ tailWord_1066461).sum := by decide
  have hdescent : baseEnd_1066461 < baseStart_1066461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066464 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1066464 : Nat := 118140960795 + 1066464 * 2 ^ 59
def prefixEnd_1066464 : Nat := 4983230072969 + 3 ^ 40 * 1066464 * 2
def baseEnd_1066464 : Nat := 547608632716620688395427

theorem tailTrace_1066464 : CollatzResearch.WordTrace tailWord_1066464 prefixEnd_1066464 547608632716620688395427 := by
  unfold tailWord_1066464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448568804195270197799223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25931425072260360263732297 19448568804195270197799223)
  ·
    refine ⟨29172853206292905296698835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19448568804195270197799223 29172853206292905296698835)
    ·
      refine ⟨43759279809439357945048253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29172853206292905296698835 43759279809439357945048253)
      ·
        refine ⟨16409729928539759229393095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43759279809439357945048253 16409729928539759229393095)
        ·
          refine ⟨24614594892809638844089643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16409729928539759229393095 24614594892809638844089643)
          ·
            refine ⟨36921892339214458266134465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24614594892809638844089643 36921892339214458266134465)
            ·
              refine ⟨27691419254410843699600849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36921892339214458266134465 27691419254410843699600849)
              ·
                refine ⟨20768564440808132774700637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27691419254410843699600849 20768564440808132774700637)
                ·
                  refine ⟨7788211665303049790512739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20768564440808132774700637 7788211665303049790512739)
                  ·
                    refine ⟨11682317497954574685769109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7788211665303049790512739 11682317497954574685769109)
                    ·
                      refine ⟨547608632716620688395427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11682317497954574685769109 547608632716620688395427)
                      ·
                        rfl

theorem cell23_1066464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1066464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066464 prefixEnd_1066464 := by exact prefixLift 1066464
  have htrace : WordTrace (prefixWord ++ tailWord_1066464) baseStart_1066464 baseEnd_1066464 := by
    simpa [prefixWord, tailWord_1066464, baseEnd_1066464] using wordTrace_append hprefix tailTrace_1066464
  have hstable : (prefixWord ++ tailWord_1066464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066464).length < 2 ^ (prefixWord ++ tailWord_1066464).sum := by decide
  have hdescent : baseEnd_1066464 < baseStart_1066464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066474 : List Nat := [3, 1, 3, 1, 15]
def baseStart_1066474 : Nat := 118140960795 + 1066474 * 2 ^ 59
def prefixEnd_1066474 : Nat := 4983230072969 + 3 ^ 40 * 1066474 * 2
def baseEnd_1066474 : Nat := 751184866286921329589

theorem tailTrace_1066474 : CollatzResearch.WordTrace tailWord_1066474 prefixEnd_1066474 751184866286921329589 := by
  unfold tailWord_1066474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724375584588578025865619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25931668225569541402308317 9724375584588578025865619)
  ·
    refine ⟨14586563376882867038798429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9724375584588578025865619 14586563376882867038798429)
    ·
      refine ⟨5469961266331075139549411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14586563376882867038798429 5469961266331075139549411)
      ·
        refine ⟨8204941899496612709324117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469961266331075139549411 8204941899496612709324117)
        ·
          refine ⟨751184866286921329589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 8204941899496612709324117 751184866286921329589)
          ·
            rfl

theorem cell23_1066474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 15].length) (baseStart_1066474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066474 prefixEnd_1066474 := by exact prefixLift 1066474
  have htrace : WordTrace (prefixWord ++ tailWord_1066474) baseStart_1066474 baseEnd_1066474 := by
    simpa [prefixWord, tailWord_1066474, baseEnd_1066474] using wordTrace_append hprefix tailTrace_1066474
  have hstable : (prefixWord ++ tailWord_1066474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066474).length < 2 ^ (prefixWord ++ tailWord_1066474).sum := by decide
  have hdescent : baseEnd_1066474 < baseStart_1066474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066508 : List Nat := [2, 2, 1, 2, 5, 1, 3, 7]
def baseStart_1066508 : Nat := 118140960795 + 1066508 * 2 ^ 59
def prefixEnd_1066508 : Nat := 4983230072969 + 3 ^ 40 * 1066508 * 2
def baseEnd_1066508 : Nat := 20282637995015500601675

theorem tailTrace_1066508 : CollatzResearch.WordTrace tailWord_1066508 prefixEnd_1066508 20282637995015500601675 := by
  unfold tailWord_1066508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19449371210115567955100089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25932494946820757273466785 19449371210115567955100089)
  ·
    refine ⟨14587028407586675966325067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19449371210115567955100089 14587028407586675966325067)
    ·
      refine ⟨21880542611380013949487601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14587028407586675966325067 21880542611380013949487601)
      ·
        refine ⟨16410406958535010462115701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21880542611380013949487601 16410406958535010462115701)
        ·
          refine ⟨1538475652362657230823347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16410406958535010462115701 1538475652362657230823347)
          ·
            refine ⟨2307713478543985846235021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538475652362657230823347 2307713478543985846235021)
            ·
              refine ⟨865392554453994692338133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2307713478543985846235021 865392554453994692338133)
              ·
                refine ⟨20282637995015500601675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 865392554453994692338133 20282637995015500601675)
                ·
                  rfl

theorem cell23_1066508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 7].length) (baseStart_1066508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066508 prefixEnd_1066508 := by exact prefixLift 1066508
  have htrace : WordTrace (prefixWord ++ tailWord_1066508) baseStart_1066508 baseEnd_1066508 := by
    simpa [prefixWord, tailWord_1066508, baseEnd_1066508] using wordTrace_append hprefix tailTrace_1066508
  have hstable : (prefixWord ++ tailWord_1066508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066508).length < 2 ^ (prefixWord ++ tailWord_1066508).sum := by decide
  have hdescent : baseEnd_1066508 < baseStart_1066508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066551 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 2, 6]
def baseStart_1066551 : Nat := 118140960795 + 1066551 * 2 ^ 59
def prefixEnd_1066551 : Nat := 4983230072969 + 3 ^ 40 * 1066551 * 2
def baseEnd_1066551 : Nat := 182551101844520616002509

theorem tailTrace_1066551 : CollatzResearch.WordTrace tailWord_1066551 prefixEnd_1066551 182551101844520616002509 := by
  unfold tailWord_1066551
  simp only [CollatzResearch.WordTrace]
  refine ⟨38900310759075354254015507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25933540506050236169343671 38900310759075354254015507)
  ·
    refine ⟨58350466138613031381023261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38900310759075354254015507 58350466138613031381023261)
    ·
      refine ⟨21881424801979886767883723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58350466138613031381023261 21881424801979886767883723)
      ·
        refine ⟨32822137202969830151825585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21881424801979886767883723 32822137202969830151825585)
        ·
          refine ⟨24616602902227372613869189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32822137202969830151825585 24616602902227372613869189)
          ·
            refine ⟨4615613044167632365100473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24616602902227372613869189 4615613044167632365100473)
            ·
              refine ⟨3461709783125724273825355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615613044167632365100473 3461709783125724273825355)
              ·
                refine ⟨5192564674688586410738033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461709783125724273825355 5192564674688586410738033)
                ·
                  refine ⟨3894423506016439808053525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5192564674688586410738033 3894423506016439808053525)
                  ·
                    refine ⟨182551101844520616002509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3894423506016439808053525 182551101844520616002509)
                    ·
                      rfl

theorem cell23_1066551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_1066551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066551 prefixEnd_1066551 := by exact prefixLift 1066551
  have htrace : WordTrace (prefixWord ++ tailWord_1066551) baseStart_1066551 baseEnd_1066551 := by
    simpa [prefixWord, tailWord_1066551, baseEnd_1066551] using wordTrace_append hprefix tailTrace_1066551
  have hstable : (prefixWord ++ tailWord_1066551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066551).length < 2 ^ (prefixWord ++ tailWord_1066551).sum := by decide
  have hdescent : baseEnd_1066551 < baseStart_1066551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066552 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 2, 1, 3]
def baseStart_1066552 : Nat := 118140960795 + 1066552 * 2 ^ 59
def prefixEnd_1066552 : Nat := 4983230072969 + 3 ^ 40 * 1066552 * 2
def baseEnd_1066552 : Nat := 547653819014216344095023

theorem tailTrace_1066552 : CollatzResearch.WordTrace tailWord_1066552 prefixEnd_1066552 547653819014216344095023 := by
  unfold tailWord_1066552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19450173616035865712400955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25933564821381154283201273 19450173616035865712400955)
  ·
    refine ⟨29175260424053798568601433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19450173616035865712400955 29175260424053798568601433)
    ·
      refine ⟨21881445318040348926451075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29175260424053798568601433 21881445318040348926451075)
      ·
        refine ⟨32822167977060523389676613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21881445318040348926451075 32822167977060523389676613)
        ·
          refine ⟨6154156495698848135564365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32822167977060523389676613 6154156495698848135564365)
          ·
            refine ⟨2307808685887068050836637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6154156495698848135564365 2307808685887068050836637)
            ·
              refine ⟨865428257207650519063739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2307808685887068050836637 865428257207650519063739)
              ·
                refine ⟨1298142385811475778595609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865428257207650519063739 1298142385811475778595609)
                ·
                  refine ⟨973606789358606833946707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1298142385811475778595609 973606789358606833946707)
                  ·
                    refine ⟨1460410184037910250920061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 973606789358606833946707 1460410184037910250920061)
                    ·
                      refine ⟨547653819014216344095023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1460410184037910250920061 547653819014216344095023)
                      ·
                        rfl

theorem cell23_1066552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_1066552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066552 prefixEnd_1066552 := by exact prefixLift 1066552
  have htrace : WordTrace (prefixWord ++ tailWord_1066552) baseStart_1066552 baseEnd_1066552 := by
    simpa [prefixWord, tailWord_1066552, baseEnd_1066552] using wordTrace_append hprefix tailTrace_1066552
  have hstable : (prefixWord ++ tailWord_1066552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066552).length < 2 ^ (prefixWord ++ tailWord_1066552).sum := by decide
  have hdescent : baseEnd_1066552 < baseStart_1066552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066578 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1066578 : Nat := 118140960795 + 1066578 * 2 ^ 59
def prefixEnd_1066578 : Nat := 4983230072969 + 3 ^ 40 * 1066578 * 2
def baseEnd_1066578 : Nat := 547667169511233242369903

theorem tailTrace_1066578 : CollatzResearch.WordTrace tailWord_1066578 prefixEnd_1066578 547667169511233242369903 := by
  unfold tailWord_1066578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9725323882494384466312097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25934197019985025243498925 9725323882494384466312097)
  ·
    refine ⟨7293992911870788349734073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9725323882494384466312097 7293992911870788349734073)
    ·
      refine ⟨5470494683903091262300555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7293992911870788349734073 5470494683903091262300555)
      ·
        refine ⟨8205742025854636893450833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470494683903091262300555 8205742025854636893450833)
        ·
          refine ⟨6154306519390977670088125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8205742025854636893450833 6154306519390977670088125)
          ·
            refine ⟨2307864944771616626283047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6154306519390977670088125 2307864944771616626283047)
            ·
              refine ⟨3461797417157424939424571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307864944771616626283047 3461797417157424939424571)
              ·
                refine ⟨5192696125736137409136857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461797417157424939424571 5192696125736137409136857)
                ·
                  refine ⟨3894522094302103056852643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5192696125736137409136857 3894522094302103056852643)
                  ·
                    refine ⟨5841783141453154585278965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3894522094302103056852643 5841783141453154585278965)
                    ·
                      refine ⟨547667169511233242369903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5841783141453154585278965 547667169511233242369903)
                      ·
                        rfl

theorem cell23_1066578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1066578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066578 prefixEnd_1066578 := by exact prefixLift 1066578
  have htrace : WordTrace (prefixWord ++ tailWord_1066578) baseStart_1066578 baseEnd_1066578 := by
    simpa [prefixWord, tailWord_1066578, baseEnd_1066578] using wordTrace_append hprefix tailTrace_1066578
  have hstable : (prefixWord ++ tailWord_1066578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066578).length < 2 ^ (prefixWord ++ tailWord_1066578).sum := by decide
  have hdescent : baseEnd_1066578 < baseStart_1066578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066618 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2]
def baseStart_1066618 : Nat := 118140960795 + 1066618 * 2 ^ 59
def prefixEnd_1066618 : Nat := 4983230072969 + 3 ^ 40 * 1066618 * 2
def baseEnd_1066618 : Nat := 547687708737413085869719

theorem tailTrace_1066618 : CollatzResearch.WordTrace tailWord_1066618 prefixEnd_1066618 547687708737413085869719 := by
  unfold tailWord_1066618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9725688612458156174176127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25935169633221749797803005 9725688612458156174176127)
  ·
    refine ⟨14588532918687234261264191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9725688612458156174176127 14588532918687234261264191)
    ·
      refine ⟨21882799378030851391896287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14588532918687234261264191 21882799378030851391896287)
      ·
        refine ⟨32824199067046277087844431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21882799378030851391896287 32824199067046277087844431)
        ·
          refine ⟨49236298600569415631766647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32824199067046277087844431 49236298600569415631766647)
          ·
            refine ⟨73854447900854123447649971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49236298600569415631766647 73854447900854123447649971)
            ·
              refine ⟨110781671851281185171474957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73854447900854123447649971 110781671851281185171474957)
              ·
                refine ⟨41543126944230444439303109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110781671851281185171474957 41543126944230444439303109)
                ·
                  refine ⟨7789336302043208332369333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41543126944230444439303109 7789336302043208332369333)
                  ·
                    refine ⟨730250278316550781159625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7789336302043208332369333 730250278316550781159625)
                    ·
                      refine ⟨547687708737413085869719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730250278316550781159625 547687708737413085869719)
                      ·
                        rfl

theorem cell23_1066618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_1066618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066618 prefixEnd_1066618 := by exact prefixLift 1066618
  have htrace : WordTrace (prefixWord ++ tailWord_1066618) baseStart_1066618 baseEnd_1066618 := by
    simpa [prefixWord, tailWord_1066618, baseEnd_1066618] using wordTrace_append hprefix tailTrace_1066618
  have hstable : (prefixWord ++ tailWord_1066618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066618).length < 2 ^ (prefixWord ++ tailWord_1066618).sum := by decide
  have hdescent : baseEnd_1066618 < baseStart_1066618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066638 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1066638 : Nat := 118140960795 + 1066638 * 2 ^ 59
def prefixEnd_1066638 : Nat := 4983230072969 + 3 ^ 40 * 1066638 * 2
def baseEnd_1066638 : Nat := 547697978350503007619627

theorem tailTrace_1066638 : CollatzResearch.WordTrace tailWord_1066638 prefixEnd_1066638 547697978350503007619627 := by
  unfold tailWord_1066638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4862935488720021014054071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25935655939840112074955045 4862935488720021014054071)
  ·
    refine ⟨7294403233080031521081107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4862935488720021014054071 7294403233080031521081107)
    ·
      refine ⟨10941604849620047281621661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7294403233080031521081107 10941604849620047281621661)
      ·
        refine ⟨4103101818607517730608123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10941604849620047281621661 4103101818607517730608123)
        ·
          refine ⟨6154652727911276595912185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103101818607517730608123 6154652727911276595912185)
          ·
            refine ⟨4615989545933457446934139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154652727911276595912185 4615989545933457446934139)
            ·
              refine ⟨6923984318900186170401209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615989545933457446934139 6923984318900186170401209)
              ·
                refine ⟨5192988239175139627800907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6923984318900186170401209 5192988239175139627800907)
                ·
                  refine ⟨7789482358762709441701361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192988239175139627800907 7789482358762709441701361)
                  ·
                    refine ⟨5842111769072032081276021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7789482358762709441701361 5842111769072032081276021)
                    ·
                      refine ⟨547697978350503007619627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5842111769072032081276021 547697978350503007619627)
                      ·
                        rfl

theorem cell23_1066638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1066638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066638 prefixEnd_1066638 := by exact prefixLift 1066638
  have htrace : WordTrace (prefixWord ++ tailWord_1066638) baseStart_1066638 baseEnd_1066638 := by
    simpa [prefixWord, tailWord_1066638, baseEnd_1066638] using wordTrace_append hprefix tailTrace_1066638
  have hstable : (prefixWord ++ tailWord_1066638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066638).length < 2 ^ (prefixWord ++ tailWord_1066638).sum := by decide
  have hdescent : baseEnd_1066638 < baseStart_1066638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066691 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_1066691 : Nat := 118140960795 + 1066691 * 2 ^ 59
def prefixEnd_1066691 : Nat := 4983230072969 + 3 ^ 40 * 1066691 * 2
def baseEnd_1066691 : Nat := 547725192825191300256883

theorem tailTrace_1066691 : CollatzResearch.WordTrace tailWord_1066691 prefixEnd_1066691 547725192825191300256883 := by
  unfold tailWord_1066691
  simp only [CollatzResearch.WordTrace]
  refine ⟨38905416978568158164111927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25936944652378772109407951 38905416978568158164111927)
  ·
    refine ⟨58358125467852237246167891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38905416978568158164111927 58358125467852237246167891)
    ·
      refine ⟨87537188201778355869251837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58358125467852237246167891 87537188201778355869251837)
      ·
        refine ⟨32826445575666883450969439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87537188201778355869251837 32826445575666883450969439)
        ·
          refine ⟨49239668363500325176454159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32826445575666883450969439 49239668363500325176454159)
          ·
            refine ⟨73859502545250487764681239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49239668363500325176454159 73859502545250487764681239)
            ·
              refine ⟨110789253817875731647021859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73859502545250487764681239 110789253817875731647021859)
              ·
                refine ⟨166183880726813597470532789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110789253817875731647021859 166183880726813597470532789)
                ·
                  refine ⟨15579738818138774762862449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166183880726813597470532789 15579738818138774762862449)
                  ·
                    refine ⟨11684804113604081072146837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15579738818138774762862449 11684804113604081072146837)
                    ·
                      refine ⟨547725192825191300256883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11684804113604081072146837 547725192825191300256883)
                      ·
                        rfl

theorem cell23_1066691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_1066691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066691 prefixEnd_1066691 := by exact prefixLift 1066691
  have htrace : WordTrace (prefixWord ++ tailWord_1066691) baseStart_1066691 baseEnd_1066691 := by
    simpa [prefixWord, tailWord_1066691, baseEnd_1066691] using wordTrace_append hprefix tailTrace_1066691
  have hstable : (prefixWord ++ tailWord_1066691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066691).length < 2 ^ (prefixWord ++ tailWord_1066691).sum := by decide
  have hdescent : baseEnd_1066691 < baseStart_1066691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066705 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 6]
def baseStart_1066705 : Nat := 118140960795 + 1066705 * 2 ^ 59
def prefixEnd_1066705 : Nat := 4983230072969 + 3 ^ 40 * 1066705 * 2
def baseEnd_1066705 : Nat := 60859153506039360609091

theorem tailTrace_1066705 : CollatzResearch.WordTrace tailWord_1066705 prefixEnd_1066705 60859153506039360609091 := by
  unfold tailWord_1066705
  simp only [CollatzResearch.WordTrace]
  refine ⟨38905927600517438555121569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25937285067011625703414379 38905927600517438555121569)
  ·
    refine ⟨29179445700388078916341177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38905927600517438555121569 29179445700388078916341177)
    ·
      refine ⟨21884584275291059187255883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29179445700388078916341177 21884584275291059187255883)
      ·
        refine ⟨32826876412936588780883825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21884584275291059187255883 32826876412936588780883825)
        ·
          refine ⟨24620157309702441585662869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32826876412936588780883825 24620157309702441585662869)
          ·
            refine ⟨1154069873892301949327947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24620157309702441585662869 1154069873892301949327947)
            ·
              refine ⟨1731104810838452923991921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154069873892301949327947 1731104810838452923991921)
              ·
                refine ⟨1298328608128839692993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731104810838452923991921 1298328608128839692993941)
                ·
                  refine ⟨60859153506039360609091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1298328608128839692993941 60859153506039360609091)
                  ·
                    rfl

theorem cell23_1066705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 6].length) (baseStart_1066705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066705 prefixEnd_1066705 := by exact prefixLift 1066705
  have htrace : WordTrace (prefixWord ++ tailWord_1066705) baseStart_1066705 baseEnd_1066705 := by
    simpa [prefixWord, tailWord_1066705, baseEnd_1066705] using wordTrace_append hprefix tailTrace_1066705
  have hstable : (prefixWord ++ tailWord_1066705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066705).length < 2 ^ (prefixWord ++ tailWord_1066705).sum := by decide
  have hdescent : baseEnd_1066705 < baseStart_1066705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066725 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 3, 5, 2]
def baseStart_1066725 : Nat := 118140960795 + 1066725 * 2 ^ 59
def prefixEnd_1066725 : Nat := 4983230072969 + 3 ^ 40 * 1066725 * 2
def baseEnd_1066725 : Nat := 547742651167444167231727

theorem tailTrace_1066725 : CollatzResearch.WordTrace tailWord_1066725 prefixEnd_1066725 547742651167444167231727 := by
  unfold tailWord_1066725
  simp only [CollatzResearch.WordTrace]
  refine ⟨38906657060444981970849629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25937771373629987980566419 38906657060444981970849629)
  ·
    refine ⟨14589996397666868239068611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38906657060444981970849629 14589996397666868239068611)
    ·
      refine ⟨21884994596500302358602917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14589996397666868239068611 21884994596500302358602917)
      ·
        refine ⟨4103436486843806692238047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21884994596500302358602917 4103436486843806692238047)
        ·
          refine ⟨6155154730265710038357071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103436486843806692238047 6155154730265710038357071)
          ·
            refine ⟨9232732095398565057535607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155154730265710038357071 9232732095398565057535607)
            ·
              refine ⟨13849098143097847586303411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9232732095398565057535607 13849098143097847586303411)
              ·
                refine ⟨20773647214646771379455117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13849098143097847586303411 20773647214646771379455117)
                ·
                  refine ⟨7790117705492539267295669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20773647214646771379455117 7790117705492539267295669)
                  ·
                    refine ⟨730323534889925556308969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7790117705492539267295669 730323534889925556308969)
                    ·
                      refine ⟨547742651167444167231727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730323534889925556308969 547742651167444167231727)
                      ·
                        rfl

theorem cell23_1066725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_1066725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066725 prefixEnd_1066725 := by exact prefixLift 1066725
  have htrace : WordTrace (prefixWord ++ tailWord_1066725) baseStart_1066725 baseEnd_1066725 := by
    simpa [prefixWord, tailWord_1066725, baseEnd_1066725] using wordTrace_append hprefix tailTrace_1066725
  have hstable : (prefixWord ++ tailWord_1066725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066725).length < 2 ^ (prefixWord ++ tailWord_1066725).sum := by decide
  have hdescent : baseEnd_1066725 < baseStart_1066725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066735 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 1, 5]
def baseStart_1066735 : Nat := 118140960795 + 1066735 * 2 ^ 59
def prefixEnd_1066735 : Nat := 4983230072969 + 3 ^ 40 * 1066735 * 2
def baseEnd_1066735 : Nat := 182582595324663042702227

theorem tailTrace_1066735 : CollatzResearch.WordTrace tailWord_1066735 prefixEnd_1066735 182582595324663042702227 := by
  unfold tailWord_1066735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38907021790408753678713659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25938014526939169119142439 38907021790408753678713659)
  ·
    refine ⟨58360532685613130518070489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38907021790408753678713659 58360532685613130518070489)
    ·
      refine ⟨43770399514209847888552867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58360532685613130518070489 43770399514209847888552867)
      ·
        refine ⟨65655599271314771832829301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43770399514209847888552867 65655599271314771832829301)
        ·
          refine ⟨6155212431685759859327747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65655599271314771832829301 6155212431685759859327747)
          ·
            refine ⟨9232818647528639788991621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155212431685759859327747 9232818647528639788991621)
            ·
              refine ⟨1731153496411619960435929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9232818647528639788991621 1731153496411619960435929)
              ·
                refine ⟨1298365122308714970326947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731153496411619960435929 1298365122308714970326947)
                ·
                  refine ⟨1947547683463072455490421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298365122308714970326947 1947547683463072455490421)
                  ·
                    refine ⟨182582595324663042702227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1947547683463072455490421 182582595324663042702227)
                    ·
                      rfl

theorem cell23_1066735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_1066735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066735 prefixEnd_1066735 := by exact prefixLift 1066735
  have htrace : WordTrace (prefixWord ++ tailWord_1066735) baseStart_1066735 baseEnd_1066735 := by
    simpa [prefixWord, tailWord_1066735, baseEnd_1066735] using wordTrace_append hprefix tailTrace_1066735
  have hstable : (prefixWord ++ tailWord_1066735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066735).length < 2 ^ (prefixWord ++ tailWord_1066735).sum := by decide
  have hdescent : baseEnd_1066735 < baseStart_1066735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066742 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_1066742 : Nat := 118140960795 + 1066742 * 2 ^ 59
def prefixEnd_1066742 : Nat := 4983230072969 + 3 ^ 40 * 1066742 * 2
def baseEnd_1066742 : Nat := 547751380338570600719149

theorem tailTrace_1066742 : CollatzResearch.WordTrace tailWord_1066742 prefixEnd_1066742 547751380338570600719149 := by
  unfold tailWord_1066742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431704818836462117138655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25938184734255595916145653 2431704818836462117138655)
  ·
    refine ⟨3647557228254693175707983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2431704818836462117138655 3647557228254693175707983)
    ·
      refine ⟨5471335842382039763561975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3647557228254693175707983 5471335842382039763561975)
      ·
        refine ⟨8207003763573059645342963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5471335842382039763561975 8207003763573059645342963)
        ·
          refine ⟨12310505645359589468014445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8207003763573059645342963 12310505645359589468014445)
          ·
            refine ⟨4616439617009846050505417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12310505645359589468014445 4616439617009846050505417)
            ·
              refine ⟨3462329712757384537879063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4616439617009846050505417 3462329712757384537879063)
              ·
                refine ⟨5193494569136076806818595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462329712757384537879063 5193494569136076806818595)
                ·
                  refine ⟨7790241853704115210227893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5193494569136076806818595 7790241853704115210227893)
                  ·
                    refine ⟨730335173784760800958865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7790241853704115210227893 730335173784760800958865)
                    ·
                      refine ⟨547751380338570600719149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730335173784760800958865 547751380338570600719149)
                      ·
                        rfl

theorem cell23_1066742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_1066742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066742 prefixEnd_1066742 := by exact prefixLift 1066742
  have htrace : WordTrace (prefixWord ++ tailWord_1066742) baseStart_1066742 baseEnd_1066742 := by
    simpa [prefixWord, tailWord_1066742, baseEnd_1066742] using wordTrace_append hprefix tailTrace_1066742
  have hstable : (prefixWord ++ tailWord_1066742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066742).length < 2 ^ (prefixWord ++ tailWord_1066742).sum := by decide
  have hdescent : baseEnd_1066742 < baseStart_1066742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066748 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1066748 : Nat := 118140960795 + 1066748 * 2 ^ 59
def prefixEnd_1066748 : Nat := 4983230072969 + 3 ^ 40 * 1066748 * 2
def baseEnd_1066748 : Nat := 182584820407499192414707

theorem tailTrace_1066748 : CollatzResearch.WordTrace tailWord_1066748 prefixEnd_1066748 182584820407499192414707 := by
  unfold tailWord_1066748
  simp only [CollatzResearch.WordTrace]
  refine ⟨19453747969680828449468449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25938330626241104599291265 19453747969680828449468449)
  ·
    refine ⟨14590310977260621337101337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19453747969680828449468449 14590310977260621337101337)
    ·
      refine ⟨10942733232945466002826003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14590310977260621337101337 10942733232945466002826003)
      ·
        refine ⟨16414099849418199004239005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10942733232945466002826003 16414099849418199004239005)
        ·
          refine ⟨6155287443531824626589627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16414099849418199004239005 6155287443531824626589627)
          ·
            refine ⟨9232931165297736939884441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155287443531824626589627 9232931165297736939884441)
            ·
              refine ⟨6924698373973302704913331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9232931165297736939884441 6924698373973302704913331)
              ·
                refine ⟨10387047560959954057369997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6924698373973302704913331 10387047560959954057369997)
                ·
                  refine ⟨3895142835359982771513749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10387047560959954057369997 3895142835359982771513749)
                  ·
                    refine ⟨182584820407499192414707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3895142835359982771513749 182584820407499192414707)
                    ·
                      rfl

theorem cell23_1066748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1066748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066748 prefixEnd_1066748 := by exact prefixLift 1066748
  have htrace : WordTrace (prefixWord ++ tailWord_1066748) baseStart_1066748 baseEnd_1066748 := by
    simpa [prefixWord, tailWord_1066748, baseEnd_1066748] using wordTrace_append hprefix tailTrace_1066748
  have hstable : (prefixWord ++ tailWord_1066748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066748).length < 2 ^ (prefixWord ++ tailWord_1066748).sum := by decide
  have hdescent : baseEnd_1066748 < baseStart_1066748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066755 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 4]
def baseStart_1066755 : Nat := 118140960795 + 1066755 * 2 ^ 59
def prefixEnd_1066755 : Nat := 4983230072969 + 3 ^ 40 * 1066755 * 2
def baseEnd_1066755 : Nat := 547758055587079049856589

theorem tailTrace_1066755 : CollatzResearch.WordTrace tailWord_1066755 prefixEnd_1066755 547758055587079049856589 := by
  unfold tailWord_1066755
  simp only [CollatzResearch.WordTrace]
  refine ⟨38907751250336297094441719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25938500833557531396294479 38907751250336297094441719)
  ·
    refine ⟨58361626875504445641662579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38907751250336297094441719 58361626875504445641662579)
    ·
      refine ⟨87542440313256668462493869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58361626875504445641662579 87542440313256668462493869)
      ·
        refine ⟨32828415117471250673435201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87542440313256668462493869 32828415117471250673435201)
        ·
          refine ⟨24621311338103438005076401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32828415117471250673435201 24621311338103438005076401)
          ·
            refine ⟨18465983503577578503807301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24621311338103438005076401 18465983503577578503807301)
            ·
              refine ⟨3462371906920795969463869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18465983503577578503807301 3462371906920795969463869)
              ·
                refine ⟨1298389465095298488548951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3462371906920795969463869 1298389465095298488548951)
                ·
                  refine ⟨1947584197642947732823427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298389465095298488548951 1947584197642947732823427)
                  ·
                    refine ⟨2921376296464421599235141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947584197642947732823427 2921376296464421599235141)
                    ·
                      refine ⟨547758055587079049856589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2921376296464421599235141 547758055587079049856589)
                      ·
                        rfl

theorem cell23_1066755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_1066755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066755 prefixEnd_1066755 := by exact prefixLift 1066755
  have htrace : WordTrace (prefixWord ++ tailWord_1066755) baseStart_1066755 baseEnd_1066755 := by
    simpa [prefixWord, tailWord_1066755, baseEnd_1066755] using wordTrace_append hprefix tailTrace_1066755
  have hstable : (prefixWord ++ tailWord_1066755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066755).length < 2 ^ (prefixWord ++ tailWord_1066755).sum := by decide
  have hdescent : baseEnd_1066755 < baseStart_1066755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066759 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1066759 : Nat := 118140960795 + 1066759 * 2 ^ 59
def prefixEnd_1066759 : Nat := 4983230072969 + 3 ^ 40 * 1066759 * 2
def baseEnd_1066759 : Nat := 547760109509697034206571

theorem tailTrace_1066759 : CollatzResearch.WordTrace tailWord_1066759 prefixEnd_1066759 547760109509697034206571 := by
  unfold tailWord_1066759
  simp only [CollatzResearch.WordTrace]
  refine ⟨38907897142321805777587331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25938598094881203851724887 38907897142321805777587331)
  ·
    refine ⟨58361845713482708666380997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38907897142321805777587331 58361845713482708666380997)
    ·
      refine ⟨10942846071278007874946437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58361845713482708666380997 10942846071278007874946437)
      ·
        refine ⟨2051783638364626476552457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10942846071278007874946437 2051783638364626476552457)
        ·
          refine ⟨1538837728773469857414343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2051783638364626476552457 1538837728773469857414343)
          ·
            refine ⟨2308256593160204786121515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538837728773469857414343 2308256593160204786121515)
            ·
              refine ⟨3462384889740307179182273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308256593160204786121515 3462384889740307179182273)
              ·
                refine ⟨2596788667305230384386705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462384889740307179182273 2596788667305230384386705)
                ·
                  refine ⟨1947591500478922788290029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2596788667305230384386705 1947591500478922788290029)
                  ·
                    refine ⟨730346812679596045608761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947591500478922788290029 730346812679596045608761)
                    ·
                      refine ⟨547760109509697034206571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730346812679596045608761 547760109509697034206571)
                      ·
                        rfl

theorem cell23_1066759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1066759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066759 prefixEnd_1066759 := by exact prefixLift 1066759
  have htrace : WordTrace (prefixWord ++ tailWord_1066759) baseStart_1066759 baseEnd_1066759 := by
    simpa [prefixWord, tailWord_1066759, baseEnd_1066759] using wordTrace_append hprefix tailTrace_1066759
  have hstable : (prefixWord ++ tailWord_1066759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066759).length < 2 ^ (prefixWord ++ tailWord_1066759).sum := by decide
  have hdescent : baseEnd_1066759 < baseStart_1066759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066775 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1066775 : Nat := 118140960795 + 1066775 * 2 ^ 59
def prefixEnd_1066775 : Nat := 4983230072969 + 3 ^ 40 * 1066775 * 2
def baseEnd_1066775 : Nat := 547768325200168971606497

theorem tailTrace_1066775 : CollatzResearch.WordTrace tailWord_1066775 prefixEnd_1066775 547768325200168971606497 := by
  unfold tailWord_1066775
  simp only [CollatzResearch.WordTrace]
  refine ⟨38908480710263840510169779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25938987140175893673446519 38908480710263840510169779)
  ·
    refine ⟨58362721065395760765254669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38908480710263840510169779 58362721065395760765254669)
    ·
      refine ⟨21886020399523410286970501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58362721065395760765254669 21886020399523410286970501)
      ·
        refine ⟨4103628824910639428806969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21886020399523410286970501 4103628824910639428806969)
        ·
          refine ⟨3077721618682979571605227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4103628824910639428806969 3077721618682979571605227)
          ·
            refine ⟨4616582428024469357407841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077721618682979571605227 4616582428024469357407841)
            ·
              refine ⟨3462436821018352018055881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4616582428024469357407841 3462436821018352018055881)
              ·
                refine ⟨2596827615763764013541911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462436821018352018055881 2596827615763764013541911)
                ·
                  refine ⟨3895241423645646020312867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596827615763764013541911 3895241423645646020312867)
                  ·
                    refine ⟨5842862135468469030469301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895241423645646020312867 5842862135468469030469301)
                    ·
                      refine ⟨547768325200168971606497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5842862135468469030469301 547768325200168971606497)
                      ·
                        rfl

theorem cell23_1066775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1066775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066775 prefixEnd_1066775 := by exact prefixLift 1066775
  have htrace : WordTrace (prefixWord ++ tailWord_1066775) baseStart_1066775 baseEnd_1066775 := by
    simpa [prefixWord, tailWord_1066775, baseEnd_1066775] using wordTrace_append hprefix tailTrace_1066775
  have hstable : (prefixWord ++ tailWord_1066775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066775).length < 2 ^ (prefixWord ++ tailWord_1066775).sum := by decide
  have hdescent : baseEnd_1066775 < baseStart_1066775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066778 : List Nat := [3, 1, 1, 3, 2, 2, 1, 10]
def baseStart_1066778 : Nat := 118140960795 + 1066778 * 2 ^ 59
def prefixEnd_1066778 : Nat := 4983230072969 + 3 ^ 40 * 1066778 * 2
def baseEnd_1066778 : Nat := 20287772801560461476629

theorem tailTrace_1066778 : CollatzResearch.WordTrace tailWord_1066778 prefixEnd_1066778 20287772801560461476629 := by
  unfold tailWord_1066778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727147532313243005632247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25939060086168648015019325 9727147532313243005632247)
  ·
    refine ⟨14590721298469864508448371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9727147532313243005632247 14590721298469864508448371)
    ·
      refine ⟨21886081947704796762672557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14590721298469864508448371 21886081947704796762672557)
      ·
        refine ⟨8207280730389298786002209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21886081947704796762672557 8207280730389298786002209)
        ·
          refine ⟨6155460547791974089501657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8207280730389298786002209 6155460547791974089501657)
          ·
            refine ⟨4616595410843980567126243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6155460547791974089501657 4616595410843980567126243)
            ·
              refine ⟨6924893116265970850689365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4616595410843980567126243 6924893116265970850689365)
              ·
                refine ⟨20287772801560461476629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6924893116265970850689365 20287772801560461476629)
                ·
                  rfl

theorem cell23_1066778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_1066778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066778 prefixEnd_1066778 := by exact prefixLift 1066778
  have htrace : WordTrace (prefixWord ++ tailWord_1066778) baseStart_1066778 baseEnd_1066778 := by
    simpa [prefixWord, tailWord_1066778, baseEnd_1066778] using wordTrace_append hprefix tailTrace_1066778
  have hstable : (prefixWord ++ tailWord_1066778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066778).length < 2 ^ (prefixWord ++ tailWord_1066778).sum := by decide
  have hdescent : baseEnd_1066778 < baseStart_1066778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066792 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1066792 : Nat := 118140960795 + 1066792 * 2 ^ 59
def prefixEnd_1066792 : Nat := 4983230072969 + 3 ^ 40 * 1066792 * 2
def baseEnd_1066792 : Nat := 547777054371295405093919

theorem tailTrace_1066792 : CollatzResearch.WordTrace tailWord_1066792 prefixEnd_1066792 547777054371295405093919 := by
  unfold tailWord_1066792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19454550375601126206769315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25939400500801501609025753 19454550375601126206769315)
  ·
    refine ⟨29181825563401689310153973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19454550375601126206769315 29181825563401689310153973)
    ·
      refine ⟨2735796146568908372826935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29181825563401689310153973 2735796146568908372826935)
      ·
        refine ⟨4103694219853362559240403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735796146568908372826935 4103694219853362559240403)
        ·
          refine ⟨6155541329780043838860605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103694219853362559240403 6155541329780043838860605)
          ·
            refine ⟨2308327998667516439572727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6155541329780043838860605 2308327998667516439572727)
            ·
              refine ⟨3462491998001274659359091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308327998667516439572727 3462491998001274659359091)
              ·
                refine ⟨5193737997001911989038637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462491998001274659359091 5193737997001911989038637)
                ·
                  refine ⟨1947651748875716995889489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5193737997001911989038637 1947651748875716995889489)
                  ·
                    refine ⟨1460738811656787746917117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947651748875716995889489 1460738811656787746917117)
                    ·
                      refine ⟨547777054371295405093919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1460738811656787746917117 547777054371295405093919)
                      ·
                        rfl

theorem cell23_1066792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1066792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066792 prefixEnd_1066792 := by exact prefixLift 1066792
  have htrace : WordTrace (prefixWord ++ tailWord_1066792) baseStart_1066792 baseEnd_1066792 := by
    simpa [prefixWord, tailWord_1066792, baseEnd_1066792] using wordTrace_append hprefix tailTrace_1066792
  have hstable : (prefixWord ++ tailWord_1066792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066792).length < 2 ^ (prefixWord ++ tailWord_1066792).sum := by decide
  have hdescent : baseEnd_1066792 < baseStart_1066792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066806 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1066806 : Nat := 118140960795 + 1066806 * 2 ^ 59
def prefixEnd_1066806 : Nat := 4983230072969 + 3 ^ 40 * 1066806 * 2
def baseEnd_1066806 : Nat := 547784243100458350318855

theorem tailTrace_1066806 : CollatzResearch.WordTrace tailWord_1066806 prefixEnd_1066806 547784243100458350318855 := by
  unfold tailWord_1066806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431850710821970800284267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25939740915434355203032181 2431850710821970800284267)
  ·
    refine ⟨3647776066232956200426401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2431850710821970800284267 3647776066232956200426401)
    ·
      refine ⟨2735832049674717150319801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3647776066232956200426401 2735832049674717150319801)
      ·
        refine ⟨2051874037256037862739851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2735832049674717150319801 2051874037256037862739851)
        ·
          refine ⟨3077811055884056794109777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051874037256037862739851 3077811055884056794109777)
          ·
            refine ⟨2308358291913042595582333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3077811055884056794109777 2308358291913042595582333)
            ·
              refine ⟨865634359467390973343375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2308358291913042595582333 865634359467390973343375)
              ·
                refine ⟨1298451539201086460015063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865634359467390973343375 1298451539201086460015063)
                ·
                  refine ⟨1947677308801629690022595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298451539201086460015063 1947677308801629690022595)
                  ·
                    refine ⟨2921515963202444535033893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947677308801629690022595 2921515963202444535033893)
                    ·
                      refine ⟨547784243100458350318855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2921515963202444535033893 547784243100458350318855)
                      ·
                        rfl

theorem cell23_1066806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1066806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066806 prefixEnd_1066806 := by exact prefixLift 1066806
  have htrace : WordTrace (prefixWord ++ tailWord_1066806) baseStart_1066806 baseEnd_1066806 := by
    simpa [prefixWord, tailWord_1066806, baseEnd_1066806] using wordTrace_append hprefix tailTrace_1066806
  have hstable : (prefixWord ++ tailWord_1066806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066806).length < 2 ^ (prefixWord ++ tailWord_1066806).sum := by decide
  have hdescent : baseEnd_1066806 < baseStart_1066806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066809 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1066809 : Nat := 118140960795 + 1066809 * 2 ^ 59
def prefixEnd_1066809 : Nat := 4983230072969 + 3 ^ 40 * 1066809 * 2
def baseEnd_1066809 : Nat := 547785783542421838581341

theorem tailTrace_1066809 : CollatzResearch.WordTrace tailWord_1066809 prefixEnd_1066809 547785783542421838581341 := by
  unfold tailWord_1066809
  simp only [CollatzResearch.WordTrace]
  refine ⟨38909720792140664316907481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25939813861427109544604987 38909720792140664316907481)
  ·
    refine ⟨29182290594105498237680611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38909720792140664316907481 29182290594105498237680611)
    ·
      refine ⟨43773435891158247356520917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29182290594105498237680611 43773435891158247356520917)
      ·
        refine ⟨1025939903699021422418459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43773435891158247356520917 1025939903699021422418459)
        ·
          refine ⟨1538909855548532133627689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025939903699021422418459 1538909855548532133627689)
          ·
            refine ⟨1154182391661399100220767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1538909855548532133627689 1154182391661399100220767)
            ·
              refine ⟨1731273587492098650331151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154182391661399100220767 1731273587492098650331151)
              ·
                refine ⟨2596910381238147975496727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731273587492098650331151 2596910381238147975496727)
                ·
                  refine ⟨3895365571857221963245091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596910381238147975496727 3895365571857221963245091)
                  ·
                    refine ⟨5843048357785832944867637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3895365571857221963245091 5843048357785832944867637)
                    ·
                      refine ⟨547785783542421838581341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5843048357785832944867637 547785783542421838581341)
                      ·
                        rfl

theorem cell23_1066809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1066809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066809 prefixEnd_1066809 := by exact prefixLift 1066809
  have htrace : WordTrace (prefixWord ++ tailWord_1066809) baseStart_1066809 baseEnd_1066809 := by
    simpa [prefixWord, tailWord_1066809, baseEnd_1066809] using wordTrace_append hprefix tailTrace_1066809
  have hstable : (prefixWord ++ tailWord_1066809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066809).length < 2 ^ (prefixWord ++ tailWord_1066809).sum := by decide
  have hdescent : baseEnd_1066809 < baseStart_1066809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066885 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 7]
def baseStart_1066885 : Nat := 118140960795 + 1066885 * 2 ^ 59
def prefixEnd_1066885 : Nat := 4983230072969 + 3 ^ 40 * 1066885 * 2
def baseEnd_1066885 : Nat := 60869423119129282358999

theorem tailTrace_1066885 : CollatzResearch.WordTrace tailWord_1066885 prefixEnd_1066885 60869423119129282358999 := by
  unfold tailWord_1066885
  simp only [CollatzResearch.WordTrace]
  refine ⟨38912492739865329296674109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25941661826576886197782739 38912492739865329296674109)
  ·
    refine ⟨14592184777449498486252791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38912492739865329296674109 14592184777449498486252791)
    ·
      refine ⟨21888277166174247729379187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14592184777449498486252791 21888277166174247729379187)
      ·
        refine ⟨32832415749261371594068781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21888277166174247729379187 32832415749261371594068781)
        ·
          refine ⟨12312155905973014347775793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32832415749261371594068781 12312155905973014347775793)
          ·
            refine ⟨9234116929479760760831845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12312155905973014347775793 9234116929479760760831845)
            ·
              refine ⟨1731396924277455142655971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9234116929479760760831845 1731396924277455142655971)
              ·
                refine ⟨2597095386416182713983957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731396924277455142655971 2597095386416182713983957)
                ·
                  refine ⟨60869423119129282358999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2597095386416182713983957 60869423119129282358999)
                  ·
                    rfl

theorem cell23_1066885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_1066885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066885 prefixEnd_1066885 := by exact prefixLift 1066885
  have htrace : WordTrace (prefixWord ++ tailWord_1066885) baseStart_1066885 baseEnd_1066885 := by
    simpa [prefixWord, tailWord_1066885, baseEnd_1066885] using wordTrace_append hprefix tailTrace_1066885
  have hstable : (prefixWord ++ tailWord_1066885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066885).length < 2 ^ (prefixWord ++ tailWord_1066885).sum := by decide
  have hdescent : baseEnd_1066885 < baseStart_1066885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066915 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 2, 5]
def baseStart_1066915 : Nat := 118140960795 + 1066915 * 2 ^ 59
def prefixEnd_1066915 : Nat := 4983230072969 + 3 ^ 40 * 1066915 * 2
def baseEnd_1066915 : Nat := 182613404163932807951951

theorem tailTrace_1066915 : CollatzResearch.WordTrace tailWord_1066915 prefixEnd_1066915 182613404163932807951951 := by
  unfold tailWord_1066915
  simp only [CollatzResearch.WordTrace]
  refine ⟨38913586929756644420266199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25942391286504429613510799 38913586929756644420266199)
  ·
    refine ⟨58370380394634966630399299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38913586929756644420266199 58370380394634966630399299)
    ·
      refine ⟨87555570591952449945598949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58370380394634966630399299 87555570591952449945598949)
      ·
        refine ⟨16416669485991084364799803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87555570591952449945598949 16416669485991084364799803)
        ·
          refine ⟨24625004228986626547199705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16416669485991084364799803 24625004228986626547199705)
          ·
            refine ⟨18468753171739969910399779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24625004228986626547199705 18468753171739969910399779)
            ·
              refine ⟨27703129757609954865599669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18468753171739969910399779 27703129757609954865599669)
              ·
                refine ⟨2597168414775933268649969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27703129757609954865599669 2597168414775933268649969)
                ·
                  refine ⟨1947876311081949951487477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597168414775933268649969 1947876311081949951487477)
                  ·
                    refine ⟨182613404163932807951951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1947876311081949951487477 182613404163932807951951)
                    ·
                      rfl

theorem cell23_1066915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 5].length) (baseStart_1066915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066915 prefixEnd_1066915 := by exact prefixLift 1066915
  have htrace : WordTrace (prefixWord ++ tailWord_1066915) baseStart_1066915 baseEnd_1066915 := by
    simpa [prefixWord, tailWord_1066915, baseEnd_1066915] using wordTrace_append hprefix tailTrace_1066915
  have hstable : (prefixWord ++ tailWord_1066915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066915).length < 2 ^ (prefixWord ++ tailWord_1066915).sum := by decide
  have hdescent : baseEnd_1066915 < baseStart_1066915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066919 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 5]
def baseStart_1066919 : Nat := 118140960795 + 1066919 * 2 ^ 59
def prefixEnd_1066919 : Nat := 4983230072969 + 3 ^ 40 * 1066919 * 2
def baseEnd_1066919 : Nat := 60871362934935156467315

theorem tailTrace_1066919 : CollatzResearch.WordTrace tailWord_1066919 prefixEnd_1066919 60871362934935156467315 := by
  unfold tailWord_1066919
  simp only [CollatzResearch.WordTrace]
  refine ⟨38913732821742153103411811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25942488547828102068941207 38913732821742153103411811)
  ·
    refine ⟨58370599232613229655117717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38913732821742153103411811 58370599232613229655117717)
    ·
      refine ⟨2736121839028745140083643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58370599232613229655117717 2736121839028745140083643)
      ·
        refine ⟨4104182758543117710125465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736121839028745140083643 4104182758543117710125465)
        ·
          refine ⟨3078137068907338282594099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4104182758543117710125465 3078137068907338282594099)
          ·
            refine ⟨4617205603361007423891149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3078137068907338282594099 4617205603361007423891149)
            ·
              refine ⟨1731452101260377783959181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4617205603361007423891149 1731452101260377783959181)
              ·
                refine ⟨649294537972641668984693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1731452101260377783959181 649294537972641668984693)
                ·
                  refine ⟨60871362934935156467315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 649294537972641668984693 60871362934935156467315)
                  ·
                    rfl

theorem cell23_1066919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 5].length) (baseStart_1066919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066919 prefixEnd_1066919 := by exact prefixLift 1066919
  have htrace : WordTrace (prefixWord ++ tailWord_1066919) baseStart_1066919 baseEnd_1066919 := by
    simpa [prefixWord, tailWord_1066919, baseEnd_1066919] using wordTrace_append hprefix tailTrace_1066919
  have hstable : (prefixWord ++ tailWord_1066919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066919).length < 2 ^ (prefixWord ++ tailWord_1066919).sum := by decide
  have hdescent : baseEnd_1066919 < baseStart_1066919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066942 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1066942 : Nat := 118140960795 + 1066942 * 2 ^ 59
def prefixEnd_1066942 : Nat := 4983230072969 + 3 ^ 40 * 1066942 * 2
def baseEnd_1066942 : Nat := 547854076469469818218229

theorem tailTrace_1066942 : CollatzResearch.WordTrace tailWord_1066942 prefixEnd_1066942 547854076469469818218229 := by
  unfold tailWord_1066942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864321462582353503937385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25943047800439218687666053 4864321462582353503937385)
  ·
    refine ⟨3648241096936765127953039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4864321462582353503937385 3648241096936765127953039)
    ·
      refine ⟨5472361645405147691929559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3648241096936765127953039 5472361645405147691929559)
      ·
        refine ⟨8208542468107721537894339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472361645405147691929559 8208542468107721537894339)
        ·
          refine ⟨12312813702161582306841509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208542468107721537894339 12312813702161582306841509)
          ·
            refine ⟨2308652569155296682532783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12312813702161582306841509 2308652569155296682532783)
            ·
              refine ⟨3462978853732945023799175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308652569155296682532783 3462978853732945023799175)
              ·
                refine ⟨5194468280599417535698763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462978853732945023799175 5194468280599417535698763)
                ·
                  refine ⟨7791702420899126303548145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5194468280599417535698763 7791702420899126303548145)
                  ·
                    refine ⟨5843776815674344727661109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7791702420899126303548145 5843776815674344727661109)
                    ·
                      refine ⟨547854076469469818218229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5843776815674344727661109 547854076469469818218229)
                      ·
                        rfl

theorem cell23_1066942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1066942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066942 prefixEnd_1066942 := by exact prefixLift 1066942
  have htrace : WordTrace (prefixWord ++ tailWord_1066942) baseStart_1066942 baseEnd_1066942 := by
    simpa [prefixWord, tailWord_1066942, baseEnd_1066942] using wordTrace_append hprefix tailTrace_1066942
  have hstable : (prefixWord ++ tailWord_1066942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066942).length < 2 ^ (prefixWord ++ tailWord_1066942).sum := by decide
  have hdescent : baseEnd_1066942 < baseStart_1066942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066966 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1066966 : Nat := 118140960795 + 1066966 * 2 ^ 59
def prefixEnd_1066966 : Nat := 4983230072969 + 3 ^ 40 * 1066966 * 2
def baseEnd_1066966 : Nat := 182622133335059241439373

theorem tailTrace_1066966 : CollatzResearch.WordTrace tailWord_1066966 prefixEnd_1066966 182622133335059241439373 := by
  unfold tailWord_1066966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432215440785742508148297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25943631368381253420248501 2432215440785742508148297)
  ·
    refine ⟨1824161580589306881111223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2432215440785742508148297 1824161580589306881111223)
    ·
      refine ⟨2736242370883960321666835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824161580589306881111223 2736242370883960321666835)
      ·
        refine ⟨4104363556325940482500253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736242370883960321666835 4104363556325940482500253)
        ·
          refine ⟨1539136333622227680937595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4104363556325940482500253 1539136333622227680937595)
          ·
            refine ⟨2308704500433341521406393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539136333622227680937595 2308704500433341521406393)
            ·
              refine ⟨1731528375325006141054795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308704500433341521406393 1731528375325006141054795)
              ·
                refine ⟨2597292562987509211582193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731528375325006141054795 2597292562987509211582193)
                ·
                  refine ⟨1947969422240631908686645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597292562987509211582193 1947969422240631908686645)
                  ·
                    refine ⟨182622133335059241439373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1947969422240631908686645 182622133335059241439373)
                    ·
                      rfl

theorem cell23_1066966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1066966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066966 prefixEnd_1066966 := by exact prefixLift 1066966
  have htrace : WordTrace (prefixWord ++ tailWord_1066966) baseStart_1066966 baseEnd_1066966 := by
    simpa [prefixWord, tailWord_1066966, baseEnd_1066966] using wordTrace_append hprefix tailTrace_1066966
  have hstable : (prefixWord ++ tailWord_1066966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066966).length < 2 ^ (prefixWord ++ tailWord_1066966).sum := by decide
  have hdescent : baseEnd_1066966 < baseStart_1066966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1066969 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_1066969 : Nat := 118140960795 + 1066969 * 2 ^ 59
def prefixEnd_1066969 : Nat := 4983230072969 + 3 ^ 40 * 1066969 * 2
def baseEnd_1066969 : Nat := 547867940447141212580605

theorem tailTrace_1066969 : CollatzResearch.WordTrace tailWord_1066969 prefixEnd_1066969 547867940447141212580605 := by
  unfold tailWord_1066969
  simp only [CollatzResearch.WordTrace]
  refine ⟨38915556471561011642731961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25943704314374007761821307 38915556471561011642731961)
  ·
    refine ⟨29186667353670758732048971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38915556471561011642731961 29186667353670758732048971)
    ·
      refine ⟨43780001030506138098073457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29186667353670758732048971 43780001030506138098073457)
      ·
        refine ⟨32835000772879603573555093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43780001030506138098073457 32835000772879603573555093)
        ·
          refine ⟨1539140661228731417510395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32835000772879603573555093 1539140661228731417510395)
          ·
            refine ⟨2308710991843097126265593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539140661228731417510395 2308710991843097126265593)
            ·
              refine ⟨1731533243882322844699195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308710991843097126265593 1731533243882322844699195)
              ·
                refine ⟨2597299865823484267048793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731533243882322844699195 2597299865823484267048793)
                ·
                  refine ⟨1947974899367613200286595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597299865823484267048793 1947974899367613200286595)
                  ·
                    refine ⟨2921962349051419800429893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1947974899367613200286595 2921962349051419800429893)
                    ·
                      refine ⟨547867940447141212580605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2921962349051419800429893 547867940447141212580605)
                      ·
                        rfl

theorem cell23_1066969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_1066969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1066969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1066969 prefixEnd_1066969 := by exact prefixLift 1066969
  have htrace : WordTrace (prefixWord ++ tailWord_1066969) baseStart_1066969 baseEnd_1066969 := by
    simpa [prefixWord, tailWord_1066969, baseEnd_1066969] using wordTrace_append hprefix tailTrace_1066969
  have hstable : (prefixWord ++ tailWord_1066969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1066969).length < 2 ^ (prefixWord ++ tailWord_1066969).sum := by decide
  have hdescent : baseEnd_1066969 < baseStart_1066969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1066969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067019 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 3]
def baseStart_1067019 : Nat := 118140960795 + 1067019 * 2 ^ 59
def prefixEnd_1067019 : Nat := 4983230072969 + 3 ^ 40 * 1067019 * 2
def baseEnd_1067019 : Nat := 547893614479866016955375

theorem tailTrace_1067019 : CollatzResearch.WordTrace tailWord_1067019 prefixEnd_1067019 547893614479866016955375 := by
  unfold tailWord_1067019
  simp only [CollatzResearch.WordTrace]
  refine ⟨38917380121379870182052111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25944920080919913454701407 38917380121379870182052111)
  ·
    refine ⟨58376070182069805273078167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38917380121379870182052111 58376070182069805273078167)
    ·
      refine ⟨87564105273104707909617251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58376070182069805273078167 87564105273104707909617251)
      ·
        refine ⟨131346157909657061864425877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87564105273104707909617251 131346157909657061864425877)
        ·
          refine ⟨6156851152015174774894963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131346157909657061864425877 6156851152015174774894963)
          ·
            refine ⟨9235276728022762162342445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6156851152015174774894963 9235276728022762162342445)
            ·
              refine ⟨3463228773008535810878417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9235276728022762162342445 3463228773008535810878417)
              ·
                refine ⟨2597421579756401858158813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3463228773008535810878417 2597421579756401858158813)
                ·
                  refine ⟨974033092408650696809555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2597421579756401858158813 974033092408650696809555)
                  ·
                    refine ⟨1461049638612976045214333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974033092408650696809555 1461049638612976045214333)
                    ·
                      refine ⟨547893614479866016955375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1461049638612976045214333 547893614479866016955375)
                      ·
                        rfl

theorem cell23_1067019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 3].length) (baseStart_1067019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067019 prefixEnd_1067019 := by exact prefixLift 1067019
  have htrace : WordTrace (prefixWord ++ tailWord_1067019) baseStart_1067019 baseEnd_1067019 := by
    simpa [prefixWord, tailWord_1067019, baseEnd_1067019] using wordTrace_append hprefix tailTrace_1067019
  have hstable : (prefixWord ++ tailWord_1067019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067019).length < 2 ^ (prefixWord ++ tailWord_1067019).sum := by decide
  have hdescent : baseEnd_1067019 < baseStart_1067019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067022 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_1067022 : Nat := 118140960795 + 1067022 * 2 ^ 59
def prefixEnd_1067022 : Nat := 4983230072969 + 3 ^ 40 * 1067022 * 2
def baseEnd_1067022 : Nat := 182631718307276501739287

theorem tailTrace_1067022 : CollatzResearch.WordTrace tailWord_1067022 prefixEnd_1067022 182631718307276501739287 := by
  unfold tailWord_1067022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864686192546125211801415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25944993026912667796274213 4864686192546125211801415)
  ·
    refine ⟨7297029288819187817702123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4864686192546125211801415 7297029288819187817702123)
    ·
      refine ⟨10945543933228781726553185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7297029288819187817702123 10945543933228781726553185)
      ·
        refine ⟨8209157949921586294914889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10945543933228781726553185 8209157949921586294914889)
        ·
          refine ⟨6156868462441189721186167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8209157949921586294914889 6156868462441189721186167)
          ·
            refine ⟨9235302693661784581779251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6156868462441189721186167 9235302693661784581779251)
            ·
              refine ⟨13852954040492676872668877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9235302693661784581779251 13852954040492676872668877)
              ·
                refine ⟨5194857765184753827250829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13852954040492676872668877 5194857765184753827250829)
                ·
                  refine ⟨1948071661944282685219061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5194857765184753827250829 1948071661944282685219061)
                  ·
                    refine ⟨182631718307276501739287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1948071661944282685219061 182631718307276501739287)
                    ·
                      rfl

theorem cell23_1067022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_1067022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067022 prefixEnd_1067022 := by exact prefixLift 1067022
  have htrace : WordTrace (prefixWord ++ tailWord_1067022) baseStart_1067022 baseEnd_1067022 := by
    simpa [prefixWord, tailWord_1067022, baseEnd_1067022] using wordTrace_append hprefix tailTrace_1067022
  have hstable : (prefixWord ++ tailWord_1067022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067022).length < 2 ^ (prefixWord ++ tailWord_1067022).sum := by decide
  have hdescent : baseEnd_1067022 < baseStart_1067022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067035 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 3, 6]
def baseStart_1067035 : Nat := 118140960795 + 1067035 * 2 ^ 59
def prefixEnd_1067035 : Nat := 4983230072969 + 3 ^ 40 * 1067035 * 2
def baseEnd_1067035 : Nat := 182633943390112651451767

theorem tailTrace_1067035 : CollatzResearch.WordTrace tailWord_1067035 prefixEnd_1067035 182633943390112651451767 := by
  unfold tailWord_1067035
  simp only [CollatzResearch.WordTrace]
  refine ⟨38917963689321904914634559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25945309126214603276423039 38917963689321904914634559)
  ·
    refine ⟨58376945533982857371951839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38917963689321904914634559 58376945533982857371951839)
    ·
      refine ⟨87565418300974286057927759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58376945533982857371951839 87565418300974286057927759)
      ·
        refine ⟨131348127451461429086891639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87565418300974286057927759 131348127451461429086891639)
        ·
          refine ⟨197022191177192143630337459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131348127451461429086891639 197022191177192143630337459)
          ·
            refine ⟨295533286765788215445506189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197022191177192143630337459 295533286765788215445506189)
            ·
              refine ⟨110824982537170580792064821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295533286765788215445506189 110824982537170580792064821)
              ·
                refine ⟨10389842112859741949256077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110824982537170580792064821 10389842112859741949256077)
                ·
                  refine ⟨3896190792322403230971029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10389842112859741949256077 3896190792322403230971029)
                  ·
                    refine ⟨182633943390112651451767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3896190792322403230971029 182633943390112651451767)
                    ·
                      rfl

theorem cell23_1067035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_1067035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067035 prefixEnd_1067035 := by exact prefixLift 1067035
  have htrace : WordTrace (prefixWord ++ tailWord_1067035) baseStart_1067035 baseEnd_1067035 := by
    simpa [prefixWord, tailWord_1067035, baseEnd_1067035] using wordTrace_append hprefix tailTrace_1067035
  have hstable : (prefixWord ++ tailWord_1067035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067035).length < 2 ^ (prefixWord ++ tailWord_1067035).sum := by decide
  have hdescent : baseEnd_1067035 < baseStart_1067035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067072 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_1067072 : Nat := 118140960795 + 1067072 * 2 ^ 59
def prefixEnd_1067072 : Nat := 4983230072969 + 3 ^ 40 * 1067072 * 2
def baseEnd_1067072 : Nat := 547920828954554309592631

theorem tailTrace_1067072 : CollatzResearch.WordTrace tailWord_1067072 prefixEnd_1067072 547920828954554309592631 := by
  unfold tailWord_1067072
  simp only [CollatzResearch.WordTrace]
  refine ⟨19459656595093930116865735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25946208793458573489154313 19459656595093930116865735)
  ·
    refine ⟨29189484892640895175298603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19459656595093930116865735 29189484892640895175298603)
    ·
      refine ⟨43784227338961342762947905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29189484892640895175298603 43784227338961342762947905)
      ·
        refine ⟨32838170504221007072210929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43784227338961342762947905 32838170504221007072210929)
        ·
          refine ⟨24628627878165755304158197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32838170504221007072210929 24628627878165755304158197)
          ·
            refine ⟨2308933863578039559764831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24628627878165755304158197 2308933863578039559764831)
            ·
              refine ⟨3463400795367059339647247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308933863578039559764831 3463400795367059339647247)
              ·
                refine ⟨5195101193050589009470871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463400795367059339647247 5195101193050589009470871)
                ·
                  refine ⟨7792651789575883514206307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5195101193050589009470871 7792651789575883514206307)
                  ·
                    refine ⟨11688977684363825271309461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7792651789575883514206307 11688977684363825271309461)
                    ·
                      refine ⟨547920828954554309592631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11688977684363825271309461 547920828954554309592631)
                      ·
                        rfl

theorem cell23_1067072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_1067072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067072 prefixEnd_1067072 := by exact prefixLift 1067072
  have htrace : WordTrace (prefixWord ++ tailWord_1067072) baseStart_1067072 baseEnd_1067072 := by
    simpa [prefixWord, tailWord_1067072, baseEnd_1067072] using wordTrace_append hprefix tailTrace_1067072
  have hstable : (prefixWord ++ tailWord_1067072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067072).length < 2 ^ (prefixWord ++ tailWord_1067072).sum := by decide
  have hdescent : baseEnd_1067072 < baseStart_1067072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067152 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_1067152 : Nat := 118140960795 + 1067152 * 2 ^ 59
def prefixEnd_1067152 : Nat := 4983230072969 + 3 ^ 40 * 1067152 * 2
def baseEnd_1067152 : Nat := 547961907406913996592263

theorem tailTrace_1067152 : CollatzResearch.WordTrace tailWord_1067152 prefixEnd_1067152 547961907406913996592263 := by
  unfold tailWord_1067152
  simp only [CollatzResearch.WordTrace]
  refine ⟨19461115514949016948321855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25948154019932022597762473 19461115514949016948321855)
  ·
    refine ⟨29191673272423525422482783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19461115514949016948321855 29191673272423525422482783)
    ·
      refine ⟨43787509908635288133724175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29191673272423525422482783 43787509908635288133724175)
      ·
        refine ⟨65681264862952932200586263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43787509908635288133724175 65681264862952932200586263)
        ·
          refine ⟨98521897294429398300879395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65681264862952932200586263 98521897294429398300879395)
          ·
            refine ⟨147782845941644097451319093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98521897294429398300879395 147782845941644097451319093)
            ·
              refine ⟨13854641807029134136061165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147782845941644097451319093 13854641807029134136061165)
              ·
                refine ⟨5195490677635925301022937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13854641807029134136061165 5195490677635925301022937)
                ·
                  refine ⟨3896618008226943975767203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5195490677635925301022937 3896618008226943975767203)
                  ·
                    refine ⟨5844927012340415963650805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3896618008226943975767203 5844927012340415963650805)
                    ·
                      refine ⟨547961907406913996592263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5844927012340415963650805 547961907406913996592263)
                      ·
                        rfl

theorem cell23_1067152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_1067152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067152 prefixEnd_1067152 := by exact prefixLift 1067152
  have htrace : WordTrace (prefixWord ++ tailWord_1067152) baseStart_1067152 baseEnd_1067152 := by
    simpa [prefixWord, tailWord_1067152, baseEnd_1067152] using wordTrace_append hprefix tailTrace_1067152
  have hstable : (prefixWord ++ tailWord_1067152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067152).length < 2 ^ (prefixWord ++ tailWord_1067152).sum := by decide
  have hdescent : baseEnd_1067152 < baseStart_1067152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067169 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1067169 : Nat := 118140960795 + 1067169 * 2 ^ 59
def prefixEnd_1067169 : Nat := 4983230072969 + 3 ^ 40 * 1067169 * 2
def baseEnd_1067169 : Nat := 547970636578040430079685

theorem tailTrace_1067169 : CollatzResearch.WordTrace tailWord_1067169 prefixEnd_1067169 547970636578040430079685 := by
  unfold tailWord_1067169
  simp only [CollatzResearch.WordTrace]
  refine ⟨38922851070836445800012561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25948567380557630533341707 38922851070836445800012561)
  ·
    refine ⟨29192138303127334350009421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38922851070836445800012561 29192138303127334350009421)
    ·
      refine ⟨10947051863672750381253533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29192138303127334350009421 10947051863672750381253533)
      ·
        refine ⟨4105144448877281392970075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10947051863672750381253533 4105144448877281392970075)
        ·
          refine ⟨6157716673315922089455113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105144448877281392970075 6157716673315922089455113)
          ·
            refine ⟨4618287504986941567091335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6157716673315922089455113 4618287504986941567091335)
            ·
              refine ⟨6927431257480412350637003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618287504986941567091335 6927431257480412350637003)
              ·
                refine ⟨10391146886220618525955505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6927431257480412350637003 10391146886220618525955505)
                ·
                  refine ⟨7793360164665463894466629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10391146886220618525955505 7793360164665463894466629)
                  ·
                    refine ⟨1461255030874774480212493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7793360164665463894466629 1461255030874774480212493)
                    ·
                      refine ⟨547970636578040430079685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1461255030874774480212493 547970636578040430079685)
                      ·
                        rfl

theorem cell23_1067169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1067169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067169 prefixEnd_1067169 := by exact prefixLift 1067169
  have htrace : WordTrace (prefixWord ++ tailWord_1067169) baseStart_1067169 baseEnd_1067169 := by
    simpa [prefixWord, tailWord_1067169, baseEnd_1067169] using wordTrace_append hprefix tailTrace_1067169
  have hstable : (prefixWord ++ tailWord_1067169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067169).length < 2 ^ (prefixWord ++ tailWord_1067169).sum := by decide
  have hdescent : baseEnd_1067169 < baseStart_1067169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067209 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 7, 2]
def baseStart_1067209 : Nat := 118140960795 + 1067209 * 2 ^ 59
def prefixEnd_1067209 : Nat := 4983230072969 + 3 ^ 40 * 1067209 * 2
def baseEnd_1067209 : Nat := 547991175804220273579501

theorem tailTrace_1067209 : CollatzResearch.WordTrace tailWord_1067209 prefixEnd_1067209 547991175804220273579501 := by
  unfold tailWord_1067209
  simp only [CollatzResearch.WordTrace]
  refine ⟨38924309990691532631468681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25949539993794355087645787 38924309990691532631468681)
  ·
    refine ⟨29193232493018649473601511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38924309990691532631468681 29193232493018649473601511)
    ·
      refine ⟨43789848739527974210402267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29193232493018649473601511 43789848739527974210402267)
      ·
        refine ⟨65684773109291961315603401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43789848739527974210402267 65684773109291961315603401)
        ·
          refine ⟨49263579831968970986702551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65684773109291961315603401 49263579831968970986702551)
          ·
            refine ⟨73895369747953456480053827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49263579831968970986702551 73895369747953456480053827)
            ·
              refine ⟨110843054621930184720080741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73895369747953456480053827 110843054621930184720080741)
              ·
                refine ⟨20783072741611909635015139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110843054621930184720080741 20783072741611909635015139)
                ·
                  refine ⟨31174609112417864452522709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20783072741611909635015139 31174609112417864452522709)
                  ·
                    refine ⟨730654901072293698106001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31174609112417864452522709 730654901072293698106001)
                    ·
                      refine ⟨547991175804220273579501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730654901072293698106001 547991175804220273579501)
                      ·
                        rfl

theorem cell23_1067209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 7, 2].length) (baseStart_1067209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067209 prefixEnd_1067209 := by exact prefixLift 1067209
  have htrace : WordTrace (prefixWord ++ tailWord_1067209) baseStart_1067209 baseEnd_1067209 := by
    simpa [prefixWord, tailWord_1067209, baseEnd_1067209] using wordTrace_append hprefix tailTrace_1067209
  have hstable : (prefixWord ++ tailWord_1067209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067209).length < 2 ^ (prefixWord ++ tailWord_1067209).sum := by decide
  have hdescent : baseEnd_1067209 < baseStart_1067209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067234 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1067234 : Nat := 118140960795 + 1067234 * 2 ^ 59
def prefixEnd_1067234 : Nat := 4983230072969 + 3 ^ 40 * 1067234 * 2
def baseEnd_1067234 : Nat := 548004012820582675766887

theorem tailTrace_1067234 : CollatzResearch.WordTrace tailWord_1067234 prefixEnd_1067234 548004012820582675766887 := by
  unfold tailWord_1067234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731305453900240475282189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25950147877067307934085837 9731305453900240475282189)
  ·
    refine ⟨3649239545212590178230821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9731305453900240475282189 3649239545212590178230821)
    ·
      refine ⟨684232414727360658418279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3649239545212590178230821 684232414727360658418279)
      ·
        refine ⟨1026348622091040987627419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684232414727360658418279 1026348622091040987627419)
        ·
          refine ⟨1539522933136561481441129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026348622091040987627419 1539522933136561481441129)
          ·
            refine ⟨1154642199852421111080847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539522933136561481441129 1154642199852421111080847)
            ·
              refine ⟨1731963299778631666621271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154642199852421111080847 1731963299778631666621271)
              ·
                refine ⟨2597944949667947499931907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731963299778631666621271 2597944949667947499931907)
                ·
                  refine ⟨3896917424501921249897861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597944949667947499931907 3896917424501921249897861)
                  ·
                    refine ⟨730672017094110234355849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3896917424501921249897861 730672017094110234355849)
                    ·
                      refine ⟨548004012820582675766887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730672017094110234355849 548004012820582675766887)
                      ·
                        rfl

theorem cell23_1067234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1067234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067234 prefixEnd_1067234 := by exact prefixLift 1067234
  have htrace : WordTrace (prefixWord ++ tailWord_1067234) baseStart_1067234 baseEnd_1067234 := by
    simpa [prefixWord, tailWord_1067234, baseEnd_1067234] using wordTrace_append hprefix tailTrace_1067234
  have hstable : (prefixWord ++ tailWord_1067234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067234).length < 2 ^ (prefixWord ++ tailWord_1067234).sum := by decide
  have hdescent : baseEnd_1067234 < baseStart_1067234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067259 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 3]
def baseStart_1067259 : Nat := 118140960795 + 1067259 * 2 ^ 59
def prefixEnd_1067259 : Nat := 4983230072969 + 3 ^ 40 * 1067259 * 2
def baseEnd_1067259 : Nat := 548016849836945077954271

theorem tailTrace_1067259 : CollatzResearch.WordTrace tailWord_1067259 prefixEnd_1067259 548016849836945077954271 := by
  unfold tailWord_1067259
  simp only [CollatzResearch.WordTrace]
  refine ⟨38926133640510391170788831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25950755760340260780525887 38926133640510391170788831)
  ·
    refine ⟨58389200460765586756183247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38926133640510391170788831 58389200460765586756183247)
    ·
      refine ⟨87583800691148380134274871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58389200460765586756183247 87583800691148380134274871)
      ·
        refine ⟨131375701036722570201412307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87583800691148380134274871 131375701036722570201412307)
        ·
          refine ⟨197063551555083855302118461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131375701036722570201412307 197063551555083855302118461)
          ·
            refine ⟨73898831833156445738294423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197063551555083855302118461 73898831833156445738294423)
            ·
              refine ⟨110848247749734668607441635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73898831833156445738294423 110848247749734668607441635)
              ·
                refine ⟨166272371624602002911162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110848247749734668607441635 166272371624602002911162453)
                ·
                  refine ⟨1948504354975804721615185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 166272371624602002911162453 1948504354975804721615185)
                  ·
                    refine ⟨1461378266231853541211389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1948504354975804721615185 1461378266231853541211389)
                    ·
                      refine ⟨548016849836945077954271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1461378266231853541211389 548016849836945077954271)
                      ·
                        rfl

theorem cell23_1067259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 3].length) (baseStart_1067259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067259 prefixEnd_1067259 := by exact prefixLift 1067259
  have htrace : WordTrace (prefixWord ++ tailWord_1067259) baseStart_1067259 baseEnd_1067259 := by
    simpa [prefixWord, tailWord_1067259, baseEnd_1067259] using wordTrace_append hprefix tailTrace_1067259
  have hstable : (prefixWord ++ tailWord_1067259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067259).length < 2 ^ (prefixWord ++ tailWord_1067259).sum := by decide
  have hdescent : baseEnd_1067259 < baseStart_1067259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067276 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_1067276 : Nat := 118140960795 + 1067276 * 2 ^ 59
def prefixEnd_1067276 : Nat := 4983230072969 + 3 ^ 40 * 1067276 * 2
def baseEnd_1067276 : Nat := 548025579008071511441693

theorem tailTrace_1067276 : CollatzResearch.WordTrace tailWord_1067276 prefixEnd_1067276 548025579008071511441693 := by
  unfold tailWord_1067276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19463376840724401537078841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25951169120965868716105121 19463376840724401537078841)
  ·
    refine ⟨14597532630543301152809131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19463376840724401537078841 14597532630543301152809131)
    ·
      refine ⟨21896298945814951729213697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14597532630543301152809131 21896298945814951729213697)
      ·
        refine ⟨16422224209361213796910273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21896298945814951729213697 16422224209361213796910273)
        ·
          refine ⟨12316668157020910347682705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16422224209361213796910273 12316668157020910347682705)
          ·
            refine ⟨9237501117765682760762029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12316668157020910347682705 9237501117765682760762029)
            ·
              refine ⟨3464062919162131035285761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9237501117765682760762029 3464062919162131035285761)
              ·
                refine ⟨2598047189371598276464321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464062919162131035285761 2598047189371598276464321)
                ·
                  refine ⟨1948535392028698707348241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598047189371598276464321 1948535392028698707348241)
                  ·
                    refine ⟨1461401544021524030511181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1948535392028698707348241 1461401544021524030511181)
                    ·
                      refine ⟨548025579008071511441693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1461401544021524030511181 548025579008071511441693)
                      ·
                        rfl

theorem cell23_1067276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_1067276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067276 prefixEnd_1067276 := by exact prefixLift 1067276
  have htrace : WordTrace (prefixWord ++ tailWord_1067276) baseStart_1067276 baseEnd_1067276 := by
    simpa [prefixWord, tailWord_1067276, baseEnd_1067276] using wordTrace_append hprefix tailTrace_1067276
  have hstable : (prefixWord ++ tailWord_1067276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067276).length < 2 ^ (prefixWord ++ tailWord_1067276).sum := by decide
  have hdescent : baseEnd_1067276 < baseStart_1067276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067296 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 6]
def baseStart_1067296 : Nat := 118140960795 + 1067296 * 2 ^ 59
def prefixEnd_1067296 : Nat := 4983230072969 + 3 ^ 40 * 1067296 * 2
def baseEnd_1067296 : Nat := 60892872069017937021289

theorem tailTrace_1067296 : CollatzResearch.WordTrace tailWord_1067296 prefixEnd_1067296 60892872069017937021289 := by
  unfold tailWord_1067296
  simp only [CollatzResearch.WordTrace]
  refine ⟨19463741570688173244942871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25951655427584230993257161 19463741570688173244942871)
  ·
    refine ⟨29195612356032259867414307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19463741570688173244942871 29195612356032259867414307)
    ·
      refine ⟨43793418534048389801121461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29195612356032259867414307 43793418534048389801121461)
      ·
        refine ⟨4105632987567036543855137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43793418534048389801121461 4105632987567036543855137)
        ·
          refine ⟨3079224740675277407891353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4105632987567036543855137 3079224740675277407891353)
          ·
            refine ⟨2309418555506458055918515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079224740675277407891353 2309418555506458055918515)
            ·
              refine ⟨3464127833259687083877773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309418555506458055918515 3464127833259687083877773)
              ·
                refine ⟨1299047937472382656454165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3464127833259687083877773 1299047937472382656454165)
                ·
                  refine ⟨60892872069017937021289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1299047937472382656454165 60892872069017937021289)
                  ·
                    rfl

theorem cell23_1067296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_1067296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067296 prefixEnd_1067296 := by exact prefixLift 1067296
  have htrace : WordTrace (prefixWord ++ tailWord_1067296) baseStart_1067296 baseEnd_1067296 := by
    simpa [prefixWord, tailWord_1067296, baseEnd_1067296] using wordTrace_append hprefix tailTrace_1067296
  have hstable : (prefixWord ++ tailWord_1067296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067296).length < 2 ^ (prefixWord ++ tailWord_1067296).sum := by decide
  have hdescent : baseEnd_1067296 < baseStart_1067296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067340 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1067340 : Nat := 118140960795 + 1067340 * 2 ^ 59
def prefixEnd_1067340 : Nat := 4983230072969 + 3 ^ 40 * 1067340 * 2
def baseEnd_1067340 : Nat := 548058441769959261041399

theorem tailTrace_1067340 : CollatzResearch.WordTrace tailWord_1067340 prefixEnd_1067340 548058441769959261041399 := by
  unfold tailWord_1067340
  simp only [CollatzResearch.WordTrace]
  refine ⟨19464543976608471002243737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25952725302144628002991649 19464543976608471002243737)
  ·
    refine ⟨14598407982456353251682803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19464543976608471002243737 14598407982456353251682803)
    ·
      refine ⟨21897611973684529877524205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14598407982456353251682803 21897611973684529877524205)
      ·
        refine ⟨8211604490131698704071577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21897611973684529877524205 8211604490131698704071577)
        ·
          refine ⟨6158703367598774028053683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8211604490131698704071577 6158703367598774028053683)
          ·
            refine ⟨9238055051398161042080525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158703367598774028053683 9238055051398161042080525)
            ·
              refine ⟨3464270644274310390780197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9238055051398161042080525 3464270644274310390780197)
              ·
                refine ⟨649550745801433198271287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3464270644274310390780197 649550745801433198271287)
                ·
                  refine ⟨974326118702149797406931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649550745801433198271287 974326118702149797406931)
                  ·
                    refine ⟨1461489178053224696110397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974326118702149797406931 1461489178053224696110397)
                    ·
                      refine ⟨548058441769959261041399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1461489178053224696110397 548058441769959261041399)
                      ·
                        rfl

theorem cell23_1067340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1067340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067340 prefixEnd_1067340 := by exact prefixLift 1067340
  have htrace : WordTrace (prefixWord ++ tailWord_1067340) baseStart_1067340 baseEnd_1067340 := by
    simpa [prefixWord, tailWord_1067340, baseEnd_1067340] using wordTrace_append hprefix tailTrace_1067340
  have hstable : (prefixWord ++ tailWord_1067340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067340).length < 2 ^ (prefixWord ++ tailWord_1067340).sum := by decide
  have hdescent : baseEnd_1067340 < baseStart_1067340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067346 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1067346 : Nat := 118140960795 + 1067346 * 2 ^ 59
def prefixEnd_1067346 : Nat := 4983230072969 + 3 ^ 40 * 1067346 * 2
def baseEnd_1067346 : Nat := 548061522653886237566371

theorem tailTrace_1067346 : CollatzResearch.WordTrace tailWord_1067346 prefixEnd_1067346 548061522653886237566371 := by
  unfold tailWord_1067346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732326697798801257301473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25952871194130136686137261 9732326697798801257301473)
  ·
    refine ⟨7299245023349100942976105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9732326697798801257301473 7299245023349100942976105)
    ·
      refine ⟨5474433767511825707232079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7299245023349100942976105 5474433767511825707232079)
      ·
        refine ⟨8211650651267738560848119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474433767511825707232079 8211650651267738560848119)
        ·
          refine ⟨12317475976901607841272179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8211650651267738560848119 12317475976901607841272179)
          ·
            refine ⟨18476213965352411761908269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12317475976901607841272179 18476213965352411761908269)
            ·
              refine ⟨6928580237007154410715601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18476213965352411761908269 6928580237007154410715601)
              ·
                refine ⟨5196435177755365808036701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928580237007154410715601 5196435177755365808036701)
                ·
                  refine ⟨1948663191658262178013763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5196435177755365808036701 1948663191658262178013763)
                  ·
                    refine ⟨2922994787487393267020645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1948663191658262178013763 2922994787487393267020645)
                    ·
                      refine ⟨548061522653886237566371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2922994787487393267020645 548061522653886237566371)
                      ·
                        rfl

theorem cell23_1067346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1067346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067346 prefixEnd_1067346 := by exact prefixLift 1067346
  have htrace : WordTrace (prefixWord ++ tailWord_1067346) baseStart_1067346 baseEnd_1067346 := by
    simpa [prefixWord, tailWord_1067346, baseEnd_1067346] using wordTrace_append hprefix tailTrace_1067346
  have hstable : (prefixWord ++ tailWord_1067346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067346).length < 2 ^ (prefixWord ++ tailWord_1067346).sum := by decide
  have hdescent : baseEnd_1067346 < baseStart_1067346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067359 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1067359 : Nat := 118140960795 + 1067359 * 2 ^ 59
def prefixEnd_1067359 : Nat := 4983230072969 + 3 ^ 40 * 1067359 * 2
def baseEnd_1067359 : Nat := 548068197902394686703811

theorem tailTrace_1067359 : CollatzResearch.WordTrace tailWord_1067359 prefixEnd_1067359 548068197902394686703811 := by
  unfold tailWord_1067359
  simp only [CollatzResearch.WordTrace]
  refine ⟨38929780940148108249429131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25953187293432072166286087 38929780940148108249429131)
  ·
    refine ⟨58394671410222162374143697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38929780940148108249429131 58394671410222162374143697)
    ·
      refine ⟨43796003557666621780607773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58394671410222162374143697 43796003557666621780607773)
      ·
        refine ⟨16423501334124983167727915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43796003557666621780607773 16423501334124983167727915)
        ·
          refine ⟨24635252001187474751591873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16423501334124983167727915 24635252001187474751591873)
          ·
            refine ⟨18476439000890606063693905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24635252001187474751591873 18476439000890606063693905)
            ·
              refine ⟨13857329250667954547770429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18476439000890606063693905 13857329250667954547770429)
              ·
                refine ⟨5196498469000482955413911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13857329250667954547770429 5196498469000482955413911)
                ·
                  refine ⟨7794747703500724433120867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196498469000482955413911 7794747703500724433120867)
                  ·
                    refine ⟨11692121555251086649681301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7794747703500724433120867 11692121555251086649681301)
                    ·
                      refine ⟨548068197902394686703811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11692121555251086649681301 548068197902394686703811)
                      ·
                        rfl

theorem cell23_1067359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1067359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067359 prefixEnd_1067359 := by exact prefixLift 1067359
  have htrace : WordTrace (prefixWord ++ tailWord_1067359) baseStart_1067359 baseEnd_1067359 := by
    simpa [prefixWord, tailWord_1067359, baseEnd_1067359] using wordTrace_append hprefix tailTrace_1067359
  have hstable : (prefixWord ++ tailWord_1067359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067359).length < 2 ^ (prefixWord ++ tailWord_1067359).sum := by decide
  have hdescent : baseEnd_1067359 < baseStart_1067359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067376 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_1067376 : Nat := 118140960795 + 1067376 * 2 ^ 59
def prefixEnd_1067376 : Nat := 4983230072969 + 3 ^ 40 * 1067376 * 2
def baseEnd_1067376 : Nat := 548076927073521120191233

theorem tailTrace_1067376 : CollatzResearch.WordTrace tailWord_1067376 prefixEnd_1067376 548076927073521120191233 := by
  unfold tailWord_1067376
  simp only [CollatzResearch.WordTrace]
  refine ⟨19465200490543260076398991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25953600654057680101865321 19465200490543260076398991)
  ·
    refine ⟨29197800735814890114598487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19465200490543260076398991 29197800735814890114598487)
    ·
      refine ⟨43796701103722335171897731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29197800735814890114598487 43796701103722335171897731)
      ·
        refine ⟨65695051655583502757846597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43796701103722335171897731 65695051655583502757846597)
        ·
          refine ⟨12317822185421906767096237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65695051655583502757846597 12317822185421906767096237)
          ·
            refine ⟨4619183319533215037661089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12317822185421906767096237 4619183319533215037661089)
            ·
              refine ⟨3464387489649911278245817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4619183319533215037661089 3464387489649911278245817)
              ·
                refine ⟨2598290617237433458684363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464387489649911278245817 2598290617237433458684363)
                ·
                  refine ⟨3897435925856150188026545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598290617237433458684363 3897435925856150188026545)
                  ·
                    refine ⟨2923076944392112641019909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3897435925856150188026545 2923076944392112641019909)
                    ·
                      refine ⟨548076927073521120191233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2923076944392112641019909 548076927073521120191233)
                      ·
                        rfl

theorem cell23_1067376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_1067376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067376 prefixEnd_1067376 := by exact prefixLift 1067376
  have htrace : WordTrace (prefixWord ++ tailWord_1067376) baseStart_1067376 baseEnd_1067376 := by
    simpa [prefixWord, tailWord_1067376, baseEnd_1067376] using wordTrace_append hprefix tailTrace_1067376
  have hstable : (prefixWord ++ tailWord_1067376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067376).length < 2 ^ (prefixWord ++ tailWord_1067376).sum := by decide
  have hdescent : baseEnd_1067376 < baseStart_1067376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067409 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_1067409 : Nat := 118140960795 + 1067409 * 2 ^ 59
def prefixEnd_1067409 : Nat := 4983230072969 + 3 ^ 40 * 1067409 * 2
def baseEnd_1067409 : Nat := 548093871935119491078581

theorem tailTrace_1067409 : CollatzResearch.WordTrace tailWord_1067409 prefixEnd_1067409 548093871935119491078581 := by
  unfold tailWord_1067409
  simp only [CollatzResearch.WordTrace]
  refine ⟨38931604589966966788749281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25954403059977977859166187 38931604589966966788749281)
  ·
    refine ⟨29198703442475225091561961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38931604589966966788749281 29198703442475225091561961)
    ·
      refine ⟨21899027581856418818671471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29198703442475225091561961 21899027581856418818671471)
      ·
        refine ⟨32848541372784628228007207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21899027581856418818671471 32848541372784628228007207)
        ·
          refine ⟨49272812059176942342010811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32848541372784628228007207 49272812059176942342010811)
          ·
            refine ⟨73909218088765413513016217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49272812059176942342010811 73909218088765413513016217)
            ·
              refine ⟨55431913566574060134762163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73909218088765413513016217 55431913566574060134762163)
              ·
                refine ⟨83147870349861090202143245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55431913566574060134762163 83147870349861090202143245)
                ·
                  refine ⟨31180451381197908825803717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83147870349861090202143245 31180451381197908825803717)
                  ·
                    refine ⟨5846334633974607904838197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31180451381197908825803717 5846334633974607904838197)
                    ·
                      refine ⟨548093871935119491078581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5846334633974607904838197 548093871935119491078581)
                      ·
                        rfl

theorem cell23_1067409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_1067409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067409 prefixEnd_1067409 := by exact prefixLift 1067409
  have htrace : WordTrace (prefixWord ++ tailWord_1067409) baseStart_1067409 baseEnd_1067409 := by
    simpa [prefixWord, tailWord_1067409, baseEnd_1067409] using wordTrace_append hprefix tailTrace_1067409
  have hstable : (prefixWord ++ tailWord_1067409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067409).length < 2 ^ (prefixWord ++ tailWord_1067409).sum := by decide
  have hdescent : baseEnd_1067409 < baseStart_1067409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067426 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1067426 : Nat := 118140960795 + 1067426 * 2 ^ 59
def prefixEnd_1067426 : Nat := 4983230072969 + 3 ^ 40 * 1067426 * 2
def baseEnd_1067426 : Nat := 548102601106245924566003

theorem tailTrace_1067426 : CollatzResearch.WordTrace tailWord_1067426 prefixEnd_1067426 548102601106245924566003 := by
  unfold tailWord_1067426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9733056157726344673029533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25954816420603585794745421 9733056157726344673029533)
  ·
    refine ⟨3649896059147379252386075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9733056157726344673029533 3649896059147379252386075)
    ·
      refine ⟨5474844088721068878579113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3649896059147379252386075 5474844088721068878579113)
      ·
        refine ⟨4106133066540801658934335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5474844088721068878579113 4106133066540801658934335)
        ·
          refine ⟨6159199599811202488401503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106133066540801658934335 6159199599811202488401503)
          ·
            refine ⟨9238799399716803732602255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159199599811202488401503 9238799399716803732602255)
            ·
              refine ⟨13858199099575205598903383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238799399716803732602255 13858199099575205598903383)
              ·
                refine ⟨20787298649362808398355075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13858199099575205598903383 20787298649362808398355075)
                ·
                  refine ⟨31180947974044212597532613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20787298649362808398355075 31180947974044212597532613)
                  ·
                    refine ⟨5846427745133289862037365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31180947974044212597532613 5846427745133289862037365)
                    ·
                      refine ⟨548102601106245924566003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5846427745133289862037365 548102601106245924566003)
                      ·
                        rfl

theorem cell23_1067426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1067426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067426 prefixEnd_1067426 := by exact prefixLift 1067426
  have htrace : WordTrace (prefixWord ++ tailWord_1067426) baseStart_1067426 baseEnd_1067426 := by
    simpa [prefixWord, tailWord_1067426, baseEnd_1067426] using wordTrace_append hprefix tailTrace_1067426
  have hstable : (prefixWord ++ tailWord_1067426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067426).length < 2 ^ (prefixWord ++ tailWord_1067426).sum := by decide
  have hdescent : baseEnd_1067426 < baseStart_1067426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067456 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_1067456 : Nat := 118140960795 + 1067456 * 2 ^ 59
def prefixEnd_1067456 : Nat := 4983230072969 + 3 ^ 40 * 1067456 * 2
def baseEnd_1067456 : Nat := 548118005525880807190865

theorem tailTrace_1067456 : CollatzResearch.WordTrace tailWord_1067456 prefixEnd_1067456 548118005525880807190865 := by
  unfold tailWord_1067456
  simp only [CollatzResearch.WordTrace]
  refine ⟨19466659410398346907855111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25955545880531129210473481 19466659410398346907855111)
  ·
    refine ⟨29199989115597520361782667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19466659410398346907855111 29199989115597520361782667)
    ·
      refine ⟨43799983673396280542674001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29199989115597520361782667 43799983673396280542674001)
      ·
        refine ⟨32849987755047210407005501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43799983673396280542674001 32849987755047210407005501)
        ·
          refine ⟨12318745408142703902627063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32849987755047210407005501 12318745408142703902627063)
          ·
            refine ⟨18478118112214055853940595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12318745408142703902627063 18478118112214055853940595)
            ·
              refine ⟨27717177168321083780910893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18478118112214055853940595 27717177168321083780910893)
              ·
                refine ⟨10393941438120406417841585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27717177168321083780910893 10393941438120406417841585)
                ·
                  refine ⟨7795456078590304813381189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10393941438120406417841585 7795456078590304813381189)
                  ·
                    refine ⟨1461648014735682152508973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7795456078590304813381189 1461648014735682152508973)
                    ·
                      refine ⟨548118005525880807190865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1461648014735682152508973 548118005525880807190865)
                      ·
                        rfl

theorem cell23_1067456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_1067456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067456 prefixEnd_1067456 := by exact prefixLift 1067456
  have htrace : WordTrace (prefixWord ++ tailWord_1067456) baseStart_1067456 baseEnd_1067456 := by
    simpa [prefixWord, tailWord_1067456, baseEnd_1067456] using wordTrace_append hprefix tailTrace_1067456
  have hstable : (prefixWord ++ tailWord_1067456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067456).length < 2 ^ (prefixWord ++ tailWord_1067456).sum := by decide
  have hdescent : baseEnd_1067456 < baseStart_1067456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067466 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1067466 : Nat := 118140960795 + 1067466 * 2 ^ 59
def prefixEnd_1067466 : Nat := 4983230072969 + 3 ^ 40 * 1067466 * 2
def baseEnd_1067466 : Nat := 548123140332425768065819

theorem tailTrace_1067466 : CollatzResearch.WordTrace tailWord_1067466 prefixEnd_1067466 548123140332425768065819 := by
  unfold tailWord_1067466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9733420887690116380893563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25955789033840310349049501 9733420887690116380893563)
  ·
    refine ⟨14600131331535174571340345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9733420887690116380893563 14600131331535174571340345)
    ·
      refine ⟨10950098498651380928505259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14600131331535174571340345 10950098498651380928505259)
      ·
        refine ⟨16425147747977071392757889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10950098498651380928505259 16425147747977071392757889)
        ·
          refine ⟨12318860810982803544568417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16425147747977071392757889 12318860810982803544568417)
          ·
            refine ⟨9239145608237102658426313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12318860810982803544568417 9239145608237102658426313)
            ·
              refine ⟨6929359206177826993819735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9239145608237102658426313 6929359206177826993819735)
              ·
                refine ⟨10394038809266740490729603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929359206177826993819735 10394038809266740490729603)
                ·
                  refine ⟨15591058213900110736094405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10394038809266740490729603 15591058213900110736094405)
                  ·
                    refine ⟨2923323415106270763017701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15591058213900110736094405 2923323415106270763017701)
                    ·
                      refine ⟨548123140332425768065819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2923323415106270763017701 548123140332425768065819)
                      ·
                        rfl

theorem cell23_1067466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1067466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067466 prefixEnd_1067466 := by exact prefixLift 1067466
  have htrace : WordTrace (prefixWord ++ tailWord_1067466) baseStart_1067466 baseEnd_1067466 := by
    simpa [prefixWord, tailWord_1067466, baseEnd_1067466] using wordTrace_append hprefix tailTrace_1067466
  have hstable : (prefixWord ++ tailWord_1067466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067466).length < 2 ^ (prefixWord ++ tailWord_1067466).sum := by decide
  have hdescent : baseEnd_1067466 < baseStart_1067466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067510 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_1067510 : Nat := 118140960795 + 1067510 * 2 ^ 59
def prefixEnd_1067510 : Nat := 4983230072969 + 3 ^ 40 * 1067510 * 2
def baseEnd_1067510 : Nat := 60905081497913732879513

theorem tailTrace_1067510 : CollatzResearch.WordTrace tailWord_1067510 prefixEnd_1067510 60905081497913732879513 := by
  unfold tailWord_1067510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433455522662566314885999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25956858908400707358783989 2433455522662566314885999)
  ·
    refine ⟨3650183283993849472328999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2433455522662566314885999 3650183283993849472328999)
    ·
      refine ⟨5475274925990774208493499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3650183283993849472328999 5475274925990774208493499)
      ·
        refine ⟨8212912388986161312740249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475274925990774208493499 8212912388986161312740249)
        ·
          refine ⟨6159684291739620984555187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8212912388986161312740249 6159684291739620984555187)
          ·
            refine ⟨9239526437609431476832781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159684291739620984555187 9239526437609431476832781)
            ·
              refine ⟨3464822414103536803812293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9239526437609431476832781 3464822414103536803812293)
              ·
                refine ⟨649654202644413150714805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3464822414103536803812293 649654202644413150714805)
                ·
                  refine ⟨60905081497913732879513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 649654202644413150714805 60905081497913732879513)
                  ·
                    rfl

theorem cell23_1067510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_1067510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067510 prefixEnd_1067510 := by exact prefixLift 1067510
  have htrace : WordTrace (prefixWord ++ tailWord_1067510) baseStart_1067510 baseEnd_1067510 := by
    simpa [prefixWord, tailWord_1067510, baseEnd_1067510] using wordTrace_append hprefix tailTrace_1067510
  have hstable : (prefixWord ++ tailWord_1067510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067510).length < 2 ^ (prefixWord ++ tailWord_1067510).sum := by decide
  have hdescent : baseEnd_1067510 < baseStart_1067510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067513 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 2, 5, 2]
def baseStart_1067513 : Nat := 118140960795 + 1067513 * 2 ^ 59
def prefixEnd_1067513 : Nat := 4983230072969 + 3 ^ 40 * 1067513 * 2
def baseEnd_1067513 : Nat := 548147273923187084178103

theorem tailTrace_1067513 : CollatzResearch.WordTrace tailWord_1067513 prefixEnd_1067513 548147273923187084178103 := by
  unfold tailWord_1067513
  simp only [CollatzResearch.WordTrace]
  refine ⟨38935397781590192550535193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25956931854393461700356795 38935397781590192550535193)
  ·
    refine ⟨29201548336192644412901395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38935397781590192550535193 29201548336192644412901395)
    ·
      refine ⟨43802322504288966619352093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29201548336192644412901395 43802322504288966619352093)
      ·
        refine ⟨16425870939108362482257035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43802322504288966619352093 16425870939108362482257035)
        ·
          refine ⟨24638806408662543723385553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16425870939108362482257035 24638806408662543723385553)
          ·
            refine ⟨18479104806496907792539165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24638806408662543723385553 18479104806496907792539165)
            ·
              refine ⟨6929664302436340422202187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18479104806496907792539165 6929664302436340422202187)
              ·
                refine ⟨10394496453654510633303281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929664302436340422202187 10394496453654510633303281)
                ·
                  refine ⟨7795872340240882974977461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10394496453654510633303281 7795872340240882974977461)
                  ·
                    refine ⟨730863031897582778904137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7795872340240882974977461 730863031897582778904137)
                    ·
                      refine ⟨548147273923187084178103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 730863031897582778904137 548147273923187084178103)
                      ·
                        rfl

theorem cell23_1067513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_1067513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067513 prefixEnd_1067513 := by exact prefixLift 1067513
  have htrace : WordTrace (prefixWord ++ tailWord_1067513) baseStart_1067513 baseEnd_1067513 := by
    simpa [prefixWord, tailWord_1067513, baseEnd_1067513] using wordTrace_append hprefix tailTrace_1067513
  have hstable : (prefixWord ++ tailWord_1067513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067513).length < 2 ^ (prefixWord ++ tailWord_1067513).sum := by decide
  have hdescent : baseEnd_1067513 < baseStart_1067513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067540 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1067540 : Nat := 118140960795 + 1067540 * 2 ^ 59
def prefixEnd_1067540 : Nat := 4983230072969 + 3 ^ 40 * 1067540 * 2
def baseEnd_1067540 : Nat := 182720379300286159513493

theorem tailTrace_1067540 : CollatzResearch.WordTrace tailWord_1067540 prefixEnd_1067540 182720379300286159513493 := by
  unfold tailWord_1067540
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468191276246188080884037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25957588368328250774512049 19468191276246188080884037)
  ·
    refine ⟨3650285864296160265165757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19468191276246188080884037 3650285864296160265165757)
    ·
      refine ⟨1368857199111060099437159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3650285864296160265165757 1368857199111060099437159)
      ·
        refine ⟨2053285798666590149155739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368857199111060099437159 2053285798666590149155739)
        ·
          refine ⟨3079928697999885223733609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053285798666590149155739 3079928697999885223733609)
          ·
            refine ⟨2309946523499913917800207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079928697999885223733609 2309946523499913917800207)
            ·
              refine ⟨3464919785249870876700311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309946523499913917800207 3464919785249870876700311)
              ·
                refine ⟨5197379677874806315050467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3464919785249870876700311 5197379677874806315050467)
                ·
                  refine ⟨7796069516812209472575701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197379677874806315050467 7796069516812209472575701)
                  ·
                    refine ⟨182720379300286159513493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7796069516812209472575701 182720379300286159513493)
                    ·
                      rfl

theorem cell23_1067540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1067540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067540 prefixEnd_1067540 := by exact prefixLift 1067540
  have htrace : WordTrace (prefixWord ++ tailWord_1067540) baseStart_1067540 baseEnd_1067540 := by
    simpa [prefixWord, tailWord_1067540, baseEnd_1067540] using wordTrace_append hprefix tailTrace_1067540
  have hstable : (prefixWord ++ tailWord_1067540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067540).length < 2 ^ (prefixWord ++ tailWord_1067540).sum := by decide
  have hdescent : baseEnd_1067540 < baseStart_1067540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067553 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1067553 : Nat := 118140960795 + 1067553 * 2 ^ 59
def prefixEnd_1067553 : Nat := 4983230072969 + 3 ^ 40 * 1067553 * 2
def baseEnd_1067553 : Nat := 182722604383122309225973

theorem tailTrace_1067553 : CollatzResearch.WordTrace tailWord_1067553 prefixEnd_1067553 182722604383122309225973 := by
  unfold tailWord_1067553
  simp only [CollatzResearch.WordTrace]
  refine ⟨38936856701445279381991313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25957904467630186254660875 38936856701445279381991313)
  ·
    refine ⟨29202642526083959536493485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38936856701445279381991313 29202642526083959536493485)
    ·
      refine ⟨10950990947281484826185057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29202642526083959536493485 10950990947281484826185057)
      ·
        refine ⟨8213243210461113619638793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10950990947281484826185057 8213243210461113619638793)
        ·
          refine ⟨6159932407845835214729095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8213243210461113619638793 6159932407845835214729095)
          ·
            refine ⟨9239898611768752822093643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159932407845835214729095 9239898611768752822093643)
            ·
              refine ⟨13859847917653129233140465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9239898611768752822093643 13859847917653129233140465)
              ·
                refine ⟨10394885938239846924855349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13859847917653129233140465 10394885938239846924855349)
                ·
                  refine ⟨974520556709985649205189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10394885938239846924855349 974520556709985649205189)
                  ·
                    refine ⟨182722604383122309225973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974520556709985649205189 182722604383122309225973)
                    ·
                      rfl

theorem cell23_1067553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1067553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067553 prefixEnd_1067553 := by exact prefixLift 1067553
  have htrace : WordTrace (prefixWord ++ tailWord_1067553) baseStart_1067553 baseEnd_1067553 := by
    simpa [prefixWord, tailWord_1067553, baseEnd_1067553] using wordTrace_append hprefix tailTrace_1067553
  have hstable : (prefixWord ++ tailWord_1067553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067553).length < 2 ^ (prefixWord ++ tailWord_1067553).sum := by decide
  have hdescent : baseEnd_1067553 < baseStart_1067553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067563 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 3]
def baseStart_1067563 : Nat := 118140960795 + 1067563 * 2 ^ 59
def prefixEnd_1067563 : Nat := 4983230072969 + 3 ^ 40 * 1067563 * 2
def baseEnd_1067563 : Nat := 548172947955911888552873

theorem tailTrace_1067563 : CollatzResearch.WordTrace tailWord_1067563 prefixEnd_1067563 548172947955911888552873 := by
  unfold tailWord_1067563
  simp only [CollatzResearch.WordTrace]
  refine ⟨38937221431409051089855343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25958147620939367393236895 38937221431409051089855343)
  ·
    refine ⟨58405832147113576634783015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38937221431409051089855343 58405832147113576634783015)
    ·
      refine ⟨87608748220670364952174523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58405832147113576634783015 87608748220670364952174523)
      ·
        refine ⟨131413122331005547428261785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87608748220670364952174523 131413122331005547428261785)
        ·
          refine ⟨98559841748254160571196339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131413122331005547428261785 98559841748254160571196339)
          ·
            refine ⟨147839762622381240856794509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98559841748254160571196339 147839762622381240856794509)
            ·
              refine ⟨55439910983392965321297941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147839762622381240856794509 55439910983392965321297941)
              ·
                refine ⟨2598745827346545249435841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55439910983392965321297941 2598745827346545249435841)
                ·
                  refine ⟨1949059370509908937076881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598745827346545249435841 1949059370509908937076881)
                  ·
                    refine ⟨1461794527882431702807661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949059370509908937076881 1461794527882431702807661)
                    ·
                      refine ⟨548172947955911888552873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1461794527882431702807661 548172947955911888552873)
                      ·
                        rfl

theorem cell23_1067563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 3].length) (baseStart_1067563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067563 prefixEnd_1067563 := by exact prefixLift 1067563
  have htrace : WordTrace (prefixWord ++ tailWord_1067563) baseStart_1067563 baseEnd_1067563 := by
    simpa [prefixWord, tailWord_1067563, baseEnd_1067563] using wordTrace_append hprefix tailTrace_1067563
  have hstable : (prefixWord ++ tailWord_1067563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067563).length < 2 ^ (prefixWord ++ tailWord_1067563).sum := by decide
  have hdescent : baseEnd_1067563 < baseStart_1067563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067604 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_1067604 : Nat := 118140960795 + 1067604 * 2 ^ 59
def prefixEnd_1067604 : Nat := 4983230072969 + 3 ^ 40 * 1067604 * 2
def baseEnd_1067604 : Nat := 182731333554248742713395

theorem tailTrace_1067604 : CollatzResearch.WordTrace tailWord_1067604 prefixEnd_1067604 182731333554248742713395 := by
  unfold tailWord_1067604
  simp only [CollatzResearch.WordTrace]
  refine ⟨19469358412130257546048933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25959144549507010061398577 19469358412130257546048933)
  ·
    refine ⟨3650504702274423289884175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19469358412130257546048933 3650504702274423289884175)
    ·
      refine ⟨5475757053411634934826263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3650504702274423289884175 5475757053411634934826263)
      ·
        refine ⟨8213635580117452402239395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475757053411634934826263 8213635580117452402239395)
        ·
          refine ⟨12320453370176178603359093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213635580117452402239395 12320453370176178603359093)
          ·
            refine ⟨1155042503454016744064915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12320453370176178603359093 1155042503454016744064915)
            ·
              refine ⟨1732563755181025116097373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155042503454016744064915 1732563755181025116097373)
              ·
                refine ⟨649711408192884418536515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732563755181025116097373 649711408192884418536515)
                ·
                  refine ⟨974567112289326627804773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649711408192884418536515 974567112289326627804773)
                  ·
                    refine ⟨182731333554248742713395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974567112289326627804773 182731333554248742713395)
                    ·
                      rfl

theorem cell23_1067604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_1067604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067604 prefixEnd_1067604 := by exact prefixLift 1067604
  have htrace : WordTrace (prefixWord ++ tailWord_1067604) baseStart_1067604 baseEnd_1067604 := by
    simpa [prefixWord, tailWord_1067604, baseEnd_1067604] using wordTrace_append hprefix tailTrace_1067604
  have hstable : (prefixWord ++ tailWord_1067604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067604).length < 2 ^ (prefixWord ++ tailWord_1067604).sum := by decide
  have hdescent : baseEnd_1067604 < baseStart_1067604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067634 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_1067634 : Nat := 118140960795 + 1067634 * 2 ^ 59
def prefixEnd_1067634 : Nat := 4983230072969 + 3 ^ 40 * 1067634 * 2
def baseEnd_1067634 : Nat := 60912156120264567862783

theorem tailTrace_1067634 : CollatzResearch.WordTrace tailWord_1067634 prefixEnd_1067634 60912156120264567862783 := by
  unfold tailWord_1067634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9734952753537957553922489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25959874009434553477126637 9734952753537957553922489)
  ·
    refine ⟨7301214565153468165441867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9734952753537957553922489 7301214565153468165441867)
    ·
      refine ⟨10951821847730202248162801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7301214565153468165441867 10951821847730202248162801)
      ·
        refine ⟨8213866385797651686122101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10951821847730202248162801 8213866385797651686122101)
        ·
          refine ⟨770049973668529845573947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8213866385797651686122101 770049973668529845573947)
          ·
            refine ⟨1155074960502794768360921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770049973668529845573947 1155074960502794768360921)
            ·
              refine ⟨866306220377096076270691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155074960502794768360921 866306220377096076270691)
              ·
                refine ⟨1299459330565644114406037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866306220377096076270691 1299459330565644114406037)
                ·
                  refine ⟨60912156120264567862783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1299459330565644114406037 60912156120264567862783)
                  ·
                    rfl

theorem cell23_1067634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_1067634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067634 prefixEnd_1067634 := by exact prefixLift 1067634
  have htrace : WordTrace (prefixWord ++ tailWord_1067634) baseStart_1067634 baseEnd_1067634 := by
    simpa [prefixWord, tailWord_1067634, baseEnd_1067634] using wordTrace_append hprefix tailTrace_1067634
  have hstable : (prefixWord ++ tailWord_1067634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067634).length < 2 ^ (prefixWord ++ tailWord_1067634).sum := by decide
  have hdescent : baseEnd_1067634 < baseStart_1067634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067643 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 6, 4]
def baseStart_1067643 : Nat := 118140960795 + 1067643 * 2 ^ 59
def prefixEnd_1067643 : Nat := 4983230072969 + 3 ^ 40 * 1067643 * 2
def baseEnd_1067643 : Nat := 182738008802757191850835

theorem tailTrace_1067643 : CollatzResearch.WordTrace tailWord_1067643 prefixEnd_1067643 182738008802757191850835 := by
  unfold tailWord_1067643
  simp only [CollatzResearch.WordTrace]
  refine ⟨38940139271119224752767583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25960092847412816501845055 38940139271119224752767583)
  ·
    refine ⟨58410208906678837129151375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38940139271119224752767583 58410208906678837129151375)
    ·
      refine ⟨87615313360018255693727063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58410208906678837129151375 87615313360018255693727063)
      ·
        refine ⟨131422970040027383540590595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87615313360018255693727063 131422970040027383540590595)
        ·
          refine ⟨197134455060041075310885893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131422970040027383540590595 197134455060041075310885893)
          ·
            refine ⟨36962710323757701620791105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197134455060041075310885893 36962710323757701620791105)
            ·
              refine ⟨27722032742818276215593329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36962710323757701620791105 27722032742818276215593329)
              ·
                refine ⟨20791524557113707161694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27722032742818276215593329 20791524557113707161694997)
                ·
                  refine ⟨974602713614705023204453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20791524557113707161694997 974602713614705023204453)
                  ·
                    refine ⟨182738008802757191850835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974602713614705023204453 182738008802757191850835)
                    ·
                      rfl

theorem cell23_1067643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 4].length) (baseStart_1067643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067643 prefixEnd_1067643 := by exact prefixLift 1067643
  have htrace : WordTrace (prefixWord ++ tailWord_1067643) baseStart_1067643 baseEnd_1067643 := by
    simpa [prefixWord, tailWord_1067643, baseEnd_1067643] using wordTrace_append hprefix tailTrace_1067643
  have hstable : (prefixWord ++ tailWord_1067643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067643).length < 2 ^ (prefixWord ++ tailWord_1067643).sum := by decide
  have hdescent : baseEnd_1067643 < baseStart_1067643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067663 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_1067663 : Nat := 118140960795 + 1067663 * 2 ^ 59
def prefixEnd_1067663 : Nat := 4983230072969 + 3 ^ 40 * 1067663 * 2
def baseEnd_1067663 : Nat := 548224296021361497302413

theorem tailTrace_1067663 : CollatzResearch.WordTrace tailWord_1067663 prefixEnd_1067663 548224296021361497302413 := by
  unfold tailWord_1067663
  simp only [CollatzResearch.WordTrace]
  refine ⟨38940868731046768168495643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25960579154031178778997095 38940868731046768168495643)
  ·
    refine ⟨58411303096570152252743465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38940868731046768168495643 58411303096570152252743465)
    ·
      refine ⟨43808477322427614189557599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58411303096570152252743465 43808477322427614189557599)
      ·
        refine ⟨65712715983641421284336399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43808477322427614189557599 65712715983641421284336399)
        ·
          refine ⟨98569073975462131926504599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65712715983641421284336399 98569073975462131926504599)
          ·
            refine ⟨147853610963193197889756899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98569073975462131926504599 147853610963193197889756899)
            ·
              refine ⟨221780416444789796834635349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147853610963193197889756899 221780416444789796834635349)
              ·
                refine ⟨2598989255212380431655883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 221780416444789796834635349 2598989255212380431655883)
                ·
                  refine ⟨3898483882818570647483825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598989255212380431655883 3898483882818570647483825)
                  ·
                    refine ⟨2923862912113927985612869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3898483882818570647483825 2923862912113927985612869)
                    ·
                      refine ⟨548224296021361497302413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2923862912113927985612869 548224296021361497302413)
                      ·
                        rfl

theorem cell23_1067663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_1067663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067663 prefixEnd_1067663 := by exact prefixLift 1067663
  have htrace : WordTrace (prefixWord ++ tailWord_1067663) baseStart_1067663 baseEnd_1067663 := by
    simpa [prefixWord, tailWord_1067663, baseEnd_1067663] using wordTrace_append hprefix tailTrace_1067663
  have hstable : (prefixWord ++ tailWord_1067663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067663).length < 2 ^ (prefixWord ++ tailWord_1067663).sum := by decide
  have hdescent : baseEnd_1067663 < baseStart_1067663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067694 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1067694 : Nat := 118140960795 + 1067694 * 2 ^ 59
def prefixEnd_1067694 : Nat := 4983230072969 + 3 ^ 40 * 1067694 * 2
def baseEnd_1067694 : Nat := 182746737973883625338257

theorem tailTrace_1067694 : CollatzResearch.WordTrace tailWord_1067694 prefixEnd_1067694 182746737973883625338257 := by
  unfold tailWord_1067694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867749924241807557859267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25961332929289640308582757 4867749924241807557859267)
  ·
    refine ⟨7301624886362711336788901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4867749924241807557859267 7301624886362711336788901)
    ·
      refine ⟨1369054666193008375647919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7301624886362711336788901 1369054666193008375647919)
      ·
        refine ⟨2053581999289512563471879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369054666193008375647919 2053581999289512563471879)
        ·
          refine ⟨3080372998934268845207819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053581999289512563471879 3080372998934268845207819)
          ·
            refine ⟨4620559498401403267811729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080372998934268845207819 4620559498401403267811729)
            ·
              refine ⟨3465419623801052450858797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4620559498401403267811729 3465419623801052450858797)
              ·
                refine ⟨1299532358925394669072049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3465419623801052450858797 1299532358925394669072049)
                ·
                  refine ⟨974649269194046001804037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299532358925394669072049 974649269194046001804037)
                  ·
                    refine ⟨182746737973883625338257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974649269194046001804037 182746737973883625338257)
                    ·
                      rfl

theorem cell23_1067694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1067694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067694 prefixEnd_1067694 := by exact prefixLift 1067694
  have htrace : WordTrace (prefixWord ++ tailWord_1067694) baseStart_1067694 baseEnd_1067694 := by
    simpa [prefixWord, tailWord_1067694, baseEnd_1067694] using wordTrace_append hprefix tailTrace_1067694
  have hstable : (prefixWord ++ tailWord_1067694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067694).length < 2 ^ (prefixWord ++ tailWord_1067694).sum := by decide
  have hdescent : baseEnd_1067694 < baseStart_1067694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067808 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 2, 2, 2]
def baseStart_1067808 : Nat := 118140960795 + 1067808 * 2 ^ 59
def prefixEnd_1067808 : Nat := 4983230072969 + 3 ^ 40 * 1067808 * 2
def baseEnd_1067808 : Nat := 548298750716263429989247

theorem tailTrace_1067808 : CollatzResearch.WordTrace tailWord_1067808 prefixEnd_1067808 548298750716263429989247 := by
  unfold tailWord_1067808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19473078657760728966262039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25964104877014305288349385 19473078657760728966262039)
  ·
    refine ⟨29209617986641093449393059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19473078657760728966262039 29209617986641093449393059)
    ·
      refine ⟨43814426979961640174089589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29209617986641093449393059 43814426979961640174089589)
      ·
        refine ⟨4107602529371403766320899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43814426979961640174089589 4107602529371403766320899)
        ·
          refine ⟨6161403794057105649481349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107602529371403766320899 6161403794057105649481349)
          ·
            refine ⟨1155263211385707309277753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6161403794057105649481349 1155263211385707309277753)
            ·
              refine ⟨866447408539280481958315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155263211385707309277753 866447408539280481958315)
              ·
                refine ⟨1299671112808920722937473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866447408539280481958315 1299671112808920722937473)
                ·
                  refine ⟨974753334606690542203105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299671112808920722937473 974753334606690542203105)
                  ·
                    refine ⟨731065000955017906652329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 974753334606690542203105 731065000955017906652329)
                    ·
                      refine ⟨548298750716263429989247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731065000955017906652329 548298750716263429989247)
                      ·
                        rfl

theorem cell23_1067808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_1067808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067808 prefixEnd_1067808 := by exact prefixLift 1067808
  have htrace : WordTrace (prefixWord ++ tailWord_1067808) baseStart_1067808 baseEnd_1067808 := by
    simpa [prefixWord, tailWord_1067808, baseEnd_1067808] using wordTrace_append hprefix tailTrace_1067808
  have hstable : (prefixWord ++ tailWord_1067808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067808).length < 2 ^ (prefixWord ++ tailWord_1067808).sum := by decide
  have hdescent : baseEnd_1067808 < baseStart_1067808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067827 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 2, 5]
def baseStart_1067827 : Nat := 118140960795 + 1067827 * 2 ^ 59
def prefixEnd_1067827 : Nat := 4983230072969 + 3 ^ 40 * 1067827 * 2
def baseEnd_1067827 : Nat := 182769502282899618550553

theorem tailTrace_1067827 : CollatzResearch.WordTrace tailWord_1067827 prefixEnd_1067827 182769502282899618550553 := by
  unfold tailWord_1067827
  simp only [CollatzResearch.WordTrace]
  refine ⟨38946850302452624177465735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25964566868301749451643823 38946850302452624177465735)
  ·
    refine ⟨58420275453678936266198603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38946850302452624177465735 58420275453678936266198603)
    ·
      refine ⟨87630413180518404399297905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58420275453678936266198603 87630413180518404399297905)
      ·
        refine ⟨65722809885388803299473429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87630413180518404399297905 65722809885388803299473429)
        ·
          refine ⟨3080756713377600154662817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65722809885388803299473429 3080756713377600154662817)
          ·
            refine ⟨2310567535033200115997113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3080756713377600154662817 2310567535033200115997113)
            ·
              refine ⟨1732925651274900086997835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310567535033200115997113 1732925651274900086997835)
              ·
                refine ⟨2599388476912350130496753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732925651274900086997835 2599388476912350130496753)
                ·
                  refine ⟨1949541357684262597872565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2599388476912350130496753 1949541357684262597872565)
                  ·
                    refine ⟨182769502282899618550553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1949541357684262597872565 182769502282899618550553)
                    ·
                      rfl

theorem cell23_1067827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 5].length) (baseStart_1067827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067827 prefixEnd_1067827 := by exact prefixLift 1067827
  have htrace : WordTrace (prefixWord ++ tailWord_1067827) baseStart_1067827 baseEnd_1067827 := by
    simpa [prefixWord, tailWord_1067827, baseEnd_1067827] using wordTrace_append hprefix tailTrace_1067827
  have hstable : (prefixWord ++ tailWord_1067827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067827).length < 2 ^ (prefixWord ++ tailWord_1067827).sum := by decide
  have hdescent : baseEnd_1067827 < baseStart_1067827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067847 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_1067847 : Nat := 118140960795 + 1067847 * 2 ^ 59
def prefixEnd_1067847 : Nat := 4983230072969 + 3 ^ 40 * 1067847 * 2
def baseEnd_1067847 : Nat := 548318776461788777401567

theorem tailTrace_1067847 : CollatzResearch.WordTrace tailWord_1067847 prefixEnd_1067847 548318776461788777401567 := by
  unfold tailWord_1067847
  simp only [CollatzResearch.WordTrace]
  refine ⟨38947579762380167593193795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25965053174920111728795863 38947579762380167593193795)
  ·
    refine ⟨58421369643570251389790693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38947579762380167593193795 58421369643570251389790693)
    ·
      refine ⟨10954006808169422135585755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58421369643570251389790693 10954006808169422135585755)
      ·
        refine ⟨16431010212254133203378633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10954006808169422135585755 16431010212254133203378633)
        ·
          refine ⟨12323257659190599902533975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16431010212254133203378633 12323257659190599902533975)
          ·
            refine ⟨18484886488785899853800963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12323257659190599902533975 18484886488785899853800963)
            ·
              refine ⟨27727329733178849780701445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18484886488785899853800963 27727329733178849780701445)
              ·
                refine ⟨5198874324971034333881521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27727329733178849780701445 5198874324971034333881521)
                ·
                  refine ⟨3899155743728275750411141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198874324971034333881521 3899155743728275750411141)
                  ·
                    refine ⟨731091701949051703202089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3899155743728275750411141 731091701949051703202089)
                    ·
                      refine ⟨548318776461788777401567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731091701949051703202089 548318776461788777401567)
                      ·
                        rfl

theorem cell23_1067847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_1067847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067847 prefixEnd_1067847 := by exact prefixLift 1067847
  have htrace : WordTrace (prefixWord ++ tailWord_1067847) baseStart_1067847 baseEnd_1067847 := by
    simpa [prefixWord, tailWord_1067847, baseEnd_1067847] using wordTrace_append hprefix tailTrace_1067847
  have hstable : (prefixWord ++ tailWord_1067847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067847).length < 2 ^ (prefixWord ++ tailWord_1067847).sum := by decide
  have hdescent : baseEnd_1067847 < baseStart_1067847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067924 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_1067924 : Nat := 118140960795 + 1067924 * 2 ^ 59
def prefixEnd_1067924 : Nat := 4983230072969 + 3 ^ 40 * 1067924 * 2
def baseEnd_1067924 : Nat := 548358314472184976138713

theorem tailTrace_1067924 : CollatzResearch.WordTrace tailWord_1067924 prefixEnd_1067924 548358314472184976138713 := by
  unfold tailWord_1067924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19475194091550604871873413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25966925455400806495831217 19475194091550604871873413)
  ·
    refine ⟨3651598892165738413476265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19475194091550604871873413 3651598892165738413476265)
    ·
      refine ⟨2738699169124303810107199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3651598892165738413476265 2738699169124303810107199)
      ·
        refine ⟨4108048753686455715160799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738699169124303810107199 4108048753686455715160799)
        ·
          refine ⟨6162073130529683572741199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108048753686455715160799 6162073130529683572741199)
          ·
            refine ⟨9243109695794525359111799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6162073130529683572741199 9243109695794525359111799)
            ·
              refine ⟨13864664543691788038667699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9243109695794525359111799 13864664543691788038667699)
              ·
                refine ⟨20796996815537682058001549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13864664543691788038667699 20796996815537682058001549)
                ·
                  refine ⟨7798873805826630771750581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20796996815537682058001549 7798873805826630771750581)
                  ·
                    refine ⟨731144419296246634851617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7798873805826630771750581 731144419296246634851617)
                    ·
                      refine ⟨548358314472184976138713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731144419296246634851617 548358314472184976138713)
                      ·
                        rfl

theorem cell23_1067924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_1067924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067924 prefixEnd_1067924 := by exact prefixLift 1067924
  have htrace : WordTrace (prefixWord ++ tailWord_1067924) baseStart_1067924 baseEnd_1067924 := by
    simpa [prefixWord, tailWord_1067924, baseEnd_1067924] using wordTrace_append hprefix tailTrace_1067924
  have hstable : (prefixWord ++ tailWord_1067924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067924).length < 2 ^ (prefixWord ++ tailWord_1067924).sum := by decide
  have hdescent : baseEnd_1067924 < baseStart_1067924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067960 : List Nat := [2, 1, 2, 1, 2, 4, 11]
def baseStart_1067960 : Nat := 118140960795 + 1067960 * 2 ^ 59
def prefixEnd_1067960 : Nat := 4983230072969 + 3 ^ 40 * 1067960 * 2
def baseEnd_1067960 : Nat := 6770083947848726361587

theorem tailTrace_1067960 : CollatzResearch.WordTrace tailWord_1067960 prefixEnd_1067960 6770083947848726361587 := by
  unfold tailWord_1067960
  simp only [CollatzResearch.WordTrace]
  refine ⟨19475850605485393946028667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25967800807313858594704889 19475850605485393946028667)
  ·
    refine ⟨29213775908228090919043001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19475850605485393946028667 29213775908228090919043001)
    ·
      refine ⟨21910331931171068189282251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29213775908228090919043001 21910331931171068189282251)
      ·
        refine ⟨32865497896756602283923377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21910331931171068189282251 32865497896756602283923377)
        ·
          refine ⟨24649123422567451712942533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32865497896756602283923377 24649123422567451712942533)
          ·
            refine ⟨4621710641731397196176725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24649123422567451712942533 4621710641731397196176725)
            ·
              refine ⟨6770083947848726361587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4621710641731397196176725 6770083947848726361587)
              ·
                rfl

theorem cell23_1067960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 11].length) (baseStart_1067960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067960 prefixEnd_1067960 := by exact prefixLift 1067960
  have htrace : WordTrace (prefixWord ++ tailWord_1067960) baseStart_1067960 baseEnd_1067960 := by
    simpa [prefixWord, tailWord_1067960, baseEnd_1067960] using wordTrace_append hprefix tailTrace_1067960
  have hstable : (prefixWord ++ tailWord_1067960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067960).length < 2 ^ (prefixWord ++ tailWord_1067960).sum := by decide
  have hdescent : baseEnd_1067960 < baseStart_1067960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1067965 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_1067965 : Nat := 118140960795 + 1067965 * 2 ^ 59
def prefixEnd_1067965 : Nat := 4983230072969 + 3 ^ 40 * 1067965 * 2
def baseEnd_1067965 : Nat := 548379367179019315726025

theorem tailTrace_1067965 : CollatzResearch.WordTrace tailWord_1067965 prefixEnd_1067965 548379367179019315726025 := by
  unfold tailWord_1067965
  simp only [CollatzResearch.WordTrace]
  refine ⟨38951883575952673745989349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25967922383968449163992899 38951883575952673745989349)
  ·
    refine ⟨7303478170491126327373003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38951883575952673745989349 7303478170491126327373003)
    ·
      refine ⟨10955217255736689491059505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7303478170491126327373003 10955217255736689491059505)
      ·
        refine ⟨8216412941802517118294629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10955217255736689491059505 8216412941802517118294629)
        ·
          refine ⟨1540577426587971959680243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8216412941802517118294629 1540577426587971959680243)
          ·
            refine ⟨2310866139881957939520365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540577426587971959680243 2310866139881957939520365)
            ·
              refine ⟨866574802455734227320137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2310866139881957939520365 866574802455734227320137)
              ·
                refine ⟨649931101841800670490103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866574802455734227320137 649931101841800670490103)
                ·
                  refine ⟨974896652762701005735155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649931101841800670490103 974896652762701005735155)
                  ·
                    refine ⟨1462344979144051508602733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974896652762701005735155 1462344979144051508602733)
                    ·
                      refine ⟨548379367179019315726025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1462344979144051508602733 548379367179019315726025)
                      ·
                        rfl

theorem cell23_1067965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_1067965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1067965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1067965 prefixEnd_1067965 := by exact prefixLift 1067965
  have htrace : WordTrace (prefixWord ++ tailWord_1067965) baseStart_1067965 baseEnd_1067965 := by
    simpa [prefixWord, tailWord_1067965, baseEnd_1067965] using wordTrace_append hprefix tailTrace_1067965
  have hstable : (prefixWord ++ tailWord_1067965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1067965).length < 2 ^ (prefixWord ++ tailWord_1067965).sum := by decide
  have hdescent : baseEnd_1067965 < baseStart_1067965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1067965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068004 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_1068004 : Nat := 118140960795 + 1068004 * 2 ^ 59
def prefixEnd_1068004 : Nat := 4983230072969 + 3 ^ 40 * 1068004 * 2
def baseEnd_1068004 : Nat := 548399392924544663138345

theorem tailTrace_1068004 : CollatzResearch.WordTrace tailWord_1068004 prefixEnd_1068004 548399392924544663138345 := by
  unfold tailWord_1068004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19476653011405691703329533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25968870681874255604439377 19476653011405691703329533)
  ·
    refine ⟨7303744879277134388748575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19476653011405691703329533 7303744879277134388748575)
    ·
      refine ⟨10955617318915701583122863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7303744879277134388748575 10955617318915701583122863)
      ·
        refine ⟨16433425978373552374684295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10955617318915701583122863 16433425978373552374684295)
        ·
          refine ⟨24650138967560328562026443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16433425978373552374684295 24650138967560328562026443)
          ·
            refine ⟨36975208451340492843039665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24650138967560328562026443 36975208451340492843039665)
            ·
              refine ⟨27731406338505369632279749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36975208451340492843039665 27731406338505369632279749)
              ·
                refine ⟨5199638688469756806052453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27731406338505369632279749 5199638688469756806052453)
                ·
                  refine ⟨974932254088079401134835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5199638688469756806052453 974932254088079401134835)
                  ·
                    refine ⟨1462398381132119101702253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974932254088079401134835 1462398381132119101702253)
                    ·
                      refine ⟨548399392924544663138345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1462398381132119101702253 548399392924544663138345)
                      ·
                        rfl

theorem cell23_1068004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_1068004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068004 prefixEnd_1068004 := by exact prefixLift 1068004
  have htrace : WordTrace (prefixWord ++ tailWord_1068004) baseStart_1068004 baseEnd_1068004 := by
    simpa [prefixWord, tailWord_1068004, baseEnd_1068004] using wordTrace_append hprefix tailTrace_1068004
  have hstable : (prefixWord ++ tailWord_1068004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068004).length < 2 ^ (prefixWord ++ tailWord_1068004).sum := by decide
  have hdescent : baseEnd_1068004 < baseStart_1068004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068022 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_1068022 : Nat := 118140960795 + 1068022 * 2 ^ 59
def prefixEnd_1068022 : Nat := 4983230072969 + 3 ^ 40 * 1068022 * 2
def baseEnd_1068022 : Nat := 548408635576325592713263

theorem tailTrace_1068022 : CollatzResearch.WordTrace tailWord_1068022 prefixEnd_1068022 548408635576325592713263 := by
  unfold tailWord_1068022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434622658546635780050895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25969308357830781653876213 2434622658546635780050895)
  ·
    refine ⟨3651933987819953670076343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2434622658546635780050895 3651933987819953670076343)
    ·
      refine ⟨5477900981729930505114515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3651933987819953670076343 5477900981729930505114515)
      ·
        refine ⟨8216851472594895757671773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5477900981729930505114515 8216851472594895757671773)
        ·
          refine ⟨3081319302223085909126915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8216851472594895757671773 3081319302223085909126915)
          ·
            refine ⟨4621978953334628863690373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081319302223085909126915 4621978953334628863690373)
            ·
              refine ⟨866621053750242911941945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4621978953334628863690373 866621053750242911941945)
              ·
                refine ⟨649965790312682183956459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866621053750242911941945 649965790312682183956459)
                ·
                  refine ⟨974948685469023275934689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649965790312682183956459 974948685469023275934689)
                  ·
                    refine ⟨731211514101767456951017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 974948685469023275934689 731211514101767456951017)
                    ·
                      refine ⟨548408635576325592713263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731211514101767456951017 548408635576325592713263)
                      ·
                        rfl

theorem cell23_1068022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_1068022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068022 prefixEnd_1068022 := by exact prefixLift 1068022
  have htrace : WordTrace (prefixWord ++ tailWord_1068022) baseStart_1068022 baseEnd_1068022 := by
    simpa [prefixWord, tailWord_1068022, baseEnd_1068022] using wordTrace_append hprefix tailTrace_1068022
  have hstable : (prefixWord ++ tailWord_1068022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068022).length < 2 ^ (prefixWord ++ tailWord_1068022).sum := by decide
  have hdescent : baseEnd_1068022 < baseStart_1068022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068037 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_1068037 : Nat := 118140960795 + 1068037 * 2 ^ 59
def prefixEnd_1068037 : Nat := 4983230072969 + 3 ^ 40 * 1068037 * 2
def baseEnd_1068037 : Nat := 182805445928714344675231

theorem tailTrace_1068037 : CollatzResearch.WordTrace tailWord_1068037 prefixEnd_1068037 182805445928714344675231 := by
  unfold tailWord_1068037
  simp only [CollatzResearch.WordTrace]
  refine ⟨38954509631691830042610365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25969673087794553361740243 38954509631691830042610365)
  ·
    refine ⟨14607941111884436265978887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38954509631691830042610365 14607941111884436265978887)
    ·
      refine ⟨21911911667826654398968331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14607941111884436265978887 21911911667826654398968331)
      ·
        refine ⟨32867867501739981598452497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21911911667826654398968331 32867867501739981598452497)
        ·
          refine ⟨24650900626304986198839373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32867867501739981598452497 24650900626304986198839373)
          ·
            refine ⟨9244087734864369824564765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24650900626304986198839373 9244087734864369824564765)
            ·
              refine ⟨3466532900574138684211787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9244087734864369824564765 3466532900574138684211787)
              ·
                refine ⟨5199799350861208026317681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466532900574138684211787 5199799350861208026317681)
                ·
                  refine ⟨3899849513145906019738261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5199799350861208026317681 3899849513145906019738261)
                  ·
                    refine ⟨182805445928714344675231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3899849513145906019738261 182805445928714344675231)
                    ·
                      rfl

theorem cell23_1068037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_1068037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068037 prefixEnd_1068037 := by exact prefixLift 1068037
  have htrace : WordTrace (prefixWord ++ tailWord_1068037) baseStart_1068037 baseEnd_1068037 := by
    simpa [prefixWord, tailWord_1068037, baseEnd_1068037] using wordTrace_append hprefix tailTrace_1068037
  have hstable : (prefixWord ++ tailWord_1068037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068037).length < 2 ^ (prefixWord ++ tailWord_1068037).sum := by decide
  have hdescent : baseEnd_1068037 < baseStart_1068037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068065 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1068065 : Nat := 118140960795 + 1068065 * 2 ^ 59
def prefixEnd_1068065 : Nat := 4983230072969 + 3 ^ 40 * 1068065 * 2
def baseEnd_1068065 : Nat := 548430715244468924475565

theorem tailTrace_1068065 : CollatzResearch.WordTrace tailWord_1068065 prefixEnd_1068065 548430715244468924475565 := by
  unfold tailWord_1068065
  simp only [CollatzResearch.WordTrace]
  refine ⟨38955530875590390824629649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25970353917060260549753099 38955530875590390824629649)
  ·
    refine ⟨29216648156692793118472237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38955530875590390824629649 29216648156692793118472237)
    ·
      refine ⟨10956243058759797419427089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29216648156692793118472237 10956243058759797419427089)
      ·
        refine ⟨8217182294069848064570317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10956243058759797419427089 8217182294069848064570317)
        ·
          refine ⟨3081443360276193024213869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8217182294069848064570317 3081443360276193024213869)
          ·
            refine ⟨1155541260103572384080201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3081443360276193024213869 1155541260103572384080201)
            ·
              refine ⟨866655945077679288060151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155541260103572384080201 866655945077679288060151)
              ·
                refine ⟨1299983917616518932090227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866655945077679288060151 1299983917616518932090227)
                ·
                  refine ⟨1949975876424778398135341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299983917616518932090227 1949975876424778398135341)
                  ·
                    refine ⟨731240953659291899300753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949975876424778398135341 731240953659291899300753)
                    ·
                      refine ⟨548430715244468924475565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731240953659291899300753 548430715244468924475565)
                      ·
                        rfl

theorem cell23_1068065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1068065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068065 prefixEnd_1068065 := by exact prefixLift 1068065
  have htrace : WordTrace (prefixWord ++ tailWord_1068065) baseStart_1068065 baseEnd_1068065 := by
    simpa [prefixWord, tailWord_1068065, baseEnd_1068065] using wordTrace_append hprefix tailTrace_1068065
  have hstable : (prefixWord ++ tailWord_1068065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068065).length < 2 ^ (prefixWord ++ tailWord_1068065).sum := by decide
  have hdescent : baseEnd_1068065 < baseStart_1068065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068078 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1068078 : Nat := 118140960795 + 1068078 * 2 ^ 59
def prefixEnd_1068078 : Nat := 4983230072969 + 3 ^ 40 * 1068078 * 2
def baseEnd_1068078 : Nat := 548437390492977373613005

theorem tailTrace_1068078 : CollatzResearch.WordTrace tailWord_1068078 prefixEnd_1068078 548437390492977373613005 := by
  unfold tailWord_1068078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869500628067911755606611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25970670016362196029901925 4869500628067911755606611)
  ·
    refine ⟨7304250942101867633409917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4869500628067911755606611 7304250942101867633409917)
    ·
      refine ⟨2739094103288200362528719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7304250942101867633409917 2739094103288200362528719)
      ·
        refine ⟨4108641154932300543793079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739094103288200362528719 4108641154932300543793079)
        ·
          refine ⟨6162961732398450815689619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108641154932300543793079 6162961732398450815689619)
          ·
            refine ⟨9244442598597676223534429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6162961732398450815689619 9244442598597676223534429)
            ·
              refine ⟨3466665974474128583825411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9244442598597676223534429 3466665974474128583825411)
              ·
                refine ⟨5199998961711192875738117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466665974474128583825411 5199998961711192875738117)
                ·
                  refine ⟨974999805320848664200897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5199998961711192875738117 974999805320848664200897)
                  ·
                    refine ⟨731249853990636498150673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 974999805320848664200897 731249853990636498150673)
                    ·
                      refine ⟨548437390492977373613005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731249853990636498150673 548437390492977373613005)
                      ·
                        rfl

theorem cell23_1068078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1068078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068078 prefixEnd_1068078 := by exact prefixLift 1068078
  have htrace : WordTrace (prefixWord ++ tailWord_1068078) baseStart_1068078 baseEnd_1068078 := by
    simpa [prefixWord, tailWord_1068078, baseEnd_1068078] using wordTrace_append hprefix tailTrace_1068078
  have hstable : (prefixWord ++ tailWord_1068078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068078).length < 2 ^ (prefixWord ++ tailWord_1068078).sum := by decide
  have hdescent : baseEnd_1068078 < baseStart_1068078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068114 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1068114 : Nat := 118140960795 + 1068114 * 2 ^ 59
def prefixEnd_1068114 : Nat := 4983230072969 + 3 ^ 40 * 1068114 * 2
def baseEnd_1068114 : Nat := 182818625265513077587613

theorem tailTrace_1068114 : CollatzResearch.WordTrace tailWord_1068114 prefixEnd_1068114 182818625265513077587613 := by
  unfold tailWord_1068114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739329513103218048290849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25971545368275248128775597 9739329513103218048290849)
  ·
    refine ⟨7304497134827413536218137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9739329513103218048290849 7304497134827413536218137)
    ·
      refine ⟨5478372851120560152163603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7304497134827413536218137 5478372851120560152163603)
      ·
        refine ⟨8217559276680840228245405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5478372851120560152163603 8217559276680840228245405)
        ·
          refine ⟨3081584728755315085592027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8217559276680840228245405 3081584728755315085592027)
          ·
            refine ⟨4622377093132972628388041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081584728755315085592027 4622377093132972628388041)
            ·
              refine ⟨3466782819849729471291031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4622377093132972628388041 3466782819849729471291031)
              ·
                refine ⟨5200174229774594206936547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466782819849729471291031 5200174229774594206936547)
                ·
                  refine ⟨7800261344661891310404821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200174229774594206936547 7800261344661891310404821)
                  ·
                    refine ⟨182818625265513077587613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7800261344661891310404821 182818625265513077587613)
                    ·
                      rfl

theorem cell23_1068114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1068114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068114 prefixEnd_1068114 := by exact prefixLift 1068114
  have htrace : WordTrace (prefixWord ++ tailWord_1068114) baseStart_1068114 baseEnd_1068114 := by
    simpa [prefixWord, tailWord_1068114, baseEnd_1068114] using wordTrace_append hprefix tailTrace_1068114
  have hstable : (prefixWord ++ tailWord_1068114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068114).length < 2 ^ (prefixWord ++ tailWord_1068114).sum := by decide
  have hdescent : baseEnd_1068114 < baseStart_1068114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068124 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1068124 : Nat := 118140960795 + 1068124 * 2 ^ 59
def prefixEnd_1068124 : Nat := 4983230072969 + 3 ^ 40 * 1068124 * 2
def baseEnd_1068124 : Nat := 548461010603084193637793

theorem tailTrace_1068124 : CollatzResearch.WordTrace tailWord_1068124 prefixEnd_1068124 548461010603084193637793 := by
  unfold tailWord_1068124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19478841391188321950513713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25971788521584429267351617 19478841391188321950513713)
  ·
    refine ⟨14609131043391241462885285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19478841391188321950513713 14609131043391241462885285)
    ·
      refine ⟨2739212070635857774290991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14609131043391241462885285 2739212070635857774290991)
      ·
        refine ⟨4108818105953786661436487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739212070635857774290991 4108818105953786661436487)
        ·
          refine ⟨6163227158930679992154731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108818105953786661436487 6163227158930679992154731)
          ·
            refine ⟨9244840738396019988232097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6163227158930679992154731 9244840738396019988232097)
            ·
              refine ⟨6933630553797014991174073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9244840738396019988232097 6933630553797014991174073)
              ·
                refine ⟨5200222915347761243380555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6933630553797014991174073 5200222915347761243380555)
                ·
                  refine ⟨7800334373021641865070833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200222915347761243380555 7800334373021641865070833)
                  ·
                    refine ⟨5850250779766231398803125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7800334373021641865070833 5850250779766231398803125)
                    ·
                      refine ⟨548461010603084193637793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5850250779766231398803125 548461010603084193637793)
                      ·
                        rfl

theorem cell23_1068124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1068124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068124 prefixEnd_1068124 := by exact prefixLift 1068124
  have htrace : WordTrace (prefixWord ++ tailWord_1068124) baseStart_1068124 baseEnd_1068124 := by
    simpa [prefixWord, tailWord_1068124, baseEnd_1068124] using wordTrace_append hprefix tailTrace_1068124
  have hstable : (prefixWord ++ tailWord_1068124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068124).length < 2 ^ (prefixWord ++ tailWord_1068124).sum := by decide
  have hdescent : baseEnd_1068124 < baseStart_1068124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068168 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1068168 : Nat := 118140960795 + 1068168 * 2 ^ 59
def prefixEnd_1068168 : Nat := 4983230072969 + 3 ^ 40 * 1068168 * 2
def baseEnd_1068168 : Nat := 548483603751882021487591

theorem tailTrace_1068168 : CollatzResearch.WordTrace tailWord_1068168 prefixEnd_1068168 548483603751882021487591 := by
  unfold tailWord_1068168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479643797108619707814579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25972858396144826277086105 19479643797108619707814579)
  ·
    refine ⟨29219465695662929561721869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19479643797108619707814579 29219465695662929561721869)
    ·
      refine ⟨10957299635873598585645701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29219465695662929561721869 10957299635873598585645701)
      ·
        refine ⟨2054493681726299734808569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10957299635873598585645701 2054493681726299734808569)
        ·
          refine ⟨1540870261294724801106427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054493681726299734808569 1540870261294724801106427)
          ·
            refine ⟨2311305391942087201659641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540870261294724801106427 2311305391942087201659641)
            ·
              refine ⟨1733479043956565401244731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2311305391942087201659641 1733479043956565401244731)
              ·
                refine ⟨2600218565934848101867097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733479043956565401244731 2600218565934848101867097)
                ·
                  refine ⟨1950163924451136076400323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600218565934848101867097 1950163924451136076400323)
                  ·
                    refine ⟨2925245886676704114600485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1950163924451136076400323 2925245886676704114600485)
                    ·
                      refine ⟨548483603751882021487591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2925245886676704114600485 548483603751882021487591)
                      ·
                        rfl

theorem cell23_1068168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1068168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068168 prefixEnd_1068168 := by exact prefixLift 1068168
  have htrace : WordTrace (prefixWord ++ tailWord_1068168) baseStart_1068168 baseEnd_1068168 := by
    simpa [prefixWord, tailWord_1068168, baseEnd_1068168] using wordTrace_append hprefix tailTrace_1068168
  have hstable : (prefixWord ++ tailWord_1068168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068168).length < 2 ^ (prefixWord ++ tailWord_1068168).sum := by decide
  have hdescent : baseEnd_1068168 < baseStart_1068168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068211 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 4, 3, 2]
def baseStart_1068211 : Nat := 118140960795 + 1068211 * 2 ^ 59
def prefixEnd_1068211 : Nat := 4983230072969 + 3 ^ 40 * 1068211 * 2
def baseEnd_1068211 : Nat := 548505683420025353249893

theorem tailTrace_1068211 : CollatzResearch.WordTrace tailWord_1068211 prefixEnd_1068211 548505683420025353249893 := by
  unfold tailWord_1068211
  simp only [CollatzResearch.WordTrace]
  refine ⟨38960855933061457759444487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25973903955374305172962991 38960855933061457759444487)
  ·
    refine ⟨58441283899592186639166731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38960855933061457759444487 58441283899592186639166731)
    ·
      refine ⟨87661925849388279958750097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58441283899592186639166731 87661925849388279958750097)
      ·
        refine ⟨65746444387041209969062573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87661925849388279958750097 65746444387041209969062573)
        ·
          refine ⟨24654916645140453738398465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65746444387041209969062573 24654916645140453738398465)
          ·
            refine ⟨18491187483855340303798849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24654916645140453738398465 18491187483855340303798849)
            ·
              refine ⟨13868390612891505227849137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18491187483855340303798849 13868390612891505227849137)
              ·
                refine ⟨10401292959668628920886853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13868390612891505227849137 10401292959668628920886853)
                ·
                  refine ⟨1950242429937867922666285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10401292959668628920886853 1950242429937867922666285)
                  ·
                    refine ⟨731340911226700470999857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950242429937867922666285 731340911226700470999857)
                    ·
                      refine ⟨548505683420025353249893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731340911226700470999857 548505683420025353249893)
                      ·
                        rfl

theorem cell23_1068211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3, 2].length) (baseStart_1068211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068211 prefixEnd_1068211 := by exact prefixLift 1068211
  have htrace : WordTrace (prefixWord ++ tailWord_1068211) baseStart_1068211 baseEnd_1068211 := by
    simpa [prefixWord, tailWord_1068211, baseEnd_1068211] using wordTrace_append hprefix tailTrace_1068211
  have hstable : (prefixWord ++ tailWord_1068211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068211).length < 2 ^ (prefixWord ++ tailWord_1068211).sum := by decide
  have hdescent : baseEnd_1068211 < baseStart_1068211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068238 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_1068238 : Nat := 118140960795 + 1068238 * 2 ^ 59
def prefixEnd_1068238 : Nat := 4983230072969 + 3 ^ 40 * 1068238 * 2
def baseEnd_1068238 : Nat := 182839849132565582537423

theorem tailTrace_1068238 : CollatzResearch.WordTrace tailWord_1068238 prefixEnd_1068238 182839849132565582537423 := by
  unfold tailWord_1068238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870230087995455171334671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25974560469309094247118245 4870230087995455171334671)
  ·
    refine ⟨7305345131993182757002007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4870230087995455171334671 7305345131993182757002007)
    ·
      refine ⟨10958017697989774135503011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7305345131993182757002007 10958017697989774135503011)
      ·
        refine ⟨16437026546984661203254517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10958017697989774135503011 16437026546984661203254517)
        ·
          refine ⟨1540971238779811987805111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16437026546984661203254517 1540971238779811987805111)
          ·
            refine ⟨2311456858169717981707667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540971238779811987805111 2311456858169717981707667)
            ·
              refine ⟨3467185287254576972561501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311456858169717981707667 3467185287254576972561501)
              ·
                refine ⟨1300194482720466364710563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3467185287254576972561501 1300194482720466364710563)
                ·
                  refine ⟨1950291724080699547065845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300194482720466364710563 1950291724080699547065845)
                  ·
                    refine ⟨182839849132565582537423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1950291724080699547065845 182839849132565582537423)
                    ·
                      rfl

theorem cell23_1068238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_1068238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068238 prefixEnd_1068238 := by exact prefixLift 1068238
  have htrace : WordTrace (prefixWord ++ tailWord_1068238) baseStart_1068238 baseEnd_1068238 := by
    simpa [prefixWord, tailWord_1068238, baseEnd_1068238] using wordTrace_append hprefix tailTrace_1068238
  have hstable : (prefixWord ++ tailWord_1068238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068238).length < 2 ^ (prefixWord ++ tailWord_1068238).sum := by decide
  have hdescent : baseEnd_1068238 < baseStart_1068238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068264 : List Nat := [2, 1, 4, 1, 2, 1, 2, 10]
def baseStart_1068264 : Nat := 118140960795 + 1068264 * 2 ^ 59
def prefixEnd_1068264 : Nat := 4983230072969 + 3 ^ 40 * 1068264 * 2
def baseEnd_1068264 : Nat := 20316033255359764662487

theorem tailTrace_1068264 : CollatzResearch.WordTrace tailWord_1068264 prefixEnd_1068264 20316033255359764662487 := by
  unfold tailWord_1068264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19481394500934723905561923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25975192667912965207415897 19481394500934723905561923)
  ·
    refine ⟨29222091751402085858342885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19481394500934723905561923 29222091751402085858342885)
    ·
      refine ⟨5479142203387891098439291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29222091751402085858342885 5479142203387891098439291)
      ·
        refine ⟨8218713305081836647658937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5479142203387891098439291 8218713305081836647658937)
        ·
          refine ⟨6164034978811377485744203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8218713305081836647658937 6164034978811377485744203)
          ·
            refine ⟨9246052468217066228616305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164034978811377485744203 9246052468217066228616305)
            ·
              refine ⟨6934539351162799671462229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9246052468217066228616305 6934539351162799671462229)
              ·
                refine ⟨20316033255359764662487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6934539351162799671462229 20316033255359764662487)
                ·
                  rfl

theorem cell23_1068264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 10].length) (baseStart_1068264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068264 prefixEnd_1068264 := by exact prefixLift 1068264
  have htrace : WordTrace (prefixWord ++ tailWord_1068264) baseStart_1068264 baseEnd_1068264 := by
    simpa [prefixWord, tailWord_1068264, baseEnd_1068264] using wordTrace_append hprefix tailTrace_1068264
  have hstable : (prefixWord ++ tailWord_1068264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068264).length < 2 ^ (prefixWord ++ tailWord_1068264).sum := by decide
  have hdescent : baseEnd_1068264 < baseStart_1068264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068271 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_1068271 : Nat := 118140960795 + 1068271 * 2 ^ 59
def prefixEnd_1068271 : Nat := 4983230072969 + 3 ^ 40 * 1068271 * 2
def baseEnd_1068271 : Nat := 548536492259295118499617

theorem tailTrace_1068271 : CollatzResearch.WordTrace tailWord_1068271 prefixEnd_1068271 548536492259295118499617 := by
  unfold tailWord_1068271
  simp only [CollatzResearch.WordTrace]
  refine ⟨38963044312844088006628667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25975362875229392004419111 38963044312844088006628667)
  ·
    refine ⟨58444566469266132009943001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38963044312844088006628667 58444566469266132009943001)
    ·
      refine ⟨43833424851949599007457251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58444566469266132009943001 43833424851949599007457251)
      ·
        refine ⟨65750137277924398511185877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43833424851949599007457251 65750137277924398511185877)
        ·
          refine ⟨1541018842451353090105919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65750137277924398511185877 1541018842451353090105919)
          ·
            refine ⟨2311528263677029635158879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541018842451353090105919 2311528263677029635158879)
            ·
              refine ⟨3467292395515544452738319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311528263677029635158879 3467292395515544452738319)
              ·
                refine ⟨5200938593273316679107479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467292395515544452738319 5200938593273316679107479)
                ·
                  refine ⟨7801407889909975018661219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200938593273316679107479 7801407889909975018661219)
                  ·
                    refine ⟨11702111834864962527991829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7801407889909975018661219 11702111834864962527991829)
                    ·
                      refine ⟨548536492259295118499617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11702111834864962527991829 548536492259295118499617)
                      ·
                        rfl

theorem cell23_1068271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_1068271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068271 prefixEnd_1068271 := by exact prefixLift 1068271
  have htrace : WordTrace (prefixWord ++ tailWord_1068271) baseStart_1068271 baseEnd_1068271 := by
    simpa [prefixWord, tailWord_1068271, baseEnd_1068271] using wordTrace_append hprefix tailTrace_1068271
  have hstable : (prefixWord ++ tailWord_1068271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068271).length < 2 ^ (prefixWord ++ tailWord_1068271).sum := by decide
  have hdescent : baseEnd_1068271 < baseStart_1068271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068325 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_1068325 : Nat := 118140960795 + 1068325 * 2 ^ 59
def prefixEnd_1068325 : Nat := 4983230072969 + 3 ^ 40 * 1068325 * 2
def baseEnd_1068325 : Nat := 548564220214637907224369

theorem tailTrace_1068325 : CollatzResearch.WordTrace tailWord_1068325 prefixEnd_1068325 548564220214637907224369 := by
  unfold tailWord_1068325
  simp only [CollatzResearch.WordTrace]
  refine ⟨38965013854648455229094429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25976675903098970152729619 38965013854648455229094429)
  ·
    refine ⟨14611880195493170710910411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38965013854648455229094429 14611880195493170710910411)
    ·
      refine ⟨21917820293239756066365617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14611880195493170710910411 21917820293239756066365617)
      ·
        refine ⟨16438365219929817049774213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21917820293239756066365617 16438365219929817049774213)
        ·
          refine ⟨3082193478736840696832665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16438365219929817049774213 3082193478736840696832665)
          ·
            refine ⟨2311645109052630522624499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3082193478736840696832665 2311645109052630522624499)
            ·
              refine ⟨3467467663578945783936749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311645109052630522624499 3467467663578945783936749)
              ·
                refine ⟨1300300373842104668976281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3467467663578945783936749 1300300373842104668976281)
                ·
                  refine ⟨975225280381578501732211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300300373842104668976281 975225280381578501732211)
                  ·
                    refine ⟨1462837920572367752598317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 975225280381578501732211 1462837920572367752598317)
                    ·
                      refine ⟨548564220214637907224369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1462837920572367752598317 548564220214637907224369)
                      ·
                        rfl

theorem cell23_1068325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_1068325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068325 prefixEnd_1068325 := by exact prefixLift 1068325
  have htrace : WordTrace (prefixWord ++ tailWord_1068325) baseStart_1068325 baseEnd_1068325 := by
    simpa [prefixWord, tailWord_1068325, baseEnd_1068325] using wordTrace_append hprefix tailTrace_1068325
  have hstable : (prefixWord ++ tailWord_1068325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068325).length < 2 ^ (prefixWord ++ tailWord_1068325).sum := by decide
  have hdescent : baseEnd_1068325 < baseStart_1068325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068342 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1068342 : Nat := 118140960795 + 1068342 * 2 ^ 59
def prefixEnd_1068342 : Nat := 4983230072969 + 3 ^ 40 * 1068342 * 2
def baseEnd_1068342 : Nat := 548572949385764340711791

theorem tailTrace_1068342 : CollatzResearch.WordTrace tailWord_1068342 prefixEnd_1068342 548572949385764340711791 := by
  unfold tailWord_1068342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435352118474179195778955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25977089263724578088308853 2435352118474179195778955)
  ·
    refine ⟨3653028177711268793668433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2435352118474179195778955 3653028177711268793668433)
    ·
      refine ⟨2739771133283451595251325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3653028177711268793668433 2739771133283451595251325)
      ·
        refine ⟨1027414174981294348219247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2739771133283451595251325 1027414174981294348219247)
        ·
          refine ⟨1541121262471941522328871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027414174981294348219247 1541121262471941522328871)
          ·
            refine ⟨2311681893707912283493307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541121262471941522328871 2311681893707912283493307)
            ·
              refine ⟨3467522840561868425239961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311681893707912283493307 3467522840561868425239961)
              ·
                refine ⟨2600642130421401318929971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3467522840561868425239961 2600642130421401318929971)
                ·
                  refine ⟨3900963195632101978394957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2600642130421401318929971 3900963195632101978394957)
                  ·
                    refine ⟨1462861198362038241898109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3900963195632101978394957 1462861198362038241898109)
                    ·
                      refine ⟨548572949385764340711791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1462861198362038241898109 548572949385764340711791)
                      ·
                        rfl

theorem cell23_1068342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1068342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068342 prefixEnd_1068342 := by exact prefixLift 1068342
  have htrace : WordTrace (prefixWord ++ tailWord_1068342) baseStart_1068342 baseEnd_1068342 := by
    simpa [prefixWord, tailWord_1068342, baseEnd_1068342] using wordTrace_append hprefix tailTrace_1068342
  have hstable : (prefixWord ++ tailWord_1068342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068342).length < 2 ^ (prefixWord ++ tailWord_1068342).sum := by decide
  have hdescent : baseEnd_1068342 < baseStart_1068342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068348 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_1068348 : Nat := 118140960795 + 1068348 * 2 ^ 59
def prefixEnd_1068348 : Nat := 4983230072969 + 3 ^ 40 * 1068348 * 2
def baseEnd_1068348 : Nat := 548576030269691317236763

theorem tailTrace_1068348 : CollatzResearch.WordTrace tailWord_1068348 prefixEnd_1068348 548576030269691317236763 := by
  unfold tailWord_1068348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19482926366782565078590849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25977235155710086771454465 19482926366782565078590849)
  ·
    refine ⟨14612194775086923808943137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19482926366782565078590849 14612194775086923808943137)
    ·
      refine ⟨10959146081315192856707353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14612194775086923808943137 10959146081315192856707353)
      ·
        refine ⟨8219359560986394642530515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10959146081315192856707353 8219359560986394642530515)
        ·
          refine ⟨12329039341479591963795773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219359560986394642530515 12329039341479591963795773)
          ·
            refine ⟨4623389753054846986423415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12329039341479591963795773 4623389753054846986423415)
            ·
              refine ⟨6935084629582270479635123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623389753054846986423415 6935084629582270479635123)
              ·
                refine ⟨10402626944373405719452685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6935084629582270479635123 10402626944373405719452685)
                ·
                  refine ⟨3900985104140027144794757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10402626944373405719452685 3900985104140027144794757)
                  ·
                    refine ⟨731434707026255089649017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3900985104140027144794757 731434707026255089649017)
                    ·
                      refine ⟨548576030269691317236763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731434707026255089649017 548576030269691317236763)
                      ·
                        rfl

theorem cell23_1068348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_1068348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068348 prefixEnd_1068348 := by exact prefixLift 1068348
  have htrace : WordTrace (prefixWord ++ tailWord_1068348) baseStart_1068348 baseEnd_1068348 := by
    simpa [prefixWord, tailWord_1068348, baseEnd_1068348] using wordTrace_append hprefix tailTrace_1068348
  have hstable : (prefixWord ++ tailWord_1068348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068348).length < 2 ^ (prefixWord ++ tailWord_1068348).sum := by decide
  have hdescent : baseEnd_1068348 < baseStart_1068348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068351 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1068351 : Nat := 118140960795 + 1068351 * 2 ^ 59
def prefixEnd_1068351 : Nat := 4983230072969 + 3 ^ 40 * 1068351 * 2
def baseEnd_1068351 : Nat := 548577570711654805499249

theorem tailTrace_1068351 : CollatzResearch.WordTrace tailWord_1068351 prefixEnd_1068351 548577570711654805499249 := by
  unfold tailWord_1068351
  simp only [CollatzResearch.WordTrace]
  refine ⟨38965962152554261669540907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25977308101702841113027271 38965962152554261669540907)
  ·
    refine ⟨58448943228831392504311361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38965962152554261669540907 58448943228831392504311361)
    ·
      refine ⟨43836707421623544378233521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58448943228831392504311361 43836707421623544378233521)
      ·
        refine ⟨32877530566217658283675141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43836707421623544378233521 32877530566217658283675141)
        ·
          refine ⟨6164536981165810928189089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32877530566217658283675141 6164536981165810928189089)
          ·
            refine ⟨4623402735874358196141817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6164536981165810928189089 4623402735874358196141817)
            ·
              refine ⟨3467552051905768647106363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4623402735874358196141817 3467552051905768647106363)
              ·
                refine ⟨5201328077858652970659545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467552051905768647106363 5201328077858652970659545)
                ·
                  refine ⟨3900996058393989727994659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5201328077858652970659545 3900996058393989727994659)
                  ·
                    refine ⟨5851494087590984591991989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3900996058393989727994659 5851494087590984591991989)
                    ·
                      refine ⟨548577570711654805499249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5851494087590984591991989 548577570711654805499249)
                      ·
                        rfl

theorem cell23_1068351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1068351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068351 prefixEnd_1068351 := by exact prefixLift 1068351
  have htrace : WordTrace (prefixWord ++ tailWord_1068351) baseStart_1068351 baseEnd_1068351 := by
    simpa [prefixWord, tailWord_1068351, baseEnd_1068351] using wordTrace_append hprefix tailTrace_1068351
  have hstable : (prefixWord ++ tailWord_1068351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068351).length < 2 ^ (prefixWord ++ tailWord_1068351).sum := by decide
  have hdescent : baseEnd_1068351 < baseStart_1068351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068448 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 3, 4]
def baseStart_1068448 : Nat := 118140960795 + 1068448 * 2 ^ 59
def prefixEnd_1068448 : Nat := 4983230072969 + 3 ^ 40 * 1068448 * 2
def baseEnd_1068448 : Nat := 182875792778380308662101

theorem tailTrace_1068448 : CollatzResearch.WordTrace tailWord_1068448 prefixEnd_1068448 182875792778380308662101 := by
  unfold tailWord_1068448
  simp only [CollatzResearch.WordTrace]
  refine ⟨19484750016601423617910999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25979666688801898157214665 19484750016601423617910999)
  ·
    refine ⟨29227125024902135426866499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19484750016601423617910999 29227125024902135426866499)
    ·
      refine ⟨43840687537353203140299749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29227125024902135426866499 43840687537353203140299749)
      ·
        refine ⟨8220128913253725588806203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43840687537353203140299749 8220128913253725588806203)
        ·
          refine ⟨12330193369880588383209305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8220128913253725588806203 12330193369880588383209305)
          ·
            refine ⟨9247645027410441287406979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12330193369880588383209305 9247645027410441287406979)
            ·
              refine ⟨13871467541115661931110469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9247645027410441287406979 13871467541115661931110469)
              ·
                refine ⟨2600900163959186612083213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13871467541115661931110469 2600900163959186612083213)
                ·
                  refine ⟨975337561484694979531205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2600900163959186612083213 975337561484694979531205)
                  ·
                    refine ⟨182875792778380308662101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 975337561484694979531205 182875792778380308662101)
                    ·
                      rfl

theorem cell23_1068448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_1068448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068448 prefixEnd_1068448 := by exact prefixLift 1068448
  have htrace : WordTrace (prefixWord ++ tailWord_1068448) baseStart_1068448 baseEnd_1068448 := by
    simpa [prefixWord, tailWord_1068448, baseEnd_1068448] using wordTrace_append hprefix tailTrace_1068448
  have hstable : (prefixWord ++ tailWord_1068448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068448).length < 2 ^ (prefixWord ++ tailWord_1068448).sum := by decide
  have hdescent : baseEnd_1068448 < baseStart_1068448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068451 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1068451 : Nat := 118140960795 + 1068451 * 2 ^ 59
def prefixEnd_1068451 : Nat := 4983230072969 + 3 ^ 40 * 1068451 * 2
def baseEnd_1068451 : Nat := 548628918777104414248789

theorem tailTrace_1068451 : CollatzResearch.WordTrace tailWord_1068451 prefixEnd_1068451 548628918777104414248789 := by
  unfold tailWord_1068451
  simp only [CollatzResearch.WordTrace]
  refine ⟨38969609452191978748181207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25979739634794652498787471 38969609452191978748181207)
  ·
    refine ⟨58454414178287968122271811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38969609452191978748181207 58454414178287968122271811)
    ·
      refine ⟨87681621267431952183407717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58454414178287968122271811 87681621267431952183407717)
      ·
        refine ⟨16440303987643491034388947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87681621267431952183407717 16440303987643491034388947)
        ·
          refine ⟨24660455981465236551583421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16440303987643491034388947 24660455981465236551583421)
          ·
            refine ⟨9247670993049463706843783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24660455981465236551583421 9247670993049463706843783)
            ·
              refine ⟨13871506489574195560265675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9247670993049463706843783 13871506489574195560265675)
              ·
                refine ⟨20807259734361293340398513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13871506489574195560265675 20807259734361293340398513)
                ·
                  refine ⟨15605444800770970005298885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20807259734361293340398513 15605444800770970005298885)
                  ·
                    refine ⟨2926020900144556875993541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15605444800770970005298885 2926020900144556875993541)
                    ·
                      refine ⟨548628918777104414248789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2926020900144556875993541 548628918777104414248789)
                      ·
                        rfl

theorem cell23_1068451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1068451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068451 prefixEnd_1068451 := by exact prefixLift 1068451
  have htrace : WordTrace (prefixWord ++ tailWord_1068451) baseStart_1068451 baseEnd_1068451 := by
    simpa [prefixWord, tailWord_1068451, baseEnd_1068451] using wordTrace_append hprefix tailTrace_1068451
  have hstable : (prefixWord ++ tailWord_1068451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068451).length < 2 ^ (prefixWord ++ tailWord_1068451).sum := by decide
  have hdescent : baseEnd_1068451 < baseStart_1068451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068478 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1068478 : Nat := 118140960795 + 1068478 * 2 ^ 59
def prefixEnd_1068478 : Nat := 4983230072969 + 3 ^ 40 * 1068478 * 2
def baseEnd_1068478 : Nat := 60960309194975089845685

theorem tailTrace_1068478 : CollatzResearch.WordTrace tailWord_1068478 prefixEnd_1068478 60960309194975089845685 := by
  unfold tailWord_1068478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4871324277886770294926761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25980396148729441572942725 4871324277886770294926761)
  ·
    refine ⟨3653493208415077721195071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4871324277886770294926761 3653493208415077721195071)
    ·
      refine ⟨5480239812622616581792607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653493208415077721195071 5480239812622616581792607)
      ·
        refine ⟨8220359718933924872688911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5480239812622616581792607 8220359718933924872688911)
        ·
          refine ⟨12330539578400887309033367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8220359718933924872688911 12330539578400887309033367)
          ·
            refine ⟨18495809367601330963550051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12330539578400887309033367 18495809367601330963550051)
            ·
              refine ⟨27743714051401996445325077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18495809367601330963550051 27743714051401996445325077)
              ·
                refine ⟨1300486596159468583374613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27743714051401996445325077 1300486596159468583374613)
                ·
                  refine ⟨60960309194975089845685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1300486596159468583374613 60960309194975089845685)
                  ·
                    rfl

theorem cell23_1068478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1068478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068478 prefixEnd_1068478 := by exact prefixLift 1068478
  have htrace : WordTrace (prefixWord ++ tailWord_1068478) baseStart_1068478 baseEnd_1068478 := by
    simpa [prefixWord, tailWord_1068478, baseEnd_1068478] using wordTrace_append hprefix tailTrace_1068478
  have hstable : (prefixWord ++ tailWord_1068478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068478).length < 2 ^ (prefixWord ++ tailWord_1068478).sum := by decide
  have hdescent : baseEnd_1068478 < baseStart_1068478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068555 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 1, 6]
def baseStart_1068555 : Nat := 118140960795 + 1068555 * 2 ^ 59
def prefixEnd_1068555 : Nat := 4983230072969 + 3 ^ 40 * 1068555 * 2
def baseEnd_1068555 : Nat := 182894106921724002449437

theorem tailTrace_1068555 : CollatzResearch.WordTrace tailWord_1068555 prefixEnd_1068555 182894106921724002449437 := by
  unfold tailWord_1068555
  simp only [CollatzResearch.WordTrace]
  refine ⟨38973402643815204509967119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25982268429210136339978079 38973402643815204509967119)
  ·
    refine ⟨58460103965722806764950679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38973402643815204509967119 58460103965722806764950679)
    ·
      refine ⟨87690155948584210147426019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58460103965722806764950679 87690155948584210147426019)
      ·
        refine ⟨131535233922876315221139029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87690155948584210147426019 131535233922876315221139029)
        ·
          refine ⟨1541428522533706818997723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 131535233922876315221139029 1541428522533706818997723)
          ·
            refine ⟨2312142783800560228496585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541428522533706818997723 2312142783800560228496585)
            ·
              refine ⟨1734107087850420171372439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312142783800560228496585 1734107087850420171372439)
              ·
                refine ⟨2601160631775630257058659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734107087850420171372439 2601160631775630257058659)
                ·
                  refine ⟨3901740947663445385587989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601160631775630257058659 3901740947663445385587989)
                  ·
                    refine ⟨182894106921724002449437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3901740947663445385587989 182894106921724002449437)
                    ·
                      rfl

theorem cell23_1068555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 6].length) (baseStart_1068555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068555 prefixEnd_1068555 := by exact prefixLift 1068555
  have htrace : WordTrace (prefixWord ++ tailWord_1068555) baseStart_1068555 baseEnd_1068555 := by
    simpa [prefixWord, tailWord_1068555, baseEnd_1068555] using wordTrace_append hprefix tailTrace_1068555
  have hstable : (prefixWord ++ tailWord_1068555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068555).length < 2 ^ (prefixWord ++ tailWord_1068555).sum := by decide
  have hdescent : baseEnd_1068555 < baseStart_1068555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068565 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1068565 : Nat := 118140960795 + 1068565 * 2 ^ 59
def prefixEnd_1068565 : Nat := 4983230072969 + 3 ^ 40 * 1068565 * 2
def baseEnd_1068565 : Nat := 548687455571716968223265

theorem tailTrace_1068565 : CollatzResearch.WordTrace tailWord_1068565 prefixEnd_1068565 548687455571716968223265 := by
  unfold tailWord_1068565
  simp only [CollatzResearch.WordTrace]
  refine ⟨38973767373778976217831149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25982511582519317478554099 38973767373778976217831149)
  ·
    refine ⟨14615162765167116081686681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38973767373778976217831149 14615162765167116081686681)
    ·
      refine ⟨10961372073875337061265011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14615162765167116081686681 10961372073875337061265011)
      ·
        refine ⟨16442058110813005591897517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10961372073875337061265011 16442058110813005591897517)
        ·
          refine ⟨6165771791554877096961569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16442058110813005591897517 6165771791554877096961569)
          ·
            refine ⟨4624328843666157822721177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6165771791554877096961569 4624328843666157822721177)
            ·
              refine ⟨3468246632749618367040883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4624328843666157822721177 3468246632749618367040883)
              ·
                refine ⟨5202369949124427550561325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3468246632749618367040883 5202369949124427550561325)
                ·
                  refine ⟨1950888730921660331460497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5202369949124427550561325 1950888730921660331460497)
                  ·
                    refine ⟨1463166548191245248595373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1950888730921660331460497 1463166548191245248595373)
                    ·
                      refine ⟨548687455571716968223265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1463166548191245248595373 548687455571716968223265)
                      ·
                        rfl

theorem cell23_1068565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1068565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068565 prefixEnd_1068565 := by exact prefixLift 1068565
  have htrace : WordTrace (prefixWord ++ tailWord_1068565) baseStart_1068565 baseEnd_1068565 := by
    simpa [prefixWord, tailWord_1068565, baseEnd_1068565] using wordTrace_append hprefix tailTrace_1068565
  have hstable : (prefixWord ++ tailWord_1068565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068565).length < 2 ^ (prefixWord ++ tailWord_1068565).sum := by decide
  have hdescent : baseEnd_1068565 < baseStart_1068565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068579 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 1, 1, 4]
def baseStart_1068579 : Nat := 118140960795 + 1068579 * 2 ^ 59
def prefixEnd_1068579 : Nat := 4983230072969 + 3 ^ 40 * 1068579 * 2
def baseEnd_1068579 : Nat := 548694644300879913448201

theorem tailTrace_1068579 : CollatzResearch.WordTrace tailWord_1068579 prefixEnd_1068579 548694644300879913448201 := by
  unfold tailWord_1068579
  simp only [CollatzResearch.WordTrace]
  refine ⟨38974277995728256608840791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25982851997152171072560527 38974277995728256608840791)
  ·
    refine ⟨58461416993592384913261187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38974277995728256608840791 58461416993592384913261187)
    ·
      refine ⟨87692125490388577369891781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58461416993592384913261187 87692125490388577369891781)
      ·
        refine ⟨16442273529447858256854709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87692125490388577369891781 16442273529447858256854709)
        ·
          refine ⟨1541463143385736711580129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16442273529447858256854709 1541463143385736711580129)
          ·
            refine ⟨1156097357539302533685097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541463143385736711580129 1156097357539302533685097)
            ·
              refine ⟨867073018154476900263823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156097357539302533685097 867073018154476900263823)
              ·
                refine ⟨1300609527231715350395735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867073018154476900263823 1300609527231715350395735)
                ·
                  refine ⟨1950914290847573025593603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300609527231715350395735 1950914290847573025593603)
                  ·
                    refine ⟨2926371436271359538390405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1950914290847573025593603 2926371436271359538390405)
                    ·
                      refine ⟨548694644300879913448201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2926371436271359538390405 548694644300879913448201)
                      ·
                        rfl

theorem cell23_1068579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_1068579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068579 prefixEnd_1068579 := by exact prefixLift 1068579
  have htrace : WordTrace (prefixWord ++ tailWord_1068579) baseStart_1068579 baseEnd_1068579 := by
    simpa [prefixWord, tailWord_1068579, baseEnd_1068579] using wordTrace_append hprefix tailTrace_1068579
  have hstable : (prefixWord ++ tailWord_1068579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068579).length < 2 ^ (prefixWord ++ tailWord_1068579).sum := by decide
  have hdescent : baseEnd_1068579 < baseStart_1068579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068688 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_1068688 : Nat := 118140960795 + 1068688 * 2 ^ 59
def prefixEnd_1068688 : Nat := 4983230072969 + 3 ^ 40 * 1068688 * 2
def baseEnd_1068688 : Nat := 182916871230739995661733

theorem tailTrace_1068688 : CollatzResearch.WordTrace tailWord_1068688 prefixEnd_1068688 182916871230739995661733 := by
  unfold tailWord_1068688
  simp only [CollatzResearch.WordTrace]
  refine ⟨19489126776166684112279359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25985502368222245483039145 19489126776166684112279359)
  ·
    refine ⟨29233690164250026168419039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19489126776166684112279359 29233690164250026168419039)
    ·
      refine ⟨43850535246375039252628559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29233690164250026168419039 43850535246375039252628559)
      ·
        refine ⟨65775802869562558878942839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43850535246375039252628559 65775802869562558878942839)
        ·
          refine ⟨98663704304343838318414259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65775802869562558878942839 98663704304343838318414259)
          ·
            refine ⟨147995556456515757477621389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98663704304343838318414259 147995556456515757477621389)
            ·
              refine ⟨55498333671193409054108021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147995556456515757477621389 55498333671193409054108021)
              ·
                refine ⟨5202968781674382098822627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55498333671193409054108021 5202968781674382098822627)
                ·
                  refine ⟨7804453172511573148233941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5202968781674382098822627 7804453172511573148233941)
                  ·
                    refine ⟨182916871230739995661733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7804453172511573148233941 182916871230739995661733)
                    ·
                      rfl

theorem cell23_1068688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_1068688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068688 prefixEnd_1068688 := by exact prefixLift 1068688
  have htrace : WordTrace (prefixWord ++ tailWord_1068688) baseStart_1068688 baseEnd_1068688 := by
    simpa [prefixWord, tailWord_1068688, baseEnd_1068688] using wordTrace_append hprefix tailTrace_1068688
  have hstable : (prefixWord ++ tailWord_1068688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068688).length < 2 ^ (prefixWord ++ tailWord_1068688).sum := by decide
  have hdescent : baseEnd_1068688 < baseStart_1068688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068703 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1068703 : Nat := 118140960795 + 1068703 * 2 ^ 59
def prefixEnd_1068703 : Nat := 4983230072969 + 3 ^ 40 * 1068703 * 2
def baseEnd_1068703 : Nat := 548758315902037428297631

theorem tailTrace_1068703 : CollatzResearch.WordTrace tailWord_1068703 prefixEnd_1068703 548758315902037428297631 := by
  unfold tailWord_1068703
  simp only [CollatzResearch.WordTrace]
  refine ⟨38978800647279025786354763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25985867098186017190903175 38978800647279025786354763)
  ·
    refine ⟨58468200970918538679532145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38978800647279025786354763 58468200970918538679532145)
    ·
      refine ⟨43851150728188904009649109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58468200970918538679532145 43851150728188904009649109)
      ·
        refine ⟨1027761345191927437726151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43851150728188904009649109 1027761345191927437726151)
        ·
          refine ⟨1541642017787891156589227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027761345191927437726151 1541642017787891156589227)
          ·
            refine ⟨2312463026681836734883841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541642017787891156589227 2312463026681836734883841)
            ·
              refine ⟨1734347270011377551162881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312463026681836734883841 1734347270011377551162881)
              ·
                refine ⟨1300760452508533163372161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1734347270011377551162881 1300760452508533163372161)
                ·
                  refine ⟨975570339381399872529121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300760452508533163372161 975570339381399872529121)
                  ·
                    refine ⟨731677754536049904396841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 975570339381399872529121 731677754536049904396841)
                    ·
                      refine ⟨548758315902037428297631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731677754536049904396841 548758315902037428297631)
                      ·
                        rfl

theorem cell23_1068703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1068703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068703 prefixEnd_1068703 := by exact prefixLift 1068703
  have htrace : WordTrace (prefixWord ++ tailWord_1068703) baseStart_1068703 baseEnd_1068703 := by
    simpa [prefixWord, tailWord_1068703, baseEnd_1068703] using wordTrace_append hprefix tailTrace_1068703
  have hstable : (prefixWord ++ tailWord_1068703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068703).length < 2 ^ (prefixWord ++ tailWord_1068703).sum := by decide
  have hdescent : baseEnd_1068703 < baseStart_1068703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068769 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1068769 : Nat := 118140960795 + 1068769 * 2 ^ 59
def prefixEnd_1068769 : Nat := 4983230072969 + 3 ^ 40 * 1068769 * 2
def baseEnd_1068769 : Nat := 182930735208411390024109

theorem tailTrace_1068769 : CollatzResearch.WordTrace tailWord_1068769 prefixEnd_1068769 182930735208411390024109 := by
  unfold tailWord_1068769
  simp only [CollatzResearch.WordTrace]
  refine ⟨38981207865039919058257361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25987471910026612705504907 38981207865039919058257361)
  ·
    refine ⟨29235905898779939293693021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38981207865039919058257361 29235905898779939293693021)
    ·
      refine ⟨10963464712042477235134883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29235905898779939293693021 10963464712042477235134883)
      ·
        refine ⟨16445197068063715852702325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10963464712042477235134883 16445197068063715852702325)
        ·
          refine ⟨1541737225130973361190843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16445197068063715852702325 1541737225130973361190843)
          ·
            refine ⟨2312605837696460041786265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541737225130973361190843 2312605837696460041786265)
            ·
              refine ⟨1734454378272345031339699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312605837696460041786265 1734454378272345031339699)
              ·
                refine ⟨2601681567408517547009549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734454378272345031339699 2601681567408517547009549)
                ·
                  refine ⟨975630587778194080128581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2601681567408517547009549 975630587778194080128581)
                  ·
                    refine ⟨182930735208411390024109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 975630587778194080128581 182930735208411390024109)
                    ·
                      rfl

theorem cell23_1068769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1068769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068769 prefixEnd_1068769 := by exact prefixLift 1068769
  have htrace : WordTrace (prefixWord ++ tailWord_1068769) baseStart_1068769 baseEnd_1068769 := by
    simpa [prefixWord, tailWord_1068769, baseEnd_1068769] using wordTrace_append hprefix tailTrace_1068769
  have hstable : (prefixWord ++ tailWord_1068769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068769).length < 2 ^ (prefixWord ++ tailWord_1068769).sum := by decide
  have hdescent : baseEnd_1068769 < baseStart_1068769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068792 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_1068792 : Nat := 118140960795 + 1068792 * 2 ^ 59
def prefixEnd_1068792 : Nat := 4983230072969 + 3 ^ 40 * 1068792 * 2
def baseEnd_1068792 : Nat := 548804015680287580084721

theorem tailTrace_1068792 : CollatzResearch.WordTrace tailWord_1068792 prefixEnd_1068792 548804015680287580084721 := by
  unfold tailWord_1068792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491023371978296993172315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25988031162637729324229753 19491023371978296993172315)
  ·
    refine ⟨29236535057967445489758473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19491023371978296993172315 29236535057967445489758473)
    ·
      refine ⟨21927401293475584117318855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29236535057967445489758473 21927401293475584117318855)
      ·
        refine ⟨32891101940213376175978283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21927401293475584117318855 32891101940213376175978283)
        ·
          refine ⟨49336652910320064263967425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32891101940213376175978283 49336652910320064263967425)
          ·
            refine ⟨37002489682740048197975569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49336652910320064263967425 37002489682740048197975569)
            ·
              refine ⟨27751867262055036148481677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37002489682740048197975569 27751867262055036148481677)
              ·
                refine ⟨10406950223270638555680629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27751867262055036148481677 10406950223270638555680629)
                ·
                  refine ⟨975651583431622364595059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10406950223270638555680629 975651583431622364595059)
                  ·
                    refine ⟨1463477375147433546892589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 975651583431622364595059 1463477375147433546892589)
                    ·
                      refine ⟨548804015680287580084721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1463477375147433546892589 548804015680287580084721)
                      ·
                        rfl

theorem cell23_1068792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_1068792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068792 prefixEnd_1068792 := by exact prefixLift 1068792
  have htrace : WordTrace (prefixWord ++ tailWord_1068792) baseStart_1068792 baseEnd_1068792 := by
    simpa [prefixWord, tailWord_1068792, baseEnd_1068792] using wordTrace_append hprefix tailTrace_1068792
  have hstable : (prefixWord ++ tailWord_1068792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068792).length < 2 ^ (prefixWord ++ tailWord_1068792).sum := by decide
  have hdescent : baseEnd_1068792 < baseStart_1068792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068812 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_1068812 : Nat := 118140960795 + 1068812 * 2 ^ 59
def prefixEnd_1068812 : Nat := 4983230072969 + 3 ^ 40 * 1068812 * 2
def baseEnd_1068812 : Nat := 182938095097792500611543

theorem tailTrace_1068812 : CollatzResearch.WordTrace tailWord_1068812 prefixEnd_1068812 182938095097792500611543 := by
  unfold tailWord_1068812
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491388101942068701036345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25988517469256091601381793 19491388101942068701036345)
  ·
    refine ⟨14618541076456551525777259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19491388101942068701036345 14618541076456551525777259)
    ·
      refine ⟨21927811614684827288665889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14618541076456551525777259 21927811614684827288665889)
      ·
        refine ⟨16445858711013620466499417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21927811614684827288665889 16445858711013620466499417)
        ·
          refine ⟨12334394033260215349874563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16445858711013620466499417 12334394033260215349874563)
          ·
            refine ⟨18501591049890323024811845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12334394033260215349874563 18501591049890323024811845)
            ·
              refine ⟨3469048321854435567152221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18501591049890323024811845 3469048321854435567152221)
              ·
                refine ⟨1300893120695413337682083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3469048321854435567152221 1300893120695413337682083)
                ·
                  refine ⟨1951339681043120006523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300893120695413337682083 1951339681043120006523125)
                  ·
                    refine ⟨182938095097792500611543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1951339681043120006523125 182938095097792500611543)
                    ·
                      rfl

theorem cell23_1068812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_1068812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068812 prefixEnd_1068812 := by exact prefixLift 1068812
  have htrace : WordTrace (prefixWord ++ tailWord_1068812) baseStart_1068812 baseEnd_1068812 := by
    simpa [prefixWord, tailWord_1068812, baseEnd_1068812] using wordTrace_append hprefix tailTrace_1068812
  have hstable : (prefixWord ++ tailWord_1068812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068812).length < 2 ^ (prefixWord ++ tailWord_1068812).sum := by decide
  have hdescent : baseEnd_1068812 < baseStart_1068812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068820 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1068820 : Nat := 118140960795 + 1068820 * 2 ^ 59
def prefixEnd_1068820 : Nat := 4983230072969 + 3 ^ 40 * 1068820 * 2
def baseEnd_1068820 : Nat := 182939464379537823511531

theorem tailTrace_1068820 : CollatzResearch.WordTrace tailWord_1068820 prefixEnd_1068820 182939464379537823511531 := by
  unfold tailWord_1068820
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491533993927577384181957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25988711991903436512242609 19491533993927577384181957)
  ·
    refine ⟨3654662623861420759534117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19491533993927577384181957 3654662623861420759534117)
    ·
      refine ⟨685249241974016392412647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3654662623861420759534117 685249241974016392412647)
      ·
        refine ⟨1027873862961024588618971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685249241974016392412647 1027873862961024588618971)
        ·
          refine ⟨1541810794441536882928457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027873862961024588618971 1541810794441536882928457)
          ·
            refine ⟨1156358095831152662196343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541810794441536882928457 1156358095831152662196343)
            ·
              refine ⟨1734537143746728993294515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156358095831152662196343 1734537143746728993294515)
              ·
                refine ⟨2601805715620093489941773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734537143746728993294515 2601805715620093489941773)
                ·
                  refine ⟨975677143357535058728165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2601805715620093489941773 975677143357535058728165)
                  ·
                    refine ⟨182939464379537823511531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 975677143357535058728165 182939464379537823511531)
                    ·
                      rfl

theorem cell23_1068820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1068820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068820 prefixEnd_1068820 := by exact prefixLift 1068820
  have htrace : WordTrace (prefixWord ++ tailWord_1068820) baseStart_1068820 baseEnd_1068820 := by
    simpa [prefixWord, tailWord_1068820, baseEnd_1068820] using wordTrace_append hprefix tailTrace_1068820
  have hstable : (prefixWord ++ tailWord_1068820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068820).length < 2 ^ (prefixWord ++ tailWord_1068820).sum := by decide
  have hdescent : baseEnd_1068820 < baseStart_1068820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068826 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1068826 : Nat := 118140960795 + 1068826 * 2 ^ 59
def prefixEnd_1068826 : Nat := 4983230072969 + 3 ^ 40 * 1068826 * 2
def baseEnd_1068826 : Nat := 548821474022540447059565

theorem tailTrace_1068826 : CollatzResearch.WordTrace tailWord_1068826 prefixEnd_1068826 548821474022540447059565 := by
  unfold tailWord_1068826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745821706458354448270583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25988857883888945195388221 9745821706458354448270583)
  ·
    refine ⟨14618732559687531672405875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9745821706458354448270583 14618732559687531672405875)
    ·
      refine ⟨21928098839531297508608813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14618732559687531672405875 21928098839531297508608813)
      ·
        refine ⟨8223037064824236565728305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21928098839531297508608813 8223037064824236565728305)
        ·
          refine ⟨6167277798618177424296229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8223037064824236565728305 6167277798618177424296229)
          ·
            refine ⟨1156364587240908267055543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6167277798618177424296229 1156364587240908267055543)
            ·
              refine ⟨1734546880861362400583315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156364587240908267055543 1734546880861362400583315)
              ·
                refine ⟨2601820321292043600874973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734546880861362400583315 2601820321292043600874973)
                ·
                  refine ⟨975682620484516350328115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2601820321292043600874973 975682620484516350328115)
                  ·
                    refine ⟨1463523930726774525492173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 975682620484516350328115 1463523930726774525492173)
                    ·
                      refine ⟨548821474022540447059565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1463523930726774525492173 548821474022540447059565)
                      ·
                        rfl

theorem cell23_1068826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1068826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068826 prefixEnd_1068826 := by exact prefixLift 1068826
  have htrace : WordTrace (prefixWord ++ tailWord_1068826) baseStart_1068826 baseEnd_1068826 := by
    simpa [prefixWord, tailWord_1068826, baseEnd_1068826] using wordTrace_append hprefix tailTrace_1068826
  have hstable : (prefixWord ++ tailWord_1068826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068826).length < 2 ^ (prefixWord ++ tailWord_1068826).sum := by decide
  have hdescent : baseEnd_1068826 < baseStart_1068826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068832 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1068832 : Nat := 118140960795 + 1068832 * 2 ^ 59
def prefixEnd_1068832 : Nat := 4983230072969 + 3 ^ 40 * 1068832 * 2
def baseEnd_1068832 : Nat := 548824554906467423584537

theorem tailTrace_1068832 : CollatzResearch.WordTrace tailWord_1068832 prefixEnd_1068832 548824554906467423584537 := by
  unfold tailWord_1068832
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491752831905840408900375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25989003775874453878533833 19491752831905840408900375)
  ·
    refine ⟨29237629247858760613350563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19491752831905840408900375 29237629247858760613350563)
    ·
      refine ⟨43856443871788140920025845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29237629247858760613350563 43856443871788140920025845)
      ·
        refine ⟨4111541612980138211252423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43856443871788140920025845 4111541612980138211252423)
        ·
          refine ⟨6167312419470207316878635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4111541612980138211252423 6167312419470207316878635)
          ·
            refine ⟨9250968629205310975317953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6167312419470207316878635 9250968629205310975317953)
            ·
              refine ⟨6938226471903983231488465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9250968629205310975317953 6938226471903983231488465)
              ·
                refine ⟨5203669853927987423616349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6938226471903983231488465 5203669853927987423616349)
                ·
                  refine ⟨1951376195222995283856131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5203669853927987423616349 1951376195222995283856131)
                  ·
                    refine ⟨2927064292834492925784197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1951376195222995283856131 2927064292834492925784197)
                    ·
                      refine ⟨548824554906467423584537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2927064292834492925784197 548824554906467423584537)
                      ·
                        rfl

theorem cell23_1068832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1068832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068832 prefixEnd_1068832 := by exact prefixLift 1068832
  have htrace : WordTrace (prefixWord ++ tailWord_1068832) baseStart_1068832 baseEnd_1068832 := by
    simpa [prefixWord, tailWord_1068832, baseEnd_1068832] using wordTrace_append hprefix tailTrace_1068832
  have hstable : (prefixWord ++ tailWord_1068832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068832).length < 2 ^ (prefixWord ++ tailWord_1068832).sum := by decide
  have hdescent : baseEnd_1068832 < baseStart_1068832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068849 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_1068849 : Nat := 118140960795 + 1068849 * 2 ^ 59
def prefixEnd_1068849 : Nat := 4983230072969 + 3 ^ 40 * 1068849 * 2
def baseEnd_1068849 : Nat := 548833284077593857071959

theorem tailTrace_1068849 : CollatzResearch.WordTrace tailWord_1068849 prefixEnd_1068849 548833284077593857071959 := by
  unfold tailWord_1068849
  simp only [CollatzResearch.WordTrace]
  refine ⟨38984125704750092721169601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25989417136500061814113067 38984125704750092721169601)
  ·
    refine ⟨29238094278562569540877201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38984125704750092721169601 29238094278562569540877201)
    ·
      refine ⟨21928570708921927155657901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29238094278562569540877201 21928570708921927155657901)
      ·
        refine ⟨8223214015845722683371713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21928570708921927155657901 8223214015845722683371713)
        ·
          refine ⟨6167410511884292012528785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8223214015845722683371713 6167410511884292012528785)
          ·
            refine ⟨4625557883913219009396589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6167410511884292012528785 4625557883913219009396589)
            ·
              refine ⟨1734584206467457128523721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4625557883913219009396589 1734584206467457128523721)
              ·
                refine ⟨1300938154850592846392791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1734584206467457128523721 1300938154850592846392791)
                ·
                  refine ⟨1951407232275889269589187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300938154850592846392791 1951407232275889269589187)
                  ·
                    refine ⟨2927110848413833904383781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1951407232275889269589187 2927110848413833904383781)
                    ·
                      refine ⟨548833284077593857071959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2927110848413833904383781 548833284077593857071959)
                      ·
                        rfl

theorem cell23_1068849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_1068849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068849 prefixEnd_1068849 := by exact prefixLift 1068849
  have htrace : WordTrace (prefixWord ++ tailWord_1068849) baseStart_1068849 baseEnd_1068849 := by
    simpa [prefixWord, tailWord_1068849, baseEnd_1068849] using wordTrace_append hprefix tailTrace_1068849
  have hstable : (prefixWord ++ tailWord_1068849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068849).length < 2 ^ (prefixWord ++ tailWord_1068849).sum := by decide
  have hdescent : baseEnd_1068849 < baseStart_1068849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068876 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_1068876 : Nat := 118140960795 + 1068876 * 2 ^ 59
def prefixEnd_1068876 : Nat := 4983230072969 + 3 ^ 40 * 1068876 * 2
def baseEnd_1068876 : Nat := 182949049351755083811445

theorem tailTrace_1068876 : CollatzResearch.WordTrace tailWord_1068876 prefixEnd_1068876 182949049351755083811445 := by
  unfold tailWord_1068876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19492555237826138166201241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25990073650434850888268321 19492555237826138166201241)
  ·
    refine ⟨14619416428369603624650931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19492555237826138166201241 14619416428369603624650931)
    ·
      refine ⟨21929124642554405436976397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14619416428369603624650931 21929124642554405436976397)
      ·
        refine ⟨8223421740957902038866149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21929124642554405436976397 8223421740957902038866149)
        ·
          refine ⟨1541891576429606632287403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8223421740957902038866149 1541891576429606632287403)
          ·
            refine ⟨2312837364644409948431105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541891576429606632287403 2312837364644409948431105)
            ·
              refine ⟨1734628023483307461323329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312837364644409948431105 1734628023483307461323329)
              ·
                refine ⟨1300971017612480595992497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1734628023483307461323329 1300971017612480595992497)
                ·
                  refine ⟨975728263209360446994373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300971017612480595992497 975728263209360446994373)
                  ·
                    refine ⟨182949049351755083811445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 975728263209360446994373 182949049351755083811445)
                    ·
                      rfl

theorem cell23_1068876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_1068876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068876 prefixEnd_1068876 := by exact prefixLift 1068876
  have htrace : WordTrace (prefixWord ++ tailWord_1068876) baseStart_1068876 baseEnd_1068876 := by
    simpa [prefixWord, tailWord_1068876, baseEnd_1068876] using wordTrace_append hprefix tailTrace_1068876
  have hstable : (prefixWord ++ tailWord_1068876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068876).length < 2 ^ (prefixWord ++ tailWord_1068876).sum := by decide
  have hdescent : baseEnd_1068876 < baseStart_1068876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068877 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1068877 : Nat := 118140960795 + 1068877 * 2 ^ 59
def prefixEnd_1068877 : Nat := 4983230072969 + 3 ^ 40 * 1068877 * 2
def baseEnd_1068877 : Nat := 548847661535919747521831

theorem tailTrace_1068877 : CollatzResearch.WordTrace tailWord_1068877 prefixEnd_1068877 548847661535919747521831 := by
  unfold tailWord_1068877
  simp only [CollatzResearch.WordTrace]
  refine ⟨38985146948648653503188885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25990097965765769002125923 38985146948648653503188885)
  ·
    refine ⟨1827428763217905632961979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38985146948648653503188885 1827428763217905632961979)
    ·
      refine ⟨2741143144826858449442969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1827428763217905632961979 2741143144826858449442969)
      ·
        refine ⟨2055857358620143837082227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2741143144826858449442969 2055857358620143837082227)
        ·
          refine ⟨3083786037930215755623341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2055857358620143837082227 3083786037930215755623341)
          ·
            refine ⟨1156419764223830908358753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3083786037930215755623341 1156419764223830908358753)
            ·
              refine ⟨867314823167873181269065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156419764223830908358753 867314823167873181269065)
              ·
                refine ⟨650486117375904885951799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867314823167873181269065 650486117375904885951799)
                ·
                  refine ⟨975729176063857328927699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650486117375904885951799 975729176063857328927699)
                  ·
                    refine ⟨1463593764095785993391549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 975729176063857328927699 1463593764095785993391549)
                    ·
                      refine ⟨548847661535919747521831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1463593764095785993391549 548847661535919747521831)
                      ·
                        rfl

theorem cell23_1068877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1068877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068877 prefixEnd_1068877 := by exact prefixLift 1068877
  have htrace : WordTrace (prefixWord ++ tailWord_1068877) baseStart_1068877 baseEnd_1068877 := by
    simpa [prefixWord, tailWord_1068877, baseEnd_1068877] using wordTrace_append hprefix tailTrace_1068877
  have hstable : (prefixWord ++ tailWord_1068877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068877).length < 2 ^ (prefixWord ++ tailWord_1068877).sum := by decide
  have hdescent : baseEnd_1068877 < baseStart_1068877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068906 : List Nat := [3, 1, 3, 4, 1, 1, 3, 7]
def baseStart_1068906 : Nat := 118140960795 + 1068906 * 2 ^ 59
def prefixEnd_1068906 : Nat := 4983230072969 + 3 ^ 40 * 1068906 * 2
def baseEnd_1068906 : Nat := 20328242684255560520711

theorem tailTrace_1068906 : CollatzResearch.WordTrace tailWord_1068906 prefixEnd_1068906 20328242684255560520711 := by
  unfold tailWord_1068906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746551166385897863998643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25990803110362394303996381 9746551166385897863998643)
  ·
    refine ⟨14619826749578846795997965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9746551166385897863998643 14619826749578846795997965)
    ·
      refine ⟨5482435031092067548499237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14619826749578846795997965 5482435031092067548499237)
      ·
        refine ⟨1027956568329762665343607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5482435031092067548499237 1027956568329762665343607)
        ·
          refine ⟨1541934852494643998015411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027956568329762665343607 1541934852494643998015411)
          ·
            refine ⟨2312902278741965997023117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541934852494643998015411 2312902278741965997023117)
            ·
              refine ⟨867338354528237248883669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2312902278741965997023117 867338354528237248883669)
              ·
                refine ⟨20328242684255560520711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 867338354528237248883669 20328242684255560520711)
                ·
                  rfl

theorem cell23_1068906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_1068906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068906 prefixEnd_1068906 := by exact prefixLift 1068906
  have htrace : WordTrace (prefixWord ++ tailWord_1068906) baseStart_1068906 baseEnd_1068906 := by
    simpa [prefixWord, tailWord_1068906, baseEnd_1068906] using wordTrace_append hprefix tailTrace_1068906
  have hstable : (prefixWord ++ tailWord_1068906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068906).length < 2 ^ (prefixWord ++ tailWord_1068906).sum := by decide
  have hdescent : baseEnd_1068906 < baseStart_1068906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068915 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 8]
def baseStart_1068915 : Nat := 118140960795 + 1068915 * 2 ^ 59
def prefixEnd_1068915 : Nat := 4983230072969 + 3 ^ 40 * 1068915 * 2
def baseEnd_1068915 : Nat := 182955724600263532948885

theorem tailTrace_1068915 : CollatzResearch.WordTrace tailWord_1068915 prefixEnd_1068915 182955724600263532948885 := by
  unfold tailWord_1068915
  simp only [CollatzResearch.WordTrace]
  refine ⟨38986532922510985993072199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25991021948340657328714799 38986532922510985993072199)
  ·
    refine ⟨58479799383766478989608299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38986532922510985993072199 58479799383766478989608299)
    ·
      refine ⟨87719699075649718484412449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58479799383766478989608299 87719699075649718484412449)
      ·
        refine ⟨65789774306737288863309337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87719699075649718484412449 65789774306737288863309337)
        ·
          refine ⟨49342330730052966647482003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65789774306737288863309337 49342330730052966647482003)
          ·
            refine ⟨74013496095079449971223005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49342330730052966647482003 74013496095079449971223005)
            ·
              refine ⟨27755061035654793739208627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74013496095079449971223005 27755061035654793739208627)
              ·
                refine ⟨41632591553482190608812941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27755061035654793739208627 41632591553482190608812941)
                ·
                  refine ⟨15612221832555821478304853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41632591553482190608812941 15612221832555821478304853)
                  ·
                    refine ⟨182955724600263532948885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15612221832555821478304853 182955724600263532948885)
                    ·
                      rfl

theorem cell23_1068915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_1068915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068915 prefixEnd_1068915 := by exact prefixLift 1068915
  have htrace : WordTrace (prefixWord ++ tailWord_1068915) baseStart_1068915 baseEnd_1068915 := by
    simpa [prefixWord, tailWord_1068915, baseEnd_1068915] using wordTrace_append hprefix tailTrace_1068915
  have hstable : (prefixWord ++ tailWord_1068915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068915).length < 2 ^ (prefixWord ++ tailWord_1068915).sum := by decide
  have hdescent : baseEnd_1068915 < baseStart_1068915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068932 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1068932 : Nat := 118140960795 + 1068932 * 2 ^ 59
def prefixEnd_1068932 : Nat := 4983230072969 + 3 ^ 40 * 1068932 * 2
def baseEnd_1068932 : Nat := 182958634323972344111359

theorem tailTrace_1068932 : CollatzResearch.WordTrace tailWord_1068932 prefixEnd_1068932 182958634323972344111359 := by
  unfold tailWord_1068932
  simp only [CollatzResearch.WordTrace]
  refine ⟨19493576481724698948220525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25991435308966265264294033 19493576481724698948220525)
  ·
    refine ⟨7310091180646762105582697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19493576481724698948220525 7310091180646762105582697)
    ·
      refine ⟨5482568385485071579187023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7310091180646762105582697 5482568385485071579187023)
      ·
        refine ⟨8223852578227607368780535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5482568385485071579187023 8223852578227607368780535)
        ·
          refine ⟨12335778867341411053170803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223852578227607368780535 12335778867341411053170803)
          ·
            refine ⟨18503668301012116579756205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12335778867341411053170803 18503668301012116579756205)
            ·
              refine ⟨6938875612879543717408577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18503668301012116579756205 6938875612879543717408577)
              ·
                refine ⟨5204156709659657788056433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6938875612879543717408577 5204156709659657788056433)
                ·
                  refine ⟨3903117532244743341042325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204156709659657788056433 3903117532244743341042325)
                  ·
                    refine ⟨182958634323972344111359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3903117532244743341042325 182958634323972344111359)
                    ·
                      rfl

theorem cell23_1068932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1068932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068932 prefixEnd_1068932 := by exact prefixLift 1068932
  have htrace : WordTrace (prefixWord ++ tailWord_1068932) baseStart_1068932 baseEnd_1068932 := by
    simpa [prefixWord, tailWord_1068932, baseEnd_1068932] using wordTrace_append hprefix tailTrace_1068932
  have hstable : (prefixWord ++ tailWord_1068932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068932).length < 2 ^ (prefixWord ++ tailWord_1068932).sum := by decide
  have hdescent : baseEnd_1068932 < baseStart_1068932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068999 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_1068999 : Nat := 118140960795 + 1068999 * 2 ^ 59
def prefixEnd_1068999 : Nat := 4983230072969 + 3 ^ 40 * 1068999 * 2
def baseEnd_1068999 : Nat := 548910306175768270196269

theorem tailTrace_1068999 : CollatzResearch.WordTrace tailWord_1068999 prefixEnd_1068999 548910306175768270196269 := by
  unfold tailWord_1068999
  simp only [CollatzResearch.WordTrace]
  refine ⟨38989596654206668339130051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25993064436137778892753367 38989596654206668339130051)
  ·
    refine ⟨58484394981310002508695077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38989596654206668339130051 58484394981310002508695077)
    ·
      refine ⟨10965824058995625470380327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58484394981310002508695077 10965824058995625470380327)
      ·
        refine ⟨16448736088493438205570491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10965824058995625470380327 16448736088493438205570491)
        ·
          refine ⟨24673104132740157308355737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16448736088493438205570491 24673104132740157308355737)
          ·
            refine ⟨18504828099555117981266803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24673104132740157308355737 18504828099555117981266803)
            ·
              refine ⟨27757242149332676971900205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18504828099555117981266803 27757242149332676971900205)
              ·
                refine ⟨10408965805999753864462577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27757242149332676971900205 10408965805999753864462577)
                ·
                  refine ⟨7806724354499815398346933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10408965805999753864462577 7806724354499815398346933)
                  ·
                    refine ⟨731880408234357693595025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7806724354499815398346933 731880408234357693595025)
                    ·
                      refine ⟨548910306175768270196269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731880408234357693595025 548910306175768270196269)
                      ·
                        rfl

theorem cell23_1068999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_1068999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1068999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1068999 prefixEnd_1068999 := by exact prefixLift 1068999
  have htrace : WordTrace (prefixWord ++ tailWord_1068999) baseStart_1068999 baseEnd_1068999 := by
    simpa [prefixWord, tailWord_1068999, baseEnd_1068999] using wordTrace_append hprefix tailTrace_1068999
  have hstable : (prefixWord ++ tailWord_1068999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068999).length < 2 ^ (prefixWord ++ tailWord_1068999).sum := by decide
  have hdescent : baseEnd_1068999 < baseStart_1068999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069002 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1069002 : Nat := 118140960795 + 1069002 * 2 ^ 59
def prefixEnd_1069002 : Nat := 4983230072969 + 3 ^ 40 * 1069002 * 2
def baseEnd_1069002 : Nat := 548911846617731758458755

theorem tailTrace_1069002 : CollatzResearch.WordTrace tailWord_1069002 prefixEnd_1069002 548911846617731758458755 := by
  unfold tailWord_1069002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9747426518298949962872315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25993137382130533234326173 9747426518298949962872315)
  ·
    refine ⟨14621139777448424944308473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9747426518298949962872315 14621139777448424944308473)
    ·
      refine ⟨10965854833086318708231355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14621139777448424944308473 10965854833086318708231355)
      ·
        refine ⟨16448782249629478062347033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10965854833086318708231355 16448782249629478062347033)
        ·
          refine ⟨12336586687222108546760275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16448782249629478062347033 12336586687222108546760275)
          ·
            refine ⟨18504880030833162820140413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12336586687222108546760275 18504880030833162820140413)
            ·
              refine ⟨6939330011562436057552655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18504880030833162820140413 6939330011562436057552655)
              ·
                refine ⟨10408995017343654086328983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6939330011562436057552655 10408995017343654086328983)
                ·
                  refine ⟨15613492526015481129493475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10408995017343654086328983 15613492526015481129493475)
                  ·
                    refine ⟨23420238789023221694240213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15613492526015481129493475 23420238789023221694240213)
                    ·
                      refine ⟨548911846617731758458755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23420238789023221694240213 548911846617731758458755)
                      ·
                        rfl

theorem cell23_1069002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1069002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069002 prefixEnd_1069002 := by exact prefixLift 1069002
  have htrace : WordTrace (prefixWord ++ tailWord_1069002) baseStart_1069002 baseEnd_1069002 := by
    simpa [prefixWord, tailWord_1069002, baseEnd_1069002] using wordTrace_append hprefix tailTrace_1069002
  have hstable : (prefixWord ++ tailWord_1069002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069002).length < 2 ^ (prefixWord ++ tailWord_1069002).sum := by decide
  have hdescent : baseEnd_1069002 < baseStart_1069002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069072 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_1069072 : Nat := 118140960795 + 1069072 * 2 ^ 59
def prefixEnd_1069072 : Nat := 4983230072969 + 3 ^ 40 * 1069072 * 2
def baseEnd_1069072 : Nat := 548947790263546484583433

theorem tailTrace_1069072 : CollatzResearch.WordTrace tailWord_1069072 prefixEnd_1069072 548947790263546484583433 := by
  unfold tailWord_1069072
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496129591471100903268735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25994839455294801204358313 19496129591471100903268735)
  ·
    refine ⟨29244194387206651354903103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19496129591471100903268735 29244194387206651354903103)
    ·
      refine ⟨43866291580809977032354655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29244194387206651354903103 43866291580809977032354655)
      ·
        refine ⟨65799437371214965548531983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43866291580809977032354655 65799437371214965548531983)
        ·
          refine ⟨98699156056822448322797975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65799437371214965548531983 98699156056822448322797975)
          ·
            refine ⟨148048734085233672484196963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98699156056822448322797975 148048734085233672484196963)
            ·
              refine ⟨222073101127850508726295445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148048734085233672484196963 222073101127850508726295445)
              ·
                refine ⟨10409676615367992596545099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 222073101127850508726295445 10409676615367992596545099)
                ·
                  refine ⟨15614514923051988894817649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10409676615367992596545099 15614514923051988894817649)
                  ·
                    refine ⟨11710886192288991671113237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15614514923051988894817649 11710886192288991671113237)
                    ·
                      refine ⟨548947790263546484583433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11710886192288991671113237 548947790263546484583433)
                      ·
                        rfl

theorem cell23_1069072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_1069072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069072 prefixEnd_1069072 := by exact prefixLift 1069072
  have htrace : WordTrace (prefixWord ++ tailWord_1069072) baseStart_1069072 baseEnd_1069072 := by
    simpa [prefixWord, tailWord_1069072, baseEnd_1069072] using wordTrace_append hprefix tailTrace_1069072
  have hstable : (prefixWord ++ tailWord_1069072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069072).length < 2 ^ (prefixWord ++ tailWord_1069072).sum := by decide
  have hdescent : baseEnd_1069072 < baseStart_1069072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069119 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_1069119 : Nat := 118140960795 + 1069119 * 2 ^ 59
def prefixEnd_1069119 : Nat := 4983230072969 + 3 ^ 40 * 1069119 * 2
def baseEnd_1069119 : Nat := 548971923854307800695717

theorem tailTrace_1069119 : CollatzResearch.WordTrace tailWord_1069119 prefixEnd_1069119 548971923854307800695717 := by
  unfold tailWord_1069119
  simp only [CollatzResearch.WordTrace]
  refine ⟨38993973413771928833498411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25995982275847952555665607 38993973413771928833498411)
  ·
    refine ⟨58490960120657893250247617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38993973413771928833498411 58490960120657893250247617)
    ·
      refine ⟨43868220090493419937685713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58490960120657893250247617 43868220090493419937685713)
      ·
        refine ⟨32901165067870064953264285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43868220090493419937685713 32901165067870064953264285)
        ·
          refine ⟨12337936900451274357474107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32901165067870064953264285 12337936900451274357474107)
          ·
            refine ⟨18506905350676911536211161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12337936900451274357474107 18506905350676911536211161)
            ·
              refine ⟨13880179013007683652158371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18506905350676911536211161 13880179013007683652158371)
              ·
                refine ⟨20820268519511525478237557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13880179013007683652158371 20820268519511525478237557)
                ·
                  refine ⟨1951900173704205513584771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20820268519511525478237557 1951900173704205513584771)
                  ·
                    refine ⟨2927850260556308270377157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1951900173704205513584771 2927850260556308270377157)
                    ·
                      refine ⟨548971923854307800695717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2927850260556308270377157 548971923854307800695717)
                      ·
                        rfl

theorem cell23_1069119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_1069119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069119 prefixEnd_1069119 := by exact prefixLift 1069119
  have htrace : WordTrace (prefixWord ++ tailWord_1069119) baseStart_1069119 baseEnd_1069119 := by
    simpa [prefixWord, tailWord_1069119, baseEnd_1069119] using wordTrace_append hprefix tailTrace_1069119
  have hstable : (prefixWord ++ tailWord_1069119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069119).length < 2 ^ (prefixWord ++ tailWord_1069119).sum := by decide
  have hdescent : baseEnd_1069119 < baseStart_1069119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069133 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1069133 : Nat := 118140960795 + 1069133 * 2 ^ 59
def prefixEnd_1069133 : Nat := 4983230072969 + 3 ^ 40 * 1069133 * 2
def baseEnd_1069133 : Nat := 182993037527823581973551

theorem tailTrace_1069133 : CollatzResearch.WordTrace tailWord_1069133 prefixEnd_1069133 182993037527823581973551 := by
  unfold tailWord_1069133
  simp only [CollatzResearch.WordTrace]
  refine ⟨38994484035721209224508053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25996322690480806149672035 38994484035721209224508053)
  ·
    refine ⟨1827866439174431682398815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38994484035721209224508053 1827866439174431682398815)
    ·
      refine ⟨2741799658761647523598223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1827866439174431682398815 2741799658761647523598223)
      ·
        refine ⟨4112699488142471285397335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2741799658761647523598223 4112699488142471285397335)
        ·
          refine ⟨6169049232213706928096003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4112699488142471285397335 6169049232213706928096003)
          ·
            refine ⟨9253573848320560392144005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6169049232213706928096003 9253573848320560392144005)
            ·
              refine ⟨1735045096560105073527001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9253573848320560392144005 1735045096560105073527001)
              ·
                refine ⟨1301283822420078805145251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735045096560105073527001 1301283822420078805145251)
                ·
                  refine ⟨1951925733630118207717877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301283822420078805145251 1951925733630118207717877)
                  ·
                    refine ⟨182993037527823581973551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1951925733630118207717877 182993037527823581973551)
                    ·
                      rfl

theorem cell23_1069133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1069133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069133 prefixEnd_1069133 := by exact prefixLift 1069133
  have htrace : WordTrace (prefixWord ++ tailWord_1069133) baseStart_1069133 baseEnd_1069133 := by
    simpa [prefixWord, tailWord_1069133, baseEnd_1069133] using wordTrace_append hprefix tailTrace_1069133
  have hstable : (prefixWord ++ tailWord_1069133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069133).length < 2 ^ (prefixWord ++ tailWord_1069133).sum := by decide
  have hdescent : baseEnd_1069133 < baseStart_1069133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069170 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_1069170 : Nat := 118140960795 + 1069170 * 2 ^ 59
def prefixEnd_1069170 : Nat := 4983230072969 + 3 ^ 40 * 1069170 * 2
def baseEnd_1069170 : Nat := 548998111367687101157983

theorem tailTrace_1069170 : CollatzResearch.WordTrace tailWord_1069170 prefixEnd_1069170 548998111367687101157983 := by
  unfold tailWord_1069170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748958384146791135901241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25997222357724776362403309 9748958384146791135901241)
  ·
    refine ⟨7311718788110093351925931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9748958384146791135901241 7311718788110093351925931)
    ·
      refine ⟨10967578182165140027888897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7311718788110093351925931 10967578182165140027888897)
      ·
        refine ⟨8225683636623855020916673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10967578182165140027888897 8225683636623855020916673)
        ·
          refine ⟨6169262727467891265687505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8225683636623855020916673 6169262727467891265687505)
          ·
            refine ⟨4626947045600918449265629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6169262727467891265687505 4626947045600918449265629)
            ·
              refine ⟨1735105142100344418474611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4626947045600918449265629 1735105142100344418474611)
              ·
                refine ⟨2602657713150516627711917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735105142100344418474611 2602657713150516627711917)
                ·
                  refine ⟨975996642431443735391969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2602657713150516627711917 975996642431443735391969)
                  ·
                    refine ⟨731997481823582801543977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 975996642431443735391969 731997481823582801543977)
                    ·
                      refine ⟨548998111367687101157983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 731997481823582801543977 548998111367687101157983)
                      ·
                        rfl

theorem cell23_1069170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_1069170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069170 prefixEnd_1069170 := by exact prefixLift 1069170
  have htrace : WordTrace (prefixWord ++ tailWord_1069170) baseStart_1069170 baseEnd_1069170 := by
    simpa [prefixWord, tailWord_1069170, baseEnd_1069170] using wordTrace_append hprefix tailTrace_1069170
  have hstable : (prefixWord ++ tailWord_1069170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069170).length < 2 ^ (prefixWord ++ tailWord_1069170).sum := by decide
  have hdescent : baseEnd_1069170 < baseStart_1069170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069180 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_1069180 : Nat := 118140960795 + 1069180 * 2 ^ 59
def prefixEnd_1069180 : Nat := 4983230072969 + 3 ^ 40 * 1069180 * 2
def baseEnd_1069180 : Nat := 183001082058077354010979

theorem tailTrace_1069180 : CollatzResearch.WordTrace tailWord_1069180 prefixEnd_1069180 183001082058077354010979 := by
  unfold tailWord_1069180
  simp only [CollatzResearch.WordTrace]
  refine ⟨19498099133275468125734497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25997465511033957500979329 19498099133275468125734497)
  ·
    refine ⟨14623574349956601094300873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19498099133275468125734497 14623574349956601094300873)
    ·
      refine ⟨10967680762467450820725655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14623574349956601094300873 10967680762467450820725655)
      ·
        refine ⟨16451521143701176231088483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10967680762467450820725655 16451521143701176231088483)
        ·
          refine ⟨24677281715551764346632725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16451521143701176231088483 24677281715551764346632725)
          ·
            refine ⟨1156747580416488953748409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24677281715551764346632725 1156747580416488953748409)
            ·
              refine ⟨867560685312366715311307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156747580416488953748409 867560685312366715311307)
              ·
                refine ⟨1301341027968550072966961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867560685312366715311307 1301341027968550072966961)
                ·
                  refine ⟨976005770976412554725221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301341027968550072966961 976005770976412554725221)
                  ·
                    refine ⟨183001082058077354010979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976005770976412554725221 183001082058077354010979)
                    ·
                      rfl

theorem cell23_1069180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_1069180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069180 prefixEnd_1069180 := by exact prefixLift 1069180
  have htrace : WordTrace (prefixWord ++ tailWord_1069180) baseStart_1069180 baseEnd_1069180 := by
    simpa [prefixWord, tailWord_1069180, baseEnd_1069180] using wordTrace_append hprefix tailTrace_1069180
  have hstable : (prefixWord ++ tailWord_1069180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069180).length < 2 ^ (prefixWord ++ tailWord_1069180).sum := by decide
  have hdescent : baseEnd_1069180 < baseStart_1069180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069209 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_1069209 : Nat := 118140960795 + 1069209 * 2 ^ 59
def prefixEnd_1069209 : Nat := 4983230072969 + 3 ^ 40 * 1069209 * 2
def baseEnd_1069209 : Nat := 549018137113212448570303

theorem tailTrace_1069209 : CollatzResearch.WordTrace tailWord_1069209 prefixEnd_1069209 549018137113212448570303 := by
  unfold tailWord_1069209
  simp only [CollatzResearch.WordTrace]
  refine ⟨38997255983445874204274681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25998170655630582802849787 38997255983445874204274681)
  ·
    refine ⟨29247941987584405653206011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38997255983445874204274681 29247941987584405653206011)
    ·
      refine ⟨43871912981376608479809017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29247941987584405653206011 43871912981376608479809017)
      ·
        refine ⟨32903934736032456359856763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43871912981376608479809017 32903934736032456359856763)
        ·
          refine ⟨49355902104048684539785145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32903934736032456359856763 49355902104048684539785145)
          ·
            refine ⟨37016926578036513404838859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49355902104048684539785145 37016926578036513404838859)
            ·
              refine ⟨55525389867054770107258289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37016926578036513404838859 55525389867054770107258289)
              ·
                refine ⟨41644042400291077580443717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55525389867054770107258289 41644042400291077580443717)
                ·
                  refine ⟨7808257950054577046333197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41644042400291077580443717 7808257950054577046333197)
                  ·
                    refine ⟨2928096731270466392374949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7808257950054577046333197 2928096731270466392374949)
                    ·
                      refine ⟨549018137113212448570303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2928096731270466392374949 549018137113212448570303)
                      ·
                        rfl

theorem cell23_1069209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_1069209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069209 prefixEnd_1069209 := by exact prefixLift 1069209
  have htrace : WordTrace (prefixWord ++ tailWord_1069209) baseStart_1069209 baseEnd_1069209 := by
    simpa [prefixWord, tailWord_1069209, baseEnd_1069209] using wordTrace_append hprefix tailTrace_1069209
  have hstable : (prefixWord ++ tailWord_1069209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069209).length < 2 ^ (prefixWord ++ tailWord_1069209).sum := by decide
  have hdescent : baseEnd_1069209 < baseStart_1069209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069243 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 1, 4, 2]
def baseStart_1069243 : Nat := 118140960795 + 1069243 * 2 ^ 59
def prefixEnd_1069243 : Nat := 4983230072969 + 3 ^ 40 * 1069243 * 2
def baseEnd_1069243 : Nat := 549035595455465315545147

theorem tailTrace_1069243 : CollatzResearch.WordTrace tailWord_1069243 prefixEnd_1069243 549035595455465315545147 := by
  unfold tailWord_1069243
  simp only [CollatzResearch.WordTrace]
  refine ⟨38998496065322698011012383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25998997376881798674008255 38998496065322698011012383)
  ·
    refine ⟨58497744097984047016518575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38998496065322698011012383 58497744097984047016518575)
    ·
      refine ⟨87746616146976070524777863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58497744097984047016518575 87746616146976070524777863)
      ·
        refine ⟨131619924220464105787166795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87746616146976070524777863 131619924220464105787166795)
        ·
          refine ⟨197429886330696158680750193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131619924220464105787166795 197429886330696158680750193)
          ·
            refine ⟨148072414748022119010562645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197429886330696158680750193 148072414748022119010562645)
            ·
              refine ⟨1735223610328384207155031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 148072414748022119010562645 1735223610328384207155031)
              ·
                refine ⟨2602835415492576310732547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735223610328384207155031 2602835415492576310732547)
                ·
                  refine ⟨3904253123238864466098821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602835415492576310732547 3904253123238864466098821)
                  ·
                    refine ⟨732047460607287087393529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904253123238864466098821 732047460607287087393529)
                    ·
                      refine ⟨549035595455465315545147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732047460607287087393529 549035595455465315545147)
                      ·
                        rfl

theorem cell23_1069243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4, 2].length) (baseStart_1069243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069243 prefixEnd_1069243 := by exact prefixLift 1069243
  have htrace : WordTrace (prefixWord ++ tailWord_1069243) baseStart_1069243 baseEnd_1069243 := by
    simpa [prefixWord, tailWord_1069243, baseEnd_1069243] using wordTrace_append hprefix tailTrace_1069243
  have hstable : (prefixWord ++ tailWord_1069243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069243).length < 2 ^ (prefixWord ++ tailWord_1069243).sum := by decide
  have hdescent : baseEnd_1069243 < baseStart_1069243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069277 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1069277 : Nat := 118140960795 + 1069277 * 2 ^ 59
def prefixEnd_1069277 : Nat := 4983230072969 + 3 ^ 40 * 1069277 * 2
def baseEnd_1069277 : Nat := 549053053797718182519991

theorem tailTrace_1069277 : CollatzResearch.WordTrace tailWord_1069277 prefixEnd_1069277 549053053797718182519991 := by
  unfold tailWord_1069277
  simp only [CollatzResearch.WordTrace]
  refine ⟨38999736147199521817750085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25999824098133014545166723 38999736147199521817750085)
  ·
    refine ⟨7312450527599910340828141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38999736147199521817750085 7312450527599910340828141)
    ·
      refine ⟨2742168947849966377810553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7312450527599910340828141 2742168947849966377810553)
      ·
        refine ⟨2056626710887474783357915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2742168947849966377810553 2056626710887474783357915)
        ·
          refine ⟨3084940066331212175036873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2056626710887474783357915 3084940066331212175036873)
          ·
            refine ⟨2313705049748409131277655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3084940066331212175036873 2313705049748409131277655)
            ·
              refine ⟨3470557574622613696916483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313705049748409131277655 3470557574622613696916483)
              ·
                refine ⟨5205836361933920545374725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470557574622613696916483 5205836361933920545374725)
                ·
                  refine ⟨976094317862610102257761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5205836361933920545374725 976094317862610102257761)
                  ·
                    refine ⟨732070738396957576693321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 976094317862610102257761 732070738396957576693321)
                    ·
                      refine ⟨549053053797718182519991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732070738396957576693321 549053053797718182519991)
                      ·
                        rfl

theorem cell23_1069277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1069277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069277 prefixEnd_1069277 := by exact prefixLift 1069277
  have htrace : WordTrace (prefixWord ++ tailWord_1069277) baseStart_1069277 baseEnd_1069277 := by
    simpa [prefixWord, tailWord_1069277, baseEnd_1069277] using wordTrace_append hprefix tailTrace_1069277
  have hstable : (prefixWord ++ tailWord_1069277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069277).length < 2 ^ (prefixWord ++ tailWord_1069277).sum := by decide
  have hdescent : baseEnd_1069277 < baseStart_1069277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069333 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_1069333 : Nat := 118140960795 + 1069333 * 2 ^ 59
def prefixEnd_1069333 : Nat := 4983230072969 + 3 ^ 40 * 1069333 * 2
def baseEnd_1069333 : Nat := 549081808714369963419733

theorem tailTrace_1069333 : CollatzResearch.WordTrace tailWord_1069333 prefixEnd_1069333 549081808714369963419733 := by
  unfold tailWord_1069333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39001778634996643381788653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26001185756664428921192435 39001778634996643381788653)
  ·
    refine ⟨14625666988123741268170745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39001778634996643381788653 14625666988123741268170745)
    ·
      refine ⟨10969250241092805951128059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14625666988123741268170745 10969250241092805951128059)
      ·
        refine ⟨16453875361639208926692089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10969250241092805951128059 16453875361639208926692089)
        ·
          refine ⟨12340406521229406695019067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16453875361639208926692089 12340406521229406695019067)
          ·
            refine ⟨18510609781844110042528601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12340406521229406695019067 18510609781844110042528601)
            ·
              refine ⟨13882957336383082531896451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18510609781844110042528601 13882957336383082531896451)
              ·
                refine ⟨20824436004574623797844677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13882957336383082531896451 20824436004574623797844677)
                ·
                  refine ⟨3904581750857741962095877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20824436004574623797844677 3904581750857741962095877)
                  ·
                    refine ⟨732109078285826617892977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904581750857741962095877 732109078285826617892977)
                    ·
                      refine ⟨549081808714369963419733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732109078285826617892977 549081808714369963419733)
                      ·
                        rfl

theorem cell23_1069333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_1069333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069333 prefixEnd_1069333 := by exact prefixLift 1069333
  have htrace : WordTrace (prefixWord ++ tailWord_1069333) baseStart_1069333 baseEnd_1069333 := by
    simpa [prefixWord, tailWord_1069333, baseEnd_1069333] using wordTrace_append hprefix tailTrace_1069333
  have hstable : (prefixWord ++ tailWord_1069333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069333).length < 2 ^ (prefixWord ++ tailWord_1069333).sum := by decide
  have hdescent : baseEnd_1069333 < baseStart_1069333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069370 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_1069370 : Nat := 118140960795 + 1069370 * 2 ^ 59
def prefixEnd_1069370 : Nat := 4983230072969 + 3 ^ 40 * 1069370 * 2
def baseEnd_1069370 : Nat := 549100807498586318657063

theorem tailTrace_1069370 : CollatzResearch.WordTrace tailWord_1069370 prefixEnd_1069370 549100807498586318657063 := by
  unfold tailWord_1069370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750782033965649675221391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26002085423908399133923709 9750782033965649675221391)
  ·
    refine ⟨14626173050948474512832087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9750782033965649675221391 14626173050948474512832087)
    ·
      refine ⟨21939259576422711769248131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14626173050948474512832087 21939259576422711769248131)
      ·
        refine ⟨32908889364634067653872197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21939259576422711769248131 32908889364634067653872197)
        ·
          refine ⟨6170416755868887685101037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32908889364634067653872197 6170416755868887685101037)
          ·
            refine ⟨2313906283450832881912889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6170416755868887685101037 2313906283450832881912889)
            ·
              refine ⟨1735429712588124661434667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2313906283450832881912889 1735429712588124661434667)
              ·
                refine ⟨2603144568882186992152001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735429712588124661434667 2603144568882186992152001)
                ·
                  refine ⟨1952358426661640244114001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603144568882186992152001 1952358426661640244114001)
                  ·
                    refine ⟨1464268819996230183085501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1952358426661640244114001 1464268819996230183085501)
                    ·
                      refine ⟨549100807498586318657063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1464268819996230183085501 549100807498586318657063)
                      ·
                        rfl

theorem cell23_1069370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_1069370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069370 prefixEnd_1069370 := by exact prefixLift 1069370
  have htrace : WordTrace (prefixWord ++ tailWord_1069370) baseStart_1069370 baseEnd_1069370 := by
    simpa [prefixWord, tailWord_1069370, baseEnd_1069370] using wordTrace_append hprefix tailTrace_1069370
  have hstable : (prefixWord ++ tailWord_1069370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069370).length < 2 ^ (prefixWord ++ tailWord_1069370).sum := by decide
  have hdescent : baseEnd_1069370 < baseStart_1069370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069423 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 8, 2]
def baseStart_1069423 : Nat := 118140960795 + 1069423 * 2 ^ 59
def prefixEnd_1069423 : Nat := 4983230072969 + 3 ^ 40 * 1069423 * 2
def baseEnd_1069423 : Nat := 549128021973274611294319

theorem tailTrace_1069423 : CollatzResearch.WordTrace tailWord_1069423 prefixEnd_1069423 549128021973274611294319 := by
  unfold tailWord_1069423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39005061204670588752564923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26003374136447059168376615 39005061204670588752564923)
  ·
    refine ⟨58507591807005883128847385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39005061204670588752564923 58507591807005883128847385)
    ·
      refine ⟨43880693855254412346635539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58507591807005883128847385 43880693855254412346635539)
      ·
        refine ⟨65821040782881618519953309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43880693855254412346635539 65821040782881618519953309)
        ·
          refine ⟨24682890293580606944982491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65821040782881618519953309 24682890293580606944982491)
          ·
            refine ⟨37024335440370910417473737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24682890293580606944982491 37024335440370910417473737)
            ·
              refine ⟨27768251580278182813105303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37024335440370910417473737 27768251580278182813105303)
              ·
                refine ⟨41652377370417274219657955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27768251580278182813105303 41652377370417274219657955)
                ·
                  refine ⟨62478566055625911329486933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41652377370417274219657955 62478566055625911329486933)
                  ·
                    refine ⟨732170695964366148392425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62478566055625911329486933 732170695964366148392425)
                    ·
                      refine ⟨549128021973274611294319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732170695964366148392425 549128021973274611294319)
                      ·
                        rfl

theorem cell23_1069423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8, 2].length) (baseStart_1069423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069423 prefixEnd_1069423 := by exact prefixLift 1069423
  have htrace : WordTrace (prefixWord ++ tailWord_1069423) baseStart_1069423 baseEnd_1069423 := by
    simpa [prefixWord, tailWord_1069423, baseEnd_1069423] using wordTrace_append hprefix tailTrace_1069423
  have hstable : (prefixWord ++ tailWord_1069423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069423).length < 2 ^ (prefixWord ++ tailWord_1069423).sum := by decide
  have hdescent : baseEnd_1069423 < baseStart_1069423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069433 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 4, 4]
def baseStart_1069433 : Nat := 118140960795 + 1069433 * 2 ^ 59
def prefixEnd_1069433 : Nat := 4983230072969 + 3 ^ 40 * 1069433 * 2
def baseEnd_1069433 : Nat := 183044385593273190723091

theorem tailTrace_1069433 : CollatzResearch.WordTrace tailWord_1069433 prefixEnd_1069433 183044385593273190723091 := by
  unfold tailWord_1069433
  simp only [CollatzResearch.WordTrace]
  refine ⟨39005425934634360460428953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26003617289756240306952635 39005425934634360460428953)
  ·
    refine ⟨29254069450975770345321715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39005425934634360460428953 29254069450975770345321715)
    ·
      refine ⟨43881104176463655517982573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29254069450975770345321715 43881104176463655517982573)
      ·
        refine ⟨16455414066173870819243465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43881104176463655517982573 16455414066173870819243465)
        ·
          refine ⟨12341560549630403114432599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16455414066173870819243465 12341560549630403114432599)
          ·
            refine ⟨18512340824445604671648899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12341560549630403114432599 18512340824445604671648899)
            ·
              refine ⟨27768511236668407007473349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18512340824445604671648899 27768511236668407007473349)
              ·
                refine ⟨5206595856875326313901253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27768511236668407007473349 5206595856875326313901253)
                ·
                  refine ⟨976236723164123683856485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5206595856875326313901253 976236723164123683856485)
                  ·
                    refine ⟨183044385593273190723091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976236723164123683856485 183044385593273190723091)
                    ·
                      rfl

theorem cell23_1069433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_1069433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069433 prefixEnd_1069433 := by exact prefixLift 1069433
  have htrace : WordTrace (prefixWord ++ tailWord_1069433) baseStart_1069433 baseEnd_1069433 := by
    simpa [prefixWord, tailWord_1069433, baseEnd_1069433] using wordTrace_append hprefix tailTrace_1069433
  have hstable : (prefixWord ++ tailWord_1069433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069433).length < 2 ^ (prefixWord ++ tailWord_1069433).sum := by decide
  have hdescent : baseEnd_1069433 < baseStart_1069433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069437 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_1069437 : Nat := 118140960795 + 1069437 * 2 ^ 59
def prefixEnd_1069437 : Nat := 4983230072969 + 3 ^ 40 * 1069437 * 2
def baseEnd_1069437 : Nat := 183045070234145852173085

theorem tailTrace_1069437 : CollatzResearch.WordTrace tailWord_1069437 prefixEnd_1069437 183045070234145852173085 := by
  unfold tailWord_1069437
  simp only [CollatzResearch.WordTrace]
  refine ⟨39005571826619869143574565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26003714551079912762383043 39005571826619869143574565)
  ·
    refine ⟨7313544717491225464420231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39005571826619869143574565 7313544717491225464420231)
    ·
      refine ⟨10970317076236838196630347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7313544717491225464420231 10970317076236838196630347)
      ·
        refine ⟨16455475614355257294945521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10970317076236838196630347 16455475614355257294945521)
        ·
          refine ⟨12341606710766442971209141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16455475614355257294945521 12341606710766442971209141)
          ·
            refine ⟨1157025629134354028550857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12341606710766442971209141 1157025629134354028550857)
            ·
              refine ⟨867769221850765521413143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157025629134354028550857 867769221850765521413143)
              ·
                refine ⟨1301653832776148282119715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867769221850765521413143 1301653832776148282119715)
                ·
                  refine ⟨1952480749164222423179573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301653832776148282119715 1952480749164222423179573)
                  ·
                    refine ⟨183045070234145852173085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1952480749164222423179573 183045070234145852173085)
                    ·
                      rfl

theorem cell23_1069437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_1069437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069437 prefixEnd_1069437 := by exact prefixLift 1069437
  have htrace : WordTrace (prefixWord ++ tailWord_1069437) baseStart_1069437 baseEnd_1069437 := by
    simpa [prefixWord, tailWord_1069437, baseEnd_1069437] using wordTrace_append hprefix tailTrace_1069437
  have hstable : (prefixWord ++ tailWord_1069437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069437).length < 2 ^ (prefixWord ++ tailWord_1069437).sum := by decide
  have hdescent : baseEnd_1069437 < baseStart_1069437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069480 : List Nat := [2, 1, 6, 1, 1, 2, 1, 9]
def baseStart_1069480 : Nat := 118140960795 + 1069480 * 2 ^ 59
def prefixEnd_1069480 : Nat := 4983230072969 + 3 ^ 40 * 1069480 * 2
def baseEnd_1069480 : Nat := 20339158902614106973391

theorem tailTrace_1069480 : CollatzResearch.WordTrace tailWord_1069480 prefixEnd_1069480 20339158902614106973391 := by
  unfold tailWord_1069480
  simp only [CollatzResearch.WordTrace]
  refine ⟨19503570082732043743694947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26004760110309391658259929 19503570082732043743694947)
  ·
    refine ⟨29255355124098065615542421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19503570082732043743694947 29255355124098065615542421)
    ·
      refine ⟨1371344771442096825728551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29255355124098065615542421 1371344771442096825728551)
      ·
        refine ⟨2057017157163145238592827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371344771442096825728551 2057017157163145238592827)
        ·
          refine ⟨3085525735744717857889241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057017157163145238592827 3085525735744717857889241)
          ·
            refine ⟨2314144301808538393416931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085525735744717857889241 2314144301808538393416931)
            ·
              refine ⟨3471216452712807590125397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314144301808538393416931 3471216452712807590125397)
              ·
                refine ⟨20339158902614106973391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3471216452712807590125397 20339158902614106973391)
                ·
                  rfl

theorem cell23_1069480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 9].length) (baseStart_1069480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069480 prefixEnd_1069480 := by exact prefixLift 1069480
  have htrace : WordTrace (prefixWord ++ tailWord_1069480) baseStart_1069480 baseEnd_1069480 := by
    simpa [prefixWord, tailWord_1069480, baseEnd_1069480] using wordTrace_append hprefix tailTrace_1069480
  have hstable : (prefixWord ++ tailWord_1069480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069480).length < 2 ^ (prefixWord ++ tailWord_1069480).sum := by decide
  have hdescent : baseEnd_1069480 < baseStart_1069480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069490 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_1069490 : Nat := 118140960795 + 1069490 * 2 ^ 59
def prefixEnd_1069490 : Nat := 4983230072969 + 3 ^ 40 * 1069490 * 2
def baseEnd_1069490 : Nat := 549162425177125849156511

theorem tailTrace_1069490 : CollatzResearch.WordTrace tailWord_1069490 prefixEnd_1069490 549162425177125849156511 := by
  unfold tailWord_1069490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751876223856964798813481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26005003263618572796835949 9751876223856964798813481)
  ·
    refine ⟨7313907167892723599110111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9751876223856964798813481 7313907167892723599110111)
    ·
      refine ⟨10970860751839085398665167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7313907167892723599110111 10970860751839085398665167)
      ·
        refine ⟨16456291127758628097997751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10970860751839085398665167 16456291127758628097997751)
        ·
          refine ⟨24684436691637942146996627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16456291127758628097997751 24684436691637942146996627)
          ·
            refine ⟨37026655037456913220494941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24684436691637942146996627 37026655037456913220494941)
            ·
              refine ⟨13884995639046342457685603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37026655037456913220494941 13884995639046342457685603)
              ·
                refine ⟨20827493458569513686528405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13884995639046342457685603 20827493458569513686528405)
                ·
                  refine ⟨976288755870445954056019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20827493458569513686528405 976288755870445954056019)
                  ·
                    refine ⟨1464433133805668931084029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 976288755870445954056019 1464433133805668931084029)
                    ·
                      refine ⟨549162425177125849156511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1464433133805668931084029 549162425177125849156511)
                      ·
                        rfl

theorem cell23_1069490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_1069490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069490 prefixEnd_1069490 := by exact prefixLift 1069490
  have htrace : WordTrace (prefixWord ++ tailWord_1069490) baseStart_1069490 baseEnd_1069490 := by
    simpa [prefixWord, tailWord_1069490, baseEnd_1069490] using wordTrace_append hprefix tailTrace_1069490
  have hstable : (prefixWord ++ tailWord_1069490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069490).length < 2 ^ (prefixWord ++ tailWord_1069490).sum := by decide
  have hdescent : baseEnd_1069490 < baseStart_1069490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069508 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1069508 : Nat := 118140960795 + 1069508 * 2 ^ 59
def prefixEnd_1069508 : Nat := 4983230072969 + 3 ^ 40 * 1069508 * 2
def baseEnd_1069508 : Nat := 549171667828906778731429

theorem tailTrace_1069508 : CollatzResearch.WordTrace tailWord_1069508 prefixEnd_1069508 549171667828906778731429 := by
  unfold tailWord_1069508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504080704681324134704589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26005440939575098846272785 19504080704681324134704589)
  ·
    refine ⟨7314030264255496550514221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19504080704681324134704589 7314030264255496550514221)
    ·
      refine ⟨2742761349095811206442833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7314030264255496550514221 2742761349095811206442833)
      ·
        refine ⟨2057071011821858404832125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2742761349095811206442833 2057071011821858404832125)
        ·
          refine ⟨771401629433196901812047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2057071011821858404832125 771401629433196901812047)
          ·
            refine ⟨1157102444149795352718071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771401629433196901812047 1157102444149795352718071)
            ·
              refine ⟨1735653666224693029077107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157102444149795352718071 1735653666224693029077107)
              ·
                refine ⟨2603480499337039543615661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735653666224693029077107 2603480499337039543615661)
                ·
                  refine ⟨976305187251389828855873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2603480499337039543615661 976305187251389828855873)
                  ·
                    refine ⟨732228890438542371641905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 976305187251389828855873 732228890438542371641905)
                    ·
                      refine ⟨549171667828906778731429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732228890438542371641905 549171667828906778731429)
                      ·
                        rfl

theorem cell23_1069508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1069508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069508 prefixEnd_1069508 := by exact prefixLift 1069508
  have htrace : WordTrace (prefixWord ++ tailWord_1069508) baseStart_1069508 baseEnd_1069508 := by
    simpa [prefixWord, tailWord_1069508, baseEnd_1069508] using wordTrace_append hprefix tailTrace_1069508
  have hstable : (prefixWord ++ tailWord_1069508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069508).length < 2 ^ (prefixWord ++ tailWord_1069508).sum := by decide
  have hdescent : baseEnd_1069508 < baseStart_1069508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069524 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1069524 : Nat := 118140960795 + 1069524 * 2 ^ 59
def prefixEnd_1069524 : Nat := 4983230072969 + 3 ^ 40 * 1069524 * 2
def baseEnd_1069524 : Nat := 549179883519378716131355

theorem tailTrace_1069524 : CollatzResearch.WordTrace tailWord_1069524 prefixEnd_1069524 549179883519378716131355 := by
  unfold tailWord_1069524
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504372488652341500995813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26005829984869788667994417 19504372488652341500995813)
  ·
    refine ⟨3657069841622314031436715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19504372488652341500995813 3657069841622314031436715)
    ·
      refine ⟨5485604762433471047155073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3657069841622314031436715 5485604762433471047155073)
      ·
        refine ⟨4114203571825103285366305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5485604762433471047155073 4114203571825103285366305)
        ·
          refine ⟨3085652678868827464024729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4114203571825103285366305 3085652678868827464024729)
          ·
            refine ⟨2314239509151620598018547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085652678868827464024729 2314239509151620598018547)
            ·
              refine ⟨3471359263727430897027821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314239509151620598018547 3471359263727430897027821)
              ·
                refine ⟨1301759723897786586385433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3471359263727430897027821 1301759723897786586385433)
                ·
                  refine ⟨976319792923339939789075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301759723897786586385433 976319792923339939789075)
                  ·
                    refine ⟨1464479689385009909683613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 976319792923339939789075 1464479689385009909683613)
                    ·
                      refine ⟨549179883519378716131355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1464479689385009909683613 549179883519378716131355)
                      ·
                        rfl

theorem cell23_1069524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1069524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069524 prefixEnd_1069524 := by exact prefixLift 1069524
  have htrace : WordTrace (prefixWord ++ tailWord_1069524) baseStart_1069524 baseEnd_1069524 := by
    simpa [prefixWord, tailWord_1069524, baseEnd_1069524] using wordTrace_append hprefix tailTrace_1069524
  have hstable : (prefixWord ++ tailWord_1069524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069524).length < 2 ^ (prefixWord ++ tailWord_1069524).sum := by decide
  have hdescent : baseEnd_1069524 < baseStart_1069524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069550 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1069550 : Nat := 118140960795 + 1069550 * 2 ^ 59
def prefixEnd_1069550 : Nat := 4983230072969 + 3 ^ 40 * 1069550 * 2
def baseEnd_1069550 : Nat := 549193234016395614406235

theorem tailTrace_1069550 : CollatzResearch.WordTrace tailWord_1069550 prefixEnd_1069550 549193234016395614406235 := by
  unfold tailWord_1069550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876211659401311180304763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26006462183473659628292069 4876211659401311180304763)
  ·
    refine ⟨7314317489101966770457145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4876211659401311180304763 7314317489101966770457145)
    ·
      refine ⟨5485738116826475077842859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7314317489101966770457145 5485738116826475077842859)
      ·
        refine ⟨8228607175239712616764289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5485738116826475077842859 8228607175239712616764289)
        ·
          refine ⟨6171455381429784462573217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8228607175239712616764289 6171455381429784462573217)
          ·
            refine ⟨4628591536072338346929913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6171455381429784462573217 4628591536072338346929913)
            ·
              refine ⟨3471443652054253760197435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628591536072338346929913 3471443652054253760197435)
              ·
                refine ⟨5207165478081380640296153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471443652054253760197435 5207165478081380640296153)
                ·
                  refine ⟨3905374108561035480222115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207165478081380640296153 3905374108561035480222115)
                  ·
                    refine ⟨5858061162841553220333173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3905374108561035480222115 5858061162841553220333173)
                    ·
                      refine ⟨549193234016395614406235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5858061162841553220333173 549193234016395614406235)
                      ·
                        rfl

theorem cell23_1069550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1069550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069550 prefixEnd_1069550 := by exact prefixLift 1069550
  have htrace : WordTrace (prefixWord ++ tailWord_1069550) baseStart_1069550 baseEnd_1069550 := by
    simpa [prefixWord, tailWord_1069550, baseEnd_1069550] using wordTrace_append hprefix tailTrace_1069550
  have hstable : (prefixWord ++ tailWord_1069550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069550).length < 2 ^ (prefixWord ++ tailWord_1069550).sum := by decide
  have hdescent : baseEnd_1069550 < baseStart_1069550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069574 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1069574 : Nat := 118140960795 + 1069574 * 2 ^ 59
def prefixEnd_1069574 : Nat := 4983230072969 + 3 ^ 40 * 1069574 * 2
def baseEnd_1069574 : Nat := 183068519184034506835375

theorem tailTrace_1069574 : CollatzResearch.WordTrace tailWord_1069574 prefixEnd_1069574 183068519184034506835375 := by
  unfold tailWord_1069574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219080269597610673165993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26007045751415694360874517 1219080269597610673165993)
  ·
    refine ⟨914310202198208004874495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1219080269597610673165993 914310202198208004874495)
    ·
      refine ⟨1371465303297312007311743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914310202198208004874495 1371465303297312007311743)
      ·
        refine ⟨2057197954945968010967615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371465303297312007311743 2057197954945968010967615)
        ·
          refine ⟨3085796932418952016451423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057197954945968010967615 3085796932418952016451423)
          ·
            refine ⟨4628695398628428024677135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085796932418952016451423 4628695398628428024677135)
            ·
              refine ⟨6943043097942642037015703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628695398628428024677135 6943043097942642037015703)
              ·
                refine ⟨10414564646913963055523555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943043097942642037015703 10414564646913963055523555)
                ·
                  refine ⟨15621846970370944583285333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414564646913963055523555 15621846970370944583285333)
                  ·
                    refine ⟨183068519184034506835375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15621846970370944583285333 183068519184034506835375)
                    ·
                      rfl

theorem cell23_1069574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1069574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069574 prefixEnd_1069574 := by exact prefixLift 1069574
  have htrace : WordTrace (prefixWord ++ tailWord_1069574) baseStart_1069574 baseEnd_1069574 := by
    simpa [prefixWord, tailWord_1069574, baseEnd_1069574] using wordTrace_append hprefix tailTrace_1069574
  have hstable : (prefixWord ++ tailWord_1069574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069574).length < 2 ^ (prefixWord ++ tailWord_1069574).sum := by decide
  have hdescent : baseEnd_1069574 < baseStart_1069574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069580 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_1069580 : Nat := 118140960795 + 1069580 * 2 ^ 59
def prefixEnd_1069580 : Nat := 4983230072969 + 3 ^ 40 * 1069580 * 2
def baseEnd_1069580 : Nat := 549208638436030497031097

theorem tailTrace_1069580 : CollatzResearch.WordTrace tailWord_1069580 prefixEnd_1069580 549208638436030497031097 := by
  unfold tailWord_1069580
  simp only [CollatzResearch.WordTrace]
  refine ⟨19505393732550902283015097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26007191643401203044020129 19505393732550902283015097)
  ·
    refine ⟨14629045299413176712261323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19505393732550902283015097 14629045299413176712261323)
    ·
      refine ⟨21943567949119765068391985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14629045299413176712261323 21943567949119765068391985)
      ·
        refine ⟨16457675961839823801293989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21943567949119765068391985 16457675961839823801293989)
        ·
          refine ⟨3085814242844966962742623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16457675961839823801293989 3085814242844966962742623)
          ·
            refine ⟨4628721364267450444113935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085814242844966962742623 4628721364267450444113935)
            ·
              refine ⟨6943082046401175666170903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628721364267450444113935 6943082046401175666170903)
              ·
                refine ⟨10414623069601763499256355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943082046401175666170903 10414623069601763499256355)
                ·
                  refine ⟨15621934604402645248884533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414623069601763499256355 15621934604402645248884533)
                  ·
                    refine ⟨1464556369162747992082925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15621934604402645248884533 1464556369162747992082925)
                    ·
                      refine ⟨549208638436030497031097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1464556369162747992082925 549208638436030497031097)
                      ·
                        rfl

theorem cell23_1069580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_1069580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069580 prefixEnd_1069580 := by exact prefixLift 1069580
  have htrace : WordTrace (prefixWord ++ tailWord_1069580) baseStart_1069580 baseEnd_1069580 := by
    simpa [prefixWord, tailWord_1069580, baseEnd_1069580] using wordTrace_append hprefix tailTrace_1069580
  have hstable : (prefixWord ++ tailWord_1069580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069580).length < 2 ^ (prefixWord ++ tailWord_1069580).sum := by decide
  have hdescent : baseEnd_1069580 < baseStart_1069580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069581 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1069581 : Nat := 118140960795 + 1069581 * 2 ^ 59
def prefixEnd_1069581 : Nat := 4983230072969 + 3 ^ 40 * 1069581 * 2
def baseEnd_1069581 : Nat := 549209151916684993118593

theorem tailTrace_1069581 : CollatzResearch.WordTrace tailWord_1069581 prefixEnd_1069581 549209151916684993118593 := by
  unfold tailWord_1069581
  simp only [CollatzResearch.WordTrace]
  refine ⟨39010823938098181736816597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26007215958732121157877731 39010823938098181736816597)
  ·
    refine ⟨914316186049176134456639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39010823938098181736816597 914316186049176134456639)
    ·
      refine ⟨1371474279073764201684959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914316186049176134456639 1371474279073764201684959)
      ·
        refine ⟨2057211418610646302527439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371474279073764201684959 2057211418610646302527439)
        ·
          refine ⟨3085817127915969453791159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057211418610646302527439 3085817127915969453791159)
          ·
            refine ⟨4628725691873954180686739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085817127915969453791159 4628725691873954180686739)
            ·
              refine ⟨6943088537810931271030109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628725691873954180686739 6943088537810931271030109)
              ·
                refine ⟨2603658201679099226636291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6943088537810931271030109 2603658201679099226636291)
                ·
                  refine ⟨3905487302518648839954437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603658201679099226636291 3905487302518648839954437)
                  ·
                    refine ⟨732278869222246657491457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905487302518648839954437 732278869222246657491457)
                    ·
                      refine ⟨549209151916684993118593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732278869222246657491457 549209151916684993118593)
                      ·
                        rfl

theorem cell23_1069581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1069581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069581 prefixEnd_1069581 := by exact prefixLift 1069581
  have htrace : WordTrace (prefixWord ++ tailWord_1069581) baseStart_1069581 baseEnd_1069581 := by
    simpa [prefixWord, tailWord_1069581, baseEnd_1069581] using wordTrace_append hprefix tailTrace_1069581
  have hstable : (prefixWord ++ tailWord_1069581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069581).length < 2 ^ (prefixWord ++ tailWord_1069581).sum := by decide
  have hdescent : baseEnd_1069581 < baseStart_1069581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069583 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 6, 5]
def baseStart_1069583 : Nat := 118140960795 + 1069583 * 2 ^ 59
def prefixEnd_1069583 : Nat := 4983230072969 + 3 ^ 40 * 1069583 * 2
def baseEnd_1069583 : Nat := 183070059625997995097861

theorem tailTrace_1069583 : CollatzResearch.WordTrace tailWord_1069583 prefixEnd_1069583 183070059625997995097861 := by
  unfold tailWord_1069583
  simp only [CollatzResearch.WordTrace]
  refine ⟨39010896884090936078389403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26007264589393957385592935 39010896884090936078389403)
  ·
    refine ⟨58516345326136404117584105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39010896884090936078389403 58516345326136404117584105)
    ·
      refine ⟨43887258994602303088188079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58516345326136404117584105 43887258994602303088188079)
      ·
        refine ⟨65830888491903454632282119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43887258994602303088188079 65830888491903454632282119)
        ·
          refine ⟨98746332737855181948423179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65830888491903454632282119 98746332737855181948423179)
          ·
            refine ⟨148119499106782772922634769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98746332737855181948423179 148119499106782772922634769)
            ·
              refine ⟨111089624330087079691976077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148119499106782772922634769 111089624330087079691976077)
              ·
                refine ⟨41658609123782654884491029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111089624330087079691976077 41658609123782654884491029)
                ·
                  refine ⟨1952747302677311947710517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41658609123782654884491029 1952747302677311947710517)
                  ·
                    refine ⟨183070059625997995097861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1952747302677311947710517 183070059625997995097861)
                    ·
                      rfl

theorem cell23_1069583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_1069583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069583 prefixEnd_1069583 := by exact prefixLift 1069583
  have htrace : WordTrace (prefixWord ++ tailWord_1069583) baseStart_1069583 baseEnd_1069583 := by
    simpa [prefixWord, tailWord_1069583, baseEnd_1069583] using wordTrace_append hprefix tailTrace_1069583
  have hstable : (prefixWord ++ tailWord_1069583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069583).length < 2 ^ (prefixWord ++ tailWord_1069583).sum := by decide
  have hdescent : baseEnd_1069583 < baseStart_1069583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069637 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 2, 4, 2]
def baseStart_1069637 : Nat := 118140960795 + 1069637 * 2 ^ 59
def prefixEnd_1069637 : Nat := 4983230072969 + 3 ^ 40 * 1069637 * 2
def baseEnd_1069637 : Nat := 549237906833336774018335

theorem tailTrace_1069637 : CollatzResearch.WordTrace tailWord_1069637 prefixEnd_1069637 549237906833336774018335 := by
  unfold tailWord_1069637
  simp only [CollatzResearch.WordTrace]
  refine ⟨39012866425895303300855165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26008577617263535533903443 39012866425895303300855165)
  ·
    refine ⟨14629824909710738737820687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39012866425895303300855165 14629824909710738737820687)
    ·
      refine ⟨21944737364566108106731031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14629824909710738737820687 21944737364566108106731031)
      ·
        refine ⟨32917106046849162160096547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21944737364566108106731031 32917106046849162160096547)
        ·
          refine ⟨49375659070273743240144821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32917106046849162160096547 49375659070273743240144821)
          ·
            refine ⟨4628968037838163428763577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49375659070273743240144821 4628968037838163428763577)
            ·
              refine ⟨3471726028378622571572683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628968037838163428763577 3471726028378622571572683)
              ·
                refine ⟨5207589042567933857359025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471726028378622571572683 5207589042567933857359025)
                ·
                  refine ⟨3905691781925950393019269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207589042567933857359025 3905691781925950393019269)
                  ·
                    refine ⟨732317209111115698691113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905691781925950393019269 732317209111115698691113)
                    ·
                      refine ⟨549237906833336774018335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732317209111115698691113 549237906833336774018335)
                      ·
                        rfl

theorem cell23_1069637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_1069637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069637 prefixEnd_1069637 := by exact prefixLift 1069637
  have htrace : WordTrace (prefixWord ++ tailWord_1069637) baseStart_1069637 baseEnd_1069637 := by
    simpa [prefixWord, tailWord_1069637, baseEnd_1069637] using wordTrace_append hprefix tailTrace_1069637
  have hstable : (prefixWord ++ tailWord_1069637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069637).length < 2 ^ (prefixWord ++ tailWord_1069637).sum := by decide
  have hdescent : baseEnd_1069637 < baseStart_1069637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069650 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1069650 : Nat := 118140960795 + 1069650 * 2 ^ 59
def prefixEnd_1069650 : Nat := 4983230072969 + 3 ^ 40 * 1069650 * 2
def baseEnd_1069650 : Nat := 549244582081845223155775

theorem tailTrace_1069650 : CollatzResearch.WordTrace tailWord_1069650 prefixEnd_1069650 549244582081845223155775 := by
  unfold tailWord_1069650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9753335143712051630269601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26008893716565471014052269 9753335143712051630269601)
  ·
    refine ⟨7315001357784038722702201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9753335143712051630269601 7315001357784038722702201)
    ·
      refine ⟨5486251018338029042026651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7315001357784038722702201 5486251018338029042026651)
      ·
        refine ⟨8229376527507043563039977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5486251018338029042026651 8229376527507043563039977)
        ·
          refine ⟨6172032395630282672279983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8229376527507043563039977 6172032395630282672279983)
          ·
            refine ⟨9258048593445424008419975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6172032395630282672279983 9258048593445424008419975)
            ·
              refine ⟨13887072890168136012629963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9258048593445424008419975 13887072890168136012629963)
              ·
                refine ⟨20830609335252204018944945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13887072890168136012629963 20830609335252204018944945)
                ·
                  refine ⟨15622957001439153014208709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20830609335252204018944945 15622957001439153014208709)
                  ·
                    refine ⟨2929304437769841190164133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15622957001439153014208709 2929304437769841190164133)
                    ·
                      refine ⟨549244582081845223155775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2929304437769841190164133 549244582081845223155775)
                      ·
                        rfl

theorem cell23_1069650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1069650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069650 prefixEnd_1069650 := by exact prefixLift 1069650
  have htrace : WordTrace (prefixWord ++ tailWord_1069650) baseStart_1069650 baseEnd_1069650 := by
    simpa [prefixWord, tailWord_1069650, baseEnd_1069650] using wordTrace_append hprefix tailTrace_1069650
  have hstable : (prefixWord ++ tailWord_1069650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069650).length < 2 ^ (prefixWord ++ tailWord_1069650).sum := by decide
  have hdescent : baseEnd_1069650 < baseStart_1069650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069664 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 1, 4]
def baseStart_1069664 : Nat := 118140960795 + 1069664 * 2 ^ 59
def prefixEnd_1069664 : Nat := 4983230072969 + 3 ^ 40 * 1069664 * 2
def baseEnd_1069664 : Nat := 183083923603669389460237

theorem tailTrace_1069664 : CollatzResearch.WordTrace tailWord_1069664 prefixEnd_1069664 183083923603669389460237 := by
  unfold tailWord_1069664
  simp only [CollatzResearch.WordTrace]
  refine ⟨19506925598398743456044023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26009234131198324608058697 19506925598398743456044023)
  ·
    refine ⟨29260388397598115184066035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19506925598398743456044023 29260388397598115184066035)
    ·
      refine ⟨43890582596397172776099053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29260388397598115184066035 43890582596397172776099053)
      ·
        refine ⟨16458968473648939791037145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43890582596397172776099053 16458968473648939791037145)
        ·
          refine ⟨12344226355236704843277859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16458968473648939791037145 12344226355236704843277859)
          ·
            refine ⟨18516339532855057264916789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12344226355236704843277859 18516339532855057264916789)
            ·
              refine ⟨1735906831205161618585949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18516339532855057264916789 1735906831205161618585949)
              ·
                refine ⟨650965061701935606969731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1735906831205161618585949 650965061701935606969731)
                ·
                  refine ⟨976447592552903410454597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650965061701935606969731 976447592552903410454597)
                  ·
                    refine ⟨183083923603669389460237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976447592552903410454597 183083923603669389460237)
                    ·
                      rfl

theorem cell23_1069664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 4].length) (baseStart_1069664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069664 prefixEnd_1069664 := by exact prefixLift 1069664
  have htrace : WordTrace (prefixWord ++ tailWord_1069664) baseStart_1069664 baseEnd_1069664 := by
    simpa [prefixWord, tailWord_1069664, baseEnd_1069664] using wordTrace_append hprefix tailTrace_1069664
  have hstable : (prefixWord ++ tailWord_1069664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069664).length < 2 ^ (prefixWord ++ tailWord_1069664).sum := by decide
  have hdescent : baseEnd_1069664 < baseStart_1069664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069737 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 2, 4]
def baseStart_1069737 : Nat := 118140960795 + 1069737 * 2 ^ 59
def prefixEnd_1069737 : Nat := 4983230072969 + 3 ^ 40 * 1069737 * 2
def baseEnd_1069737 : Nat := 183096418299595460922625

theorem tailTrace_1069737 : CollatzResearch.WordTrace tailWord_1069737 prefixEnd_1069737 183096418299595460922625 := by
  unfold tailWord_1069737
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016513725533020379495465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26011009150355346919663643 39016513725533020379495465)
  ·
    refine ⟨29262385294149765284621599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39016513725533020379495465 29262385294149765284621599)
    ·
      refine ⟨43893577941224647926932399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29262385294149765284621599 43893577941224647926932399)
      ·
        refine ⟨65840366911836971890398599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43893577941224647926932399 65840366911836971890398599)
        ·
          refine ⟨98760550367755457835597899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65840366911836971890398599 98760550367755457835597899)
          ·
            refine ⟨148140825551633186753396849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98760550367755457835597899 148140825551633186753396849)
            ·
              refine ⟨111105619163724890065047637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148140825551633186753396849 111105619163724890065047637)
              ·
                refine ⟨1302018974574901055449777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 111105619163724890065047637 1302018974574901055449777)
                ·
                  refine ⟨976514230931175791587333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302018974574901055449777 976514230931175791587333)
                  ·
                    refine ⟨183096418299595460922625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976514230931175791587333 183096418299595460922625)
                    ·
                      rfl

theorem cell23_1069737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_1069737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069737 prefixEnd_1069737 := by exact prefixLift 1069737
  have htrace : WordTrace (prefixWord ++ tailWord_1069737) baseStart_1069737 baseEnd_1069737 := by
    simpa [prefixWord, tailWord_1069737, baseEnd_1069737] using wordTrace_append hprefix tailTrace_1069737
  have hstable : (prefixWord ++ tailWord_1069737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069737).length < 2 ^ (prefixWord ++ tailWord_1069737).sum := by decide
  have hdescent : baseEnd_1069737 < baseStart_1069737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069744 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 3, 2, 2]
def baseStart_1069744 : Nat := 118140960795 + 1069744 * 2 ^ 59
def prefixEnd_1069744 : Nat := 4983230072969 + 3 ^ 40 * 1069744 * 2
def baseEnd_1069744 : Nat := 549292849263367855380343

theorem tailTrace_1069744 : CollatzResearch.WordTrace tailWord_1069744 prefixEnd_1069744 549292849263367855380343 := by
  unfold tailWord_1069744
  simp only [CollatzResearch.WordTrace]
  refine ⟨19508384518253830287500143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26011179357671773716666857 19508384518253830287500143)
  ·
    refine ⟨29262576777380745431250215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19508384518253830287500143 29262576777380745431250215)
    ·
      refine ⟨43893865166071118146875323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29262576777380745431250215 43893865166071118146875323)
      ·
        refine ⟨65840797749106677220312985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43893865166071118146875323 65840797749106677220312985)
        ·
          refine ⟨49380598311830007915234739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65840797749106677220312985 49380598311830007915234739)
          ·
            refine ⟨74070897467745011872852109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49380598311830007915234739 74070897467745011872852109)
            ·
              refine ⟨27776586550404379452319541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74070897467745011872852109 27776586550404379452319541)
              ·
                refine ⟨2604054989100410573654957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27776586550404379452319541 2604054989100410573654957)
                ·
                  refine ⟨976520620912653965120609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2604054989100410573654957 976520620912653965120609)
                  ·
                    refine ⟨732390465684490473840457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 976520620912653965120609 732390465684490473840457)
                    ·
                      refine ⟨549292849263367855380343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732390465684490473840457 549292849263367855380343)
                      ·
                        rfl

theorem cell23_1069744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 2, 2].length) (baseStart_1069744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069744 prefixEnd_1069744 := by exact prefixLift 1069744
  have htrace : WordTrace (prefixWord ++ tailWord_1069744) baseStart_1069744 baseEnd_1069744 := by
    simpa [prefixWord, tailWord_1069744, baseEnd_1069744] using wordTrace_append hprefix tailTrace_1069744
  have hstable : (prefixWord ++ tailWord_1069744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069744).length < 2 ^ (prefixWord ++ tailWord_1069744).sum := by decide
  have hdescent : baseEnd_1069744 < baseStart_1069744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069747 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 3]
def baseStart_1069747 : Nat := 118140960795 + 1069747 * 2 ^ 59
def prefixEnd_1069747 : Nat := 4983230072969 + 3 ^ 40 * 1069747 * 2
def baseEnd_1069747 : Nat := 549294389705331343642829

theorem tailTrace_1069747 : CollatzResearch.WordTrace tailWord_1069747 prefixEnd_1069747 549294389705331343642829 := by
  unfold tailWord_1069747
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016878455496792087359495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26011252303664528058239663 39016878455496792087359495)
  ·
    refine ⟨58525317683245188131039243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39016878455496792087359495 58525317683245188131039243)
    ·
      refine ⟨87787976524867782196558865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58525317683245188131039243 87787976524867782196558865)
      ·
        refine ⟨65840982393650836647419149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87787976524867782196558865 65840982393650836647419149)
        ·
          refine ⟨24690368397619063742782181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65840982393650836647419149 24690368397619063742782181)
          ·
            refine ⟨4629444074553574451771659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24690368397619063742782181 4629444074553574451771659)
            ·
              refine ⟨6944166111830361677657489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629444074553574451771659 6944166111830361677657489)
              ·
                refine ⟨5208124583872771258243117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944166111830361677657489 5208124583872771258243117)
                ·
                  refine ⟨1953046718952289221841169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5208124583872771258243117 1953046718952289221841169)
                  ·
                    refine ⟨1464785039214216916380877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953046718952289221841169 1464785039214216916380877)
                    ·
                      refine ⟨549294389705331343642829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1464785039214216916380877 549294389705331343642829)
                      ·
                        rfl

theorem cell23_1069747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_1069747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069747 prefixEnd_1069747 := by exact prefixLift 1069747
  have htrace : WordTrace (prefixWord ++ tailWord_1069747) baseStart_1069747 baseEnd_1069747 := by
    simpa [prefixWord, tailWord_1069747, baseEnd_1069747] using wordTrace_append hprefix tailTrace_1069747
  have hstable : (prefixWord ++ tailWord_1069747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069747).length < 2 ^ (prefixWord ++ tailWord_1069747).sum := by decide
  have hdescent : baseEnd_1069747 < baseStart_1069747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069757 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1069757 : Nat := 118140960795 + 1069757 * 2 ^ 59
def prefixEnd_1069757 : Nat := 4983230072969 + 3 ^ 40 * 1069757 * 2
def baseEnd_1069757 : Nat := 549299524511876304517783

theorem tailTrace_1069757 : CollatzResearch.WordTrace tailWord_1069757 prefixEnd_1069757 549299524511876304517783 := by
  unfold tailWord_1069757
  simp only [CollatzResearch.WordTrace]
  refine ⟨39017243185460563795223525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26011495456973709196815683 39017243185460563795223525)
  ·
    refine ⟨7315733097273855711604411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39017243185460563795223525 7315733097273855711604411)
    ·
      refine ⟨10973599645910783567406617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7315733097273855711604411 10973599645910783567406617)
      ·
        refine ⟨8230199734433087675554963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10973599645910783567406617 8230199734433087675554963)
        ·
          refine ⟨12345299601649631513332445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8230199734433087675554963 12345299601649631513332445)
          ·
            refine ⟨4629487350618611817499667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12345299601649631513332445 4629487350618611817499667)
            ·
              refine ⟨6944231025927917726249501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629487350618611817499667 6944231025927917726249501)
              ·
                refine ⟨2604086634722969147343563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6944231025927917726249501 2604086634722969147343563)
                ·
                  refine ⟨3906129952084453721015345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604086634722969147343563 3906129952084453721015345)
                  ·
                    refine ⟨2929597464063340290761509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3906129952084453721015345 2929597464063340290761509)
                    ·
                      refine ⟨549299524511876304517783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2929597464063340290761509 549299524511876304517783)
                      ·
                        rfl

theorem cell23_1069757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1069757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069757 prefixEnd_1069757 := by exact prefixLift 1069757
  have htrace : WordTrace (prefixWord ++ tailWord_1069757) baseStart_1069757 baseEnd_1069757 := by
    simpa [prefixWord, tailWord_1069757, baseEnd_1069757] using wordTrace_append hprefix tailTrace_1069757
  have hstable : (prefixWord ++ tailWord_1069757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069757).length < 2 ^ (prefixWord ++ tailWord_1069757).sum := by decide
  have hdescent : baseEnd_1069757 < baseStart_1069757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069764 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1069764 : Nat := 118140960795 + 1069764 * 2 ^ 59
def prefixEnd_1069764 : Nat := 4983230072969 + 3 ^ 40 * 1069764 * 2
def baseEnd_1069764 : Nat := 549303118876457777130251

theorem tailTrace_1069764 : CollatzResearch.WordTrace tailWord_1069764 prefixEnd_1069764 549303118876457777130251 := by
  unfold tailWord_1069764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19508749248217601995364173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26011665664290135993818897 19508749248217601995364173)
  ·
    refine ⟨7315780968081600748261565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19508749248217601995364173 7315780968081600748261565)
    ·
      refine ⟨2743417863030600280598087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7315780968081600748261565 2743417863030600280598087)
      ·
        refine ⟨4115126794545900420897131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743417863030600280598087 4115126794545900420897131)
        ·
          refine ⟨6172690191818850631345697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115126794545900420897131 6172690191818850631345697)
          ·
            refine ⟨4629517643864137973509273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6172690191818850631345697 4629517643864137973509273)
            ·
              refine ⟨3472138232898103480131955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4629517643864137973509273 3472138232898103480131955)
              ·
                refine ⟨5208207349347155220197933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472138232898103480131955 5208207349347155220197933)
                ·
                  refine ⟨1953077756005183207574225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5208207349347155220197933 1953077756005183207574225)
                  ·
                    refine ⟨1464808317003887405680669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953077756005183207574225 1464808317003887405680669)
                    ·
                      refine ⟨549303118876457777130251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1464808317003887405680669 549303118876457777130251)
                      ·
                        rfl

theorem cell23_1069764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1069764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069764 prefixEnd_1069764 := by exact prefixLift 1069764
  have htrace : WordTrace (prefixWord ++ tailWord_1069764) baseStart_1069764 baseEnd_1069764 := by
    simpa [prefixWord, tailWord_1069764, baseEnd_1069764] using wordTrace_append hprefix tailTrace_1069764
  have hstable : (prefixWord ++ tailWord_1069764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069764).length < 2 ^ (prefixWord ++ tailWord_1069764).sum := by decide
  have hdescent : baseEnd_1069764 < baseStart_1069764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069777 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_1069777 : Nat := 118140960795 + 1069777 * 2 ^ 59
def prefixEnd_1069777 : Nat := 4983230072969 + 3 ^ 40 * 1069777 * 2
def baseEnd_1069777 : Nat := 549309794124966226267691

theorem tailTrace_1069777 : CollatzResearch.WordTrace tailWord_1069777 prefixEnd_1069777 549309794124966226267691 := by
  unfold tailWord_1069777
  simp only [CollatzResearch.WordTrace]
  refine ⟨39017972645388107210951585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26011981763592071473967723 39017972645388107210951585)
  ·
    refine ⟨29263479484041080408213689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39017972645388107210951585 29263479484041080408213689)
    ·
      refine ⟨21947609613030810306160267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29263479484041080408213689 21947609613030810306160267)
      ·
        refine ⟨32921414419546215459240401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21947609613030810306160267 32921414419546215459240401)
        ·
          refine ⟨24691060814659661594430301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32921414419546215459240401 24691060814659661594430301)
          ·
            refine ⟨9259147805497373097911363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24691060814659661594430301 9259147805497373097911363)
            ·
              refine ⟨13888721708246059646867045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9259147805497373097911363 13888721708246059646867045)
              ·
                refine ⟨2604135320296136183787571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13888721708246059646867045 2604135320296136183787571)
                ·
                  refine ⟨3906202980444204275681357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604135320296136183787571 3906202980444204275681357)
                  ·
                    refine ⟨1464826117666576603380509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3906202980444204275681357 1464826117666576603380509)
                    ·
                      refine ⟨549309794124966226267691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1464826117666576603380509 549309794124966226267691)
                      ·
                        rfl

theorem cell23_1069777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_1069777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069777 prefixEnd_1069777 := by exact prefixLift 1069777
  have htrace : WordTrace (prefixWord ++ tailWord_1069777) baseStart_1069777 baseEnd_1069777 := by
    simpa [prefixWord, tailWord_1069777, baseEnd_1069777] using wordTrace_append hprefix tailTrace_1069777
  have hstable : (prefixWord ++ tailWord_1069777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069777).length < 2 ^ (prefixWord ++ tailWord_1069777).sum := by decide
  have hdescent : baseEnd_1069777 < baseStart_1069777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069778 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1069778 : Nat := 118140960795 + 1069778 * 2 ^ 59
def prefixEnd_1069778 : Nat := 4983230072969 + 3 ^ 40 * 1069778 * 2
def baseEnd_1069778 : Nat := 549310307605620722355187

theorem tailTrace_1069778 : CollatzResearch.WordTrace tailWord_1069778 prefixEnd_1069778 549310307605620722355187 := by
  unfold tailWord_1069778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9754502279596121095434497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26012006078922989587825325 9754502279596121095434497)
  ·
    refine ⟨7315876709697090821575873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9754502279596121095434497 7315876709697090821575873)
    ·
      refine ⟨5486907532272818116181905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7315876709697090821575873 5486907532272818116181905)
      ·
        refine ⟨4115180649204613587136429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5486907532272818116181905 4115180649204613587136429)
        ·
          refine ⟨1543192743451730095176161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4115180649204613587136429 1543192743451730095176161)
          ·
            refine ⟨1157394557588797571382121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543192743451730095176161 1157394557588797571382121)
            ·
              refine ⟨868045918191598178536591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157394557588797571382121 868045918191598178536591)
              ·
                refine ⟨1302068877287397267804887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868045918191598178536591 1302068877287397267804887)
                ·
                  refine ⟨1953103315931095901707331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302068877287397267804887 1953103315931095901707331)
                  ·
                    refine ⟨2929654973896643852560997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953103315931095901707331 2929654973896643852560997)
                    ·
                      refine ⟨549310307605620722355187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2929654973896643852560997 549310307605620722355187)
                      ·
                        rfl

theorem cell23_1069778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1069778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069778 prefixEnd_1069778 := by exact prefixLift 1069778
  have htrace : WordTrace (prefixWord ++ tailWord_1069778) baseStart_1069778 baseEnd_1069778 := by
    simpa [prefixWord, tailWord_1069778, baseEnd_1069778] using wordTrace_append hprefix tailTrace_1069778
  have hstable : (prefixWord ++ tailWord_1069778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069778).length < 2 ^ (prefixWord ++ tailWord_1069778).sum := by decide
  have hdescent : baseEnd_1069778 < baseStart_1069778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069788 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1069788 : Nat := 118140960795 + 1069788 * 2 ^ 59
def prefixEnd_1069788 : Nat := 4983230072969 + 3 ^ 40 * 1069788 * 2
def baseEnd_1069788 : Nat := 183105147470721894410047

theorem tailTrace_1069788 : CollatzResearch.WordTrace tailWord_1069788 prefixEnd_1069788 183105147470721894410047 := by
  unfold tailWord_1069788
  simp only [CollatzResearch.WordTrace]
  refine ⟨19509186924174128044801009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26012249232232170726401345 19509186924174128044801009)
  ·
    refine ⟨14631890193130596033600757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19509186924174128044801009 14631890193130596033600757)
    ·
      refine ⟨1371739705605993378150071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14631890193130596033600757 1371739705605993378150071)
      ·
        refine ⟨2057609558408990067225107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371739705605993378150071 2057609558408990067225107)
        ·
          refine ⟨3086414337613485100837661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057609558408990067225107 3086414337613485100837661)
          ·
            refine ⟨1157405376605056912814123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3086414337613485100837661 1157405376605056912814123)
            ·
              refine ⟨1736108064907585369221185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157405376605056912814123 1736108064907585369221185)
              ·
                refine ⟨1302081048680689026915889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736108064907585369221185 1302081048680689026915889)
                ·
                  refine ⟨976560786510516770186917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302081048680689026915889 976560786510516770186917)
                  ·
                    refine ⟨183105147470721894410047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976560786510516770186917 183105147470721894410047)
                    ·
                      rfl

theorem cell23_1069788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1069788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069788 prefixEnd_1069788 := by exact prefixLift 1069788
  have htrace : WordTrace (prefixWord ++ tailWord_1069788) baseStart_1069788 baseEnd_1069788 := by
    simpa [prefixWord, tailWord_1069788, baseEnd_1069788] using wordTrace_append hprefix tailTrace_1069788
  have hstable : (prefixWord ++ tailWord_1069788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069788).length < 2 ^ (prefixWord ++ tailWord_1069788).sum := by decide
  have hdescent : baseEnd_1069788 < baseStart_1069788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069821 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_1069821 : Nat := 118140960795 + 1069821 * 2 ^ 59
def prefixEnd_1069821 : Nat := 4983230072969 + 3 ^ 40 * 1069821 * 2
def baseEnd_1069821 : Nat := 549332387273764054117489

theorem tailTrace_1069821 : CollatzResearch.WordTrace tailWord_1069821 prefixEnd_1069821 549332387273764054117489 := by
  unfold tailWord_1069821
  simp only [CollatzResearch.WordTrace]
  refine ⟨39019577457228702725553317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26013051638152468483702211 39019577457228702725553317)
  ·
    refine ⟨7316170773230381761041247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39019577457228702725553317 7316170773230381761041247)
    ·
      refine ⟨10974256159845572641561871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7316170773230381761041247 10974256159845572641561871)
      ·
        refine ⟨16461384239768358962342807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10974256159845572641561871 16461384239768358962342807)
        ·
          refine ⟨24692076359652538443514211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16461384239768358962342807 24692076359652538443514211)
          ·
            refine ⟨37038114539478807665271317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24692076359652538443514211 37038114539478807665271317)
            ·
              refine ⟨1736161619038069109309593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37038114539478807665271317 1736161619038069109309593)
              ·
                refine ⟨1302121214278551831982195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736161619038069109309593 1302121214278551831982195)
                ·
                  refine ⟨1953181821417827747973293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302121214278551831982195 1953181821417827747973293)
                  ·
                    refine ⟨732443183031685405489985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953181821417827747973293 732443183031685405489985)
                    ·
                      refine ⟨549332387273764054117489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732443183031685405489985 549332387273764054117489)
                      ·
                        rfl

theorem cell23_1069821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_1069821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069821 prefixEnd_1069821 := by exact prefixLift 1069821
  have htrace : WordTrace (prefixWord ++ tailWord_1069821) baseStart_1069821 baseEnd_1069821 := by
    simpa [prefixWord, tailWord_1069821, baseEnd_1069821] using wordTrace_append hprefix tailTrace_1069821
  have hstable : (prefixWord ++ tailWord_1069821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069821).length < 2 ^ (prefixWord ++ tailWord_1069821).sum := by decide
  have hdescent : baseEnd_1069821 < baseStart_1069821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069834 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_1069834 : Nat := 118140960795 + 1069834 * 2 ^ 59
def prefixEnd_1069834 : Nat := 4983230072969 + 3 ^ 40 * 1069834 * 2
def baseEnd_1069834 : Nat := 549339062522272503254929

theorem tailTrace_1069834 : CollatzResearch.WordTrace tailWord_1069834 prefixEnd_1069834 549339062522272503254929 := by
  unfold tailWord_1069834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755012901545401486444139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26013367737454403963851037 9755012901545401486444139)
  ·
    refine ⟨14632519352318102229666209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9755012901545401486444139 14632519352318102229666209)
    ·
      refine ⟨10974389514238576672249657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14632519352318102229666209 10974389514238576672249657)
      ·
        refine ⟨8230792135678932504187243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10974389514238576672249657 8230792135678932504187243)
        ·
          refine ⟨12346188203518398756280865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8230792135678932504187243 12346188203518398756280865)
          ·
            refine ⟨9259641152638799067210649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12346188203518398756280865 9259641152638799067210649)
            ·
              refine ⟨6944730864479099300407987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9259641152638799067210649 6944730864479099300407987)
              ·
                refine ⟨10417096296718648950611981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6944730864479099300407987 10417096296718648950611981)
                ·
                  refine ⟨3906411111269493356479493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10417096296718648950611981 3906411111269493356479493)
                  ·
                    refine ⟨732452083363030004339905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906411111269493356479493 732452083363030004339905)
                    ·
                      refine ⟨549339062522272503254929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732452083363030004339905 549339062522272503254929)
                      ·
                        rfl

theorem cell23_1069834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_1069834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069834 prefixEnd_1069834 := by exact prefixLift 1069834
  have htrace : WordTrace (prefixWord ++ tailWord_1069834) baseStart_1069834 baseEnd_1069834 := by
    simpa [prefixWord, tailWord_1069834, baseEnd_1069834] using wordTrace_append hprefix tailTrace_1069834
  have hstable : (prefixWord ++ tailWord_1069834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069834).length < 2 ^ (prefixWord ++ tailWord_1069834).sum := by decide
  have hdescent : baseEnd_1069834 < baseStart_1069834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069897 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_1069897 : Nat := 118140960795 + 1069897 * 2 ^ 59
def prefixEnd_1069897 : Nat := 4983230072969 + 3 ^ 40 * 1069897 * 2
def baseEnd_1069897 : Nat := 549371411803505756767139

theorem tailTrace_1069897 : CollatzResearch.WordTrace tailWord_1069897 prefixEnd_1069897 549371411803505756767139 := by
  unfold tailWord_1069897
  simp only [CollatzResearch.WordTrace]
  refine ⟨39022349404953367705319945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26014899603302245136879963 39022349404953367705319945)
  ·
    refine ⟨29266762053715025778989959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39022349404953367705319945 29266762053715025778989959)
    ·
      refine ⟨43900143080572538668484939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29266762053715025778989959 43900143080572538668484939)
      ·
        refine ⟨65850214620858808002727409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43900143080572538668484939 65850214620858808002727409)
        ·
          refine ⟨49387660965644106002045557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65850214620858808002727409 49387660965644106002045557)
          ·
            refine ⟨4630093215529134937691771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49387660965644106002045557 4630093215529134937691771)
            ·
              refine ⟨6945139823293702406537657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630093215529134937691771 6945139823293702406537657)
              ·
                refine ⟨5208854867470276804903243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945139823293702406537657 5208854867470276804903243)
                ·
                  refine ⟨7813282301205415207354865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208854867470276804903243 7813282301205415207354865)
                  ·
                    refine ⟨5859961725904061405516149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7813282301205415207354865 5859961725904061405516149)
                    ·
                      refine ⟨549371411803505756767139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5859961725904061405516149 549371411803505756767139)
                      ·
                        rfl

theorem cell23_1069897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_1069897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069897 prefixEnd_1069897 := by exact prefixLift 1069897
  have htrace : WordTrace (prefixWord ++ tailWord_1069897) baseStart_1069897 baseEnd_1069897 := by
    simpa [prefixWord, tailWord_1069897, baseEnd_1069897] using wordTrace_append hprefix tailTrace_1069897
  have hstable : (prefixWord ++ tailWord_1069897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069897).length < 2 ^ (prefixWord ++ tailWord_1069897).sum := by decide
  have hdescent : baseEnd_1069897 < baseStart_1069897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069941 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1069941 : Nat := 118140960795 + 1069941 * 2 ^ 59
def prefixEnd_1069941 : Nat := 4983230072969 + 3 ^ 40 * 1069941 * 2
def baseEnd_1069941 : Nat := 549394004952303584616937

theorem tailTrace_1069941 : CollatzResearch.WordTrace tailWord_1069941 prefixEnd_1069941 549394004952303584616937 := by
  unfold tailWord_1069941
  simp only [CollatzResearch.WordTrace]
  refine ⟨39023954216793963219921677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26015969477862642146614451 39023954216793963219921677)
  ·
    refine ⟨14633982831297736207470629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39023954216793963219921677 14633982831297736207470629)
    ·
      refine ⟨2743871780868325538900743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14633982831297736207470629 2743871780868325538900743)
      ·
        refine ⟨4115807671302488308351115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743871780868325538900743 4115807671302488308351115)
        ·
          refine ⟨6173711506953732462526673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115807671302488308351115 6173711506953732462526673)
          ·
            refine ⟨4630283630215299346895005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6173711506953732462526673 4630283630215299346895005)
            ·
              refine ⟨1736356361330737255085627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4630283630215299346895005 1736356361330737255085627)
              ·
                refine ⟨2604534541996105882628441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736356361330737255085627 2604534541996105882628441)
                ·
                  refine ⟨1953400906497079411971331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2604534541996105882628441 1953400906497079411971331)
                  ·
                    refine ⟨2930101359745619117956997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953400906497079411971331 2930101359745619117956997)
                    ·
                      refine ⟨549394004952303584616937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2930101359745619117956997 549394004952303584616937)
                      ·
                        rfl

theorem cell23_1069941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1069941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069941 prefixEnd_1069941 := by exact prefixLift 1069941
  have htrace : WordTrace (prefixWord ++ tailWord_1069941) baseStart_1069941 baseEnd_1069941 := by
    simpa [prefixWord, tailWord_1069941, baseEnd_1069941] using wordTrace_append hprefix tailTrace_1069941
  have hstable : (prefixWord ++ tailWord_1069941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069941).length < 2 ^ (prefixWord ++ tailWord_1069941).sum := by decide
  have hdescent : baseEnd_1069941 < baseStart_1069941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069944 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_1069944 : Nat := 118140960795 + 1069944 * 2 ^ 59
def prefixEnd_1069944 : Nat := 4983230072969 + 3 ^ 40 * 1069944 * 2
def baseEnd_1069944 : Nat := 549395545394267072879423

theorem tailTrace_1069944 : CollatzResearch.WordTrace tailWord_1069944 prefixEnd_1069944 549395545394267072879423 := by
  unfold tailWord_1069944
  simp only [CollatzResearch.WordTrace]
  refine ⟨19512031817891547366140443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26016042423855396488187257 19512031817891547366140443)
  ·
    refine ⟨29268047726837321049210665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19512031817891547366140443 29268047726837321049210665)
    ·
      refine ⟨21951035795127990786907999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29268047726837321049210665 21951035795127990786907999)
      ·
        refine ⟨32926553692691986180361999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21951035795127990786907999 32926553692691986180361999)
        ·
          refine ⟨49389830539037979270542999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32926553692691986180361999 49389830539037979270542999)
          ·
            refine ⟨74084745808556968905814499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49389830539037979270542999 74084745808556968905814499)
            ·
              refine ⟨111127118712835453358721749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74084745808556968905814499 111127118712835453358721749)
              ·
                refine ⟨2604541844832080938095041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111127118712835453358721749 2604541844832080938095041)
                ·
                  refine ⟨1953406383624060703571281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2604541844832080938095041 1953406383624060703571281)
                  ·
                    refine ⟨1465054787718045527678461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953406383624060703571281 1465054787718045527678461)
                    ·
                      refine ⟨549395545394267072879423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1465054787718045527678461 549395545394267072879423)
                      ·
                        rfl

theorem cell23_1069944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_1069944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069944 prefixEnd_1069944 := by exact prefixLift 1069944
  have htrace : WordTrace (prefixWord ++ tailWord_1069944) baseStart_1069944 baseEnd_1069944 := by
    simpa [prefixWord, tailWord_1069944, baseEnd_1069944] using wordTrace_append hprefix tailTrace_1069944
  have hstable : (prefixWord ++ tailWord_1069944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069944).length < 2 ^ (prefixWord ++ tailWord_1069944).sum := by decide
  have hdescent : baseEnd_1069944 < baseStart_1069944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069951 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 1, 4]
def baseStart_1069951 : Nat := 118140960795 + 1069951 * 2 ^ 59
def prefixEnd_1069951 : Nat := 4983230072969 + 3 ^ 40 * 1069951 * 2
def baseEnd_1069951 : Nat := 183133046586282848497297

theorem tailTrace_1069951 : CollatzResearch.WordTrace tailWord_1069951 prefixEnd_1069951 183133046586282848497297 := by
  unfold tailWord_1069951
  simp only [CollatzResearch.WordTrace]
  refine ⟨39024318946757734927785707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26016212631171823285190471 39024318946757734927785707)
  ·
    refine ⟨58536478420136602391678561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39024318946757734927785707 58536478420136602391678561)
    ·
      refine ⟨43902358815102451793758921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58536478420136602391678561 43902358815102451793758921)
      ·
        refine ⟨32926769111326838845319191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43902358815102451793758921 32926769111326838845319191)
        ·
          refine ⟨49390153666990258267978787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32926769111326838845319191 49390153666990258267978787)
          ·
            refine ⟨74085230500485387401968181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49390153666990258267978787 74085230500485387401968181)
            ·
              refine ⟨6945490359420505068934517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74085230500485387401968181 6945490359420505068934517)
              ·
                refine ⟨651139721195672350212611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6945490359420505068934517 651139721195672350212611)
                ·
                  refine ⟨976709581793508525318917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651139721195672350212611 976709581793508525318917)
                  ·
                    refine ⟨183133046586282848497297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976709581793508525318917 183133046586282848497297)
                    ·
                      rfl

theorem cell23_1069951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 4].length) (baseStart_1069951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069951 prefixEnd_1069951 := by exact prefixLift 1069951
  have htrace : WordTrace (prefixWord ++ tailWord_1069951) baseStart_1069951 baseEnd_1069951 := by
    simpa [prefixWord, tailWord_1069951, baseEnd_1069951] using wordTrace_append hprefix tailTrace_1069951
  have hstable : (prefixWord ++ tailWord_1069951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069951).length < 2 ^ (prefixWord ++ tailWord_1069951).sum := by decide
  have hdescent : baseEnd_1069951 < baseStart_1069951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069964 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 6]
def baseStart_1069964 : Nat := 118140960795 + 1069964 * 2 ^ 59
def prefixEnd_1069964 : Nat := 4983230072969 + 3 ^ 40 * 1069964 * 2
def baseEnd_1069964 : Nat := 61045090556372999403259

theorem tailTrace_1069964 : CollatzResearch.WordTrace tailWord_1069964 prefixEnd_1069964 61045090556372999403259 := by
  unfold tailWord_1069964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19512396547855319074004473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26016528730473758765339297 19512396547855319074004473)
  ·
    refine ⟨14634297410891489305503355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19512396547855319074004473 14634297410891489305503355)
    ·
      refine ⟨21951446116337233958255033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14634297410891489305503355 21951446116337233958255033)
      ·
        refine ⟨16463584587252925468691275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21951446116337233958255033 16463584587252925468691275)
        ·
          refine ⟨24695376880879388203036913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16463584587252925468691275 24695376880879388203036913)
          ·
            refine ⟨18521532660659541152277685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24695376880879388203036913 18521532660659541152277685)
            ·
              refine ⟨1736393686936831983026033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18521532660659541152277685 1736393686936831983026033)
              ·
                refine ⟨1302295265202623987269525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736393686936831983026033 1302295265202623987269525)
                ·
                  refine ⟨61045090556372999403259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1302295265202623987269525 61045090556372999403259)
                  ·
                    rfl

theorem cell23_1069964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_1069964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069964 prefixEnd_1069964 := by exact prefixLift 1069964
  have htrace : WordTrace (prefixWord ++ tailWord_1069964) baseStart_1069964 baseEnd_1069964 := by
    simpa [prefixWord, tailWord_1069964, baseEnd_1069964] using wordTrace_append hprefix tailTrace_1069964
  have hstable : (prefixWord ++ tailWord_1069964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069964).length < 2 ^ (prefixWord ++ tailWord_1069964).sum := by decide
  have hdescent : baseEnd_1069964 < baseStart_1069964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069981 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 6]
def baseStart_1069981 : Nat := 118140960795 + 1069981 * 2 ^ 59
def prefixEnd_1069981 : Nat := 4983230072969 + 3 ^ 40 * 1069981 * 2
def baseEnd_1069981 : Nat := 61046060464275936457417

theorem tailTrace_1069981 : CollatzResearch.WordTrace tailWord_1069981 prefixEnd_1069981 61046060464275936457417 := by
  unfold tailWord_1069981
  simp only [CollatzResearch.WordTrace]
  refine ⟨39025413136649050051377797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26016942091099366700918531 39025413136649050051377797)
  ·
    refine ⟨7317264963121696884633337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39025413136649050051377797 7317264963121696884633337)
    ·
      refine ⟨5487948722341272663475003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7317264963121696884633337 5487948722341272663475003)
      ·
        refine ⟨8231923083511908995212505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5487948722341272663475003 8231923083511908995212505)
        ·
          refine ⟨6173942312633931746409379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8231923083511908995212505 6173942312633931746409379)
          ·
            refine ⟨9260913468950897619614069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6173942312633931746409379 9260913468950897619614069)
            ·
              refine ⟨868210637714146651838819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9260913468950897619614069 868210637714146651838819)
              ·
                refine ⟨1302315956571219977758229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868210637714146651838819 1302315956571219977758229)
                ·
                  refine ⟨61046060464275936457417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1302315956571219977758229 61046060464275936457417)
                  ·
                    rfl

theorem cell23_1069981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_1069981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069981 prefixEnd_1069981 := by exact prefixLift 1069981
  have htrace : WordTrace (prefixWord ++ tailWord_1069981) baseStart_1069981 baseEnd_1069981 := by
    simpa [prefixWord, tailWord_1069981, baseEnd_1069981] using wordTrace_append hprefix tailTrace_1069981
  have hstable : (prefixWord ++ tailWord_1069981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069981).length < 2 ^ (prefixWord ++ tailWord_1069981).sum := by decide
  have hdescent : baseEnd_1069981 < baseStart_1069981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069987 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1069987 : Nat := 118140960795 + 1069987 * 2 ^ 59
def prefixEnd_1069987 : Nat := 4983230072969 + 3 ^ 40 * 1069987 * 2
def baseEnd_1069987 : Nat := 549417625062410404641725

theorem tailTrace_1069987 : CollatzResearch.WordTrace tailWord_1069987 prefixEnd_1069987 549417625062410404641725 := by
  unfold tailWord_1069987
  simp only [CollatzResearch.WordTrace]
  refine ⟨39025631974627313076096215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26017087983084875384064143 39025631974627313076096215)
  ·
    refine ⟨58538447961940969614144323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39025631974627313076096215 58538447961940969614144323)
    ·
      refine ⟨87807671942911454421216485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58538447961940969614144323 87807671942911454421216485)
      ·
        refine ⟨16463938489295897703978091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87807671942911454421216485 16463938489295897703978091)
        ·
          refine ⟨24695907733943846555967137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16463938489295897703978091 24695907733943846555967137)
          ·
            refine ⟨18521930800457884916975353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24695907733943846555967137 18521930800457884916975353)
            ·
              refine ⟨13891448100343413687731515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18521930800457884916975353 13891448100343413687731515)
              ·
                refine ⟨20837172150515120531597273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13891448100343413687731515 20837172150515120531597273)
                ·
                  refine ⟨15627879112886340398697955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20837172150515120531597273 15627879112886340398697955)
                  ·
                    refine ⟨23441818669329510598046933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15627879112886340398697955 23441818669329510598046933)
                    ·
                      refine ⟨549417625062410404641725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23441818669329510598046933 549417625062410404641725)
                      ·
                        rfl

theorem cell23_1069987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1069987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1069987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1069987 prefixEnd_1069987 := by exact prefixLift 1069987
  have htrace : WordTrace (prefixWord ++ tailWord_1069987) baseStart_1069987 baseEnd_1069987 := by
    simpa [prefixWord, tailWord_1069987, baseEnd_1069987] using wordTrace_append hprefix tailTrace_1069987
  have hstable : (prefixWord ++ tailWord_1069987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069987).length < 2 ^ (prefixWord ++ tailWord_1069987).sum := by decide
  have hdescent : baseEnd_1069987 < baseStart_1069987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070051 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1070051 : Nat := 118140960795 + 1070051 * 2 ^ 59
def prefixEnd_1070051 : Nat := 4983230072969 + 3 ^ 40 * 1070051 * 2
def baseEnd_1070051 : Nat := 549450487824298154241431

theorem tailTrace_1070051 : CollatzResearch.WordTrace tailWord_1070051 prefixEnd_1070051 549450487824298154241431 := by
  unfold tailWord_1070051
  simp only [CollatzResearch.WordTrace]
  refine ⟨39027966246395452006426007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26018644164263634670950671 39027966246395452006426007)
  ·
    refine ⟨58541949369593178009639011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39027966246395452006426007 58541949369593178009639011)
    ·
      refine ⟨87812924054389767014458517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58541949369593178009639011 87812924054389767014458517)
      ·
        refine ⟨4116230815049520328802743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87812924054389767014458517 4116230815049520328802743)
        ·
          refine ⟨6174346222574280493204115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116230815049520328802743 6174346222574280493204115)
          ·
            refine ⟨9261519333861420739806173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6174346222574280493204115 9261519333861420739806173)
            ·
              refine ⟨3473069750198032777427315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9261519333861420739806173 3473069750198032777427315)
              ·
                refine ⟨5209604625297049166140973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473069750198032777427315 5209604625297049166140973)
                ·
                  refine ⟨1953601734486393437302865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5209604625297049166140973 1953601734486393437302865)
                  ·
                    refine ⟨1465201300864795077977149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953601734486393437302865 1465201300864795077977149)
                    ·
                      refine ⟨549450487824298154241431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1465201300864795077977149 549450487824298154241431)
                      ·
                        rfl

theorem cell23_1070051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1070051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070051 prefixEnd_1070051 := by exact prefixLift 1070051
  have htrace : WordTrace (prefixWord ++ tailWord_1070051) baseStart_1070051 baseEnd_1070051 := by
    simpa [prefixWord, tailWord_1070051, baseEnd_1070051] using wordTrace_append hprefix tailTrace_1070051
  have hstable : (prefixWord ++ tailWord_1070051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070051).length < 2 ^ (prefixWord ++ tailWord_1070051).sum := by decide
  have hdescent : baseEnd_1070051 < baseStart_1070051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070124 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_1070124 : Nat := 118140960795 + 1070124 * 2 ^ 59
def prefixEnd_1070124 : Nat := 4983230072969 + 3 ^ 40 * 1070124 * 2
def baseEnd_1070124 : Nat := 549487971912076368628595

theorem tailTrace_1070124 : CollatzResearch.WordTrace tailWord_1070124 prefixEnd_1070124 549487971912076368628595 := by
  unfold tailWord_1070124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19515314387565492736916713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26020419183420656982555617 19515314387565492736916713)
  ·
    refine ⟨14636485790674119552687535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19515314387565492736916713 14636485790674119552687535)
    ·
      refine ⟨21954728686011179329031303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14636485790674119552687535 21954728686011179329031303)
      ·
        refine ⟨32932093029016768993546955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21954728686011179329031303 32932093029016768993546955)
        ·
          refine ⟨49398139543525153490320433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32932093029016768993546955 49398139543525153490320433)
          ·
            refine ⟨37048604657643865117740325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49398139543525153490320433 37048604657643865117740325)
            ·
              refine ⟨6946613373308224709576311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37048604657643865117740325 6946613373308224709576311)
              ·
                refine ⟨10419920059962337064364467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6946613373308224709576311 10419920059962337064364467)
                ·
                  refine ⟨15629880089943505596546701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10419920059962337064364467 15629880089943505596546701)
                  ·
                    refine ⟨5861205033728814598705013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15629880089943505596546701 5861205033728814598705013)
                    ·
                      refine ⟨549487971912076368628595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5861205033728814598705013 549487971912076368628595)
                      ·
                        rfl

theorem cell23_1070124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_1070124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070124 prefixEnd_1070124 := by exact prefixLift 1070124
  have htrace : WordTrace (prefixWord ++ tailWord_1070124) baseStart_1070124 baseEnd_1070124 := by
    simpa [prefixWord, tailWord_1070124, baseEnd_1070124] using wordTrace_append hprefix tailTrace_1070124
  have hstable : (prefixWord ++ tailWord_1070124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070124).length < 2 ^ (prefixWord ++ tailWord_1070124).sum := by decide
  have hdescent : baseEnd_1070124 < baseStart_1070124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070132 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1070132 : Nat := 118140960795 + 1070132 * 2 ^ 59
def prefixEnd_1070132 : Nat := 4983230072969 + 3 ^ 40 * 1070132 * 2
def baseEnd_1070132 : Nat := 549492079757312337328559

theorem tailTrace_1070132 : CollatzResearch.WordTrace tailWord_1070132 prefixEnd_1070132 549492079757312337328559 := by
  unfold tailWord_1070132
  simp only [CollatzResearch.WordTrace]
  refine ⟨19515460279551001420062325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26020613706068001893416433 19515460279551001420062325)
  ·
    refine ⟨1829574401207906383130843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19515460279551001420062325 1829574401207906383130843)
    ·
      refine ⟨2744361601811859574696265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1829574401207906383130843 2744361601811859574696265)
      ·
        refine ⟨2058271201358894681022199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2744361601811859574696265 2058271201358894681022199)
        ·
          refine ⟨3087406802038342021533299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058271201358894681022199 3087406802038342021533299)
          ·
            refine ⟨4631110203057513032299949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087406802038342021533299 4631110203057513032299949)
            ·
              refine ⟨1736666326146567387112481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4631110203057513032299949 1736666326146567387112481)
              ·
                refine ⟨1302499744609925540334361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736666326146567387112481 1302499744609925540334361)
                ·
                  refine ⟨976874808457444155250771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302499744609925540334361 976874808457444155250771)
                  ·
                    refine ⟨1465312212686166232876157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 976874808457444155250771 1465312212686166232876157)
                    ·
                      refine ⟨549492079757312337328559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1465312212686166232876157 549492079757312337328559)
                      ·
                        rfl

theorem cell23_1070132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1070132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070132 prefixEnd_1070132 := by exact prefixLift 1070132
  have htrace : WordTrace (prefixWord ++ tailWord_1070132) baseStart_1070132 baseEnd_1070132 := by
    simpa [prefixWord, tailWord_1070132, baseEnd_1070132] using wordTrace_append hprefix tailTrace_1070132
  have hstable : (prefixWord ++ tailWord_1070132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070132).length < 2 ^ (prefixWord ++ tailWord_1070132).sum := by decide
  have hdescent : baseEnd_1070132 < baseStart_1070132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070151 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1070151 : Nat := 118140960795 + 1070151 * 2 ^ 59
def prefixEnd_1070151 : Nat := 4983230072969 + 3 ^ 40 * 1070151 * 2
def baseEnd_1070151 : Nat := 549501835889747762990971

theorem tailTrace_1070151 : CollatzResearch.WordTrace tailWord_1070151 prefixEnd_1070151 549501835889747762990971 := by
  unfold tailWord_1070151
  simp only [CollatzResearch.WordTrace]
  refine ⟨39031613546033169085066307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26021075697355446056710871 39031613546033169085066307)
  ·
    refine ⟨58547420319049753627599461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39031613546033169085066307 58547420319049753627599461)
    ·
      refine ⟨10977641309821828805174899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58547420319049753627599461 10977641309821828805174899)
      ·
        refine ⟨16466461964732743207762349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10977641309821828805174899 16466461964732743207762349)
        ·
          refine ⟨6174923236774778702910881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16466461964732743207762349 6174923236774778702910881)
          ·
            refine ⟨4631192427581084027183161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6174923236774778702910881 4631192427581084027183161)
            ·
              refine ⟨3473394320685813020387371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631192427581084027183161 3473394320685813020387371)
              ·
                refine ⟨5210091481028719530581057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473394320685813020387371 5210091481028719530581057)
                ·
                  refine ⟨3907568610771539647935793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5210091481028719530581057 3907568610771539647935793)
                  ·
                    refine ⟨2930676458078654735951845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3907568610771539647935793 2930676458078654735951845)
                    ·
                      refine ⟨549501835889747762990971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2930676458078654735951845 549501835889747762990971)
                      ·
                        rfl

theorem cell23_1070151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1070151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070151 prefixEnd_1070151 := by exact prefixLift 1070151
  have htrace : WordTrace (prefixWord ++ tailWord_1070151) baseStart_1070151 baseEnd_1070151 := by
    simpa [prefixWord, tailWord_1070151, baseEnd_1070151] using wordTrace_append hprefix tailTrace_1070151
  have hstable : (prefixWord ++ tailWord_1070151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070151).length < 2 ^ (prefixWord ++ tailWord_1070151).sum := by decide
  have hdescent : baseEnd_1070151 < baseStart_1070151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070191 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 2, 5]
def baseStart_1070191 : Nat := 118140960795 + 1070191 * 2 ^ 59
def prefixEnd_1070191 : Nat := 4983230072969 + 3 ^ 40 * 1070191 * 2
def baseEnd_1070191 : Nat := 183174125038642535496929

theorem tailTrace_1070191 : CollatzResearch.WordTrace tailWord_1070191 prefixEnd_1070191 183174125038642535496929 := by
  unfold tailWord_1070191
  simp only [CollatzResearch.WordTrace]
  refine ⟨39033072465888255916522427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26022048310592170611014951 39033072465888255916522427)
  ·
    refine ⟨58549608698832383874783641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39033072465888255916522427 58549608698832383874783641)
    ·
      refine ⟨43912206524124287906087731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58549608698832383874783641 43912206524124287906087731)
      ·
        refine ⟨65868309786186431859131597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43912206524124287906087731 65868309786186431859131597)
        ·
          refine ⟨24700616169819911947174349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65868309786186431859131597 24700616169819911947174349)
          ·
            refine ⟨9262731063682466980190381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24700616169819911947174349 9262731063682466980190381)
            ·
              refine ⟨3473524148880925117571393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9262731063682466980190381 3473524148880925117571393)
              ·
                refine ⟨2605143111660693838178545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473524148880925117571393 2605143111660693838178545)
                ·
                  refine ⟨1953857333745520378633909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605143111660693838178545 1953857333745520378633909)
                  ·
                    refine ⟨183174125038642535496929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1953857333745520378633909 183174125038642535496929)
                    ·
                      rfl

theorem cell23_1070191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_1070191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070191 prefixEnd_1070191 := by exact prefixLift 1070191
  have htrace : WordTrace (prefixWord ++ tailWord_1070191) baseStart_1070191 baseEnd_1070191 := by
    simpa [prefixWord, tailWord_1070191, baseEnd_1070191] using wordTrace_append hprefix tailTrace_1070191
  have hstable : (prefixWord ++ tailWord_1070191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070191).length < 2 ^ (prefixWord ++ tailWord_1070191).sum := by decide
  have hdescent : baseEnd_1070191 < baseStart_1070191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070211 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 4]
def baseStart_1070211 : Nat := 118140960795 + 1070211 * 2 ^ 59
def prefixEnd_1070211 : Nat := 4983230072969 + 3 ^ 40 * 1070211 * 2
def baseEnd_1070211 : Nat := 549532644729017528240695

theorem tailTrace_1070211 : CollatzResearch.WordTrace tailWord_1070211 prefixEnd_1070211 549532644729017528240695 := by
  unfold tailWord_1070211
  simp only [CollatzResearch.WordTrace]
  refine ⟨39033801925815799332250487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26022534617210532888166991 39033801925815799332250487)
  ·
    refine ⟨58550702888723698998375731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39033801925815799332250487 58550702888723698998375731)
    ·
      refine ⟨87826054333085548497563597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58550702888723698998375731 87826054333085548497563597)
      ·
        refine ⟨32934770374907080686586349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87826054333085548497563597 32934770374907080686586349)
        ·
          refine ⟨12350538890590155257469881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32934770374907080686586349 12350538890590155257469881)
          ·
            refine ⟨9262904167942616443102411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12350538890590155257469881 9262904167942616443102411)
            ·
              refine ⟨13894356251913924664653617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9262904167942616443102411 13894356251913924664653617)
              ·
                refine ⟨10420767188935443498490213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13894356251913924664653617 10420767188935443498490213)
                ·
                  refine ⟨1953893847925395655966915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10420767188935443498490213 1953893847925395655966915)
                  ·
                    refine ⟨2930840771888093483950373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953893847925395655966915 2930840771888093483950373)
                    ·
                      refine ⟨549532644729017528240695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2930840771888093483950373 549532644729017528240695)
                      ·
                        rfl

theorem cell23_1070211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_1070211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070211 prefixEnd_1070211 := by exact prefixLift 1070211
  have htrace : WordTrace (prefixWord ++ tailWord_1070211) baseStart_1070211 baseEnd_1070211 := by
    simpa [prefixWord, tailWord_1070211, baseEnd_1070211] using wordTrace_append hprefix tailTrace_1070211
  have hstable : (prefixWord ++ tailWord_1070211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070211).length < 2 ^ (prefixWord ++ tailWord_1070211).sum := by decide
  have hdescent : baseEnd_1070211 < baseStart_1070211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070241 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1070241 : Nat := 118140960795 + 1070241 * 2 ^ 59
def prefixEnd_1070241 : Nat := 4983230072969 + 3 ^ 40 * 1070241 * 2
def baseEnd_1070241 : Nat := 549548049148652410865557

theorem tailTrace_1070241 : CollatzResearch.WordTrace tailWord_1070241 prefixEnd_1070241 549548049148652410865557 := by
  unfold tailWord_1070241
  simp only [CollatzResearch.WordTrace]
  refine ⟨39034896115707114455842577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26023264077138076303895051 39034896115707114455842577)
  ·
    refine ⟨29276172086780335841881933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39034896115707114455842577 29276172086780335841881933)
    ·
      refine ⟨10978564532542625940705725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29276172086780335841881933 10978564532542625940705725)
      ·
        refine ⟨4116961699703484727764647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10978564532542625940705725 4116961699703484727764647)
        ·
          refine ⟨6175442549555227091646971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116961699703484727764647 6175442549555227091646971)
          ·
            refine ⟨9263163824332840637470457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175442549555227091646971 9263163824332840637470457)
            ·
              refine ⟨6947372868249630478102843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9263163824332840637470457 6947372868249630478102843)
              ·
                refine ⟨10421059302374445717154265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6947372868249630478102843 10421059302374445717154265)
                ·
                  refine ⟨7815794476780834287865699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10421059302374445717154265 7815794476780834287865699)
                  ·
                    refine ⟨11723691715171251431798549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7815794476780834287865699 11723691715171251431798549)
                    ·
                      refine ⟨549548049148652410865557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11723691715171251431798549 549548049148652410865557)
                      ·
                        rfl

theorem cell23_1070241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1070241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070241 prefixEnd_1070241 := by exact prefixLift 1070241
  have htrace : WordTrace (prefixWord ++ tailWord_1070241) baseStart_1070241 baseEnd_1070241 := by
    simpa [prefixWord, tailWord_1070241, baseEnd_1070241] using wordTrace_append hprefix tailTrace_1070241
  have hstable : (prefixWord ++ tailWord_1070241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070241).length < 2 ^ (prefixWord ++ tailWord_1070241).sum := by decide
  have hdescent : baseEnd_1070241 < baseStart_1070241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070268 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 6]
def baseStart_1070268 : Nat := 118140960795 + 1070268 * 2 ^ 59
def prefixEnd_1070268 : Nat := 4983230072969 + 3 ^ 40 * 1070268 * 2
def baseEnd_1070268 : Nat := 61062434791813756136437

theorem tailTrace_1070268 : CollatzResearch.WordTrace tailWord_1070268 prefixEnd_1070268 61062434791813756136437 := by
  unfold tailWord_1070268
  simp only [CollatzResearch.WordTrace]
  refine ⟨19517940443304649033537729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26023920591072865378050305 19517940443304649033537729)
  ·
    refine ⟨14638455332478486775153297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19517940443304649033537729 14638455332478486775153297)
    ·
      refine ⟨10978841499358865081364973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14638455332478486775153297 10978841499358865081364973)
      ·
        refine ⟨4117065562259574405511865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10978841499358865081364973 4117065562259574405511865)
        ·
          refine ⟨3087799171694680804133899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4117065562259574405511865 3087799171694680804133899)
          ·
            refine ⟨4631698757542021206200849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087799171694680804133899 4631698757542021206200849)
            ·
              refine ⟨3473774068156515904650637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631698757542021206200849 3473774068156515904650637)
              ·
                refine ⟨1302665275558693464243989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3473774068156515904650637 1302665275558693464243989)
                ·
                  refine ⟨61062434791813756136437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1302665275558693464243989 61062434791813756136437)
                  ·
                    rfl

theorem cell23_1070268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_1070268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070268 prefixEnd_1070268 := by exact prefixLift 1070268
  have htrace : WordTrace (prefixWord ++ tailWord_1070268) baseStart_1070268 baseEnd_1070268 := by
    simpa [prefixWord, tailWord_1070268, baseEnd_1070268] using wordTrace_append hprefix tailTrace_1070268
  have hstable : (prefixWord ++ tailWord_1070268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070268).length < 2 ^ (prefixWord ++ tailWord_1070268).sum := by decide
  have hdescent : baseEnd_1070268 < baseStart_1070268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070312 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_1070312 : Nat := 118140960795 + 1070312 * 2 ^ 59
def prefixEnd_1070312 : Nat := 4983230072969 + 3 ^ 40 * 1070312 * 2
def baseEnd_1070312 : Nat := 549584506275121633077731

theorem tailTrace_1070312 : CollatzResearch.WordTrace tailWord_1070312 prefixEnd_1070312 549584506275121633077731 := by
  unfold tailWord_1070312
  simp only [CollatzResearch.WordTrace]
  refine ⟨19518742849224946790838595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26024990465633262387784793 19518742849224946790838595)
  ·
    refine ⟨29278114273837420186257893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19518742849224946790838595 29278114273837420186257893)
    ·
      refine ⟨5489646426344516284923355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29278114273837420186257893 5489646426344516284923355)
      ·
        refine ⟨8234469639516774427385033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5489646426344516284923355 8234469639516774427385033)
        ·
          refine ⟨6175852229637580820538775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8234469639516774427385033 6175852229637580820538775)
          ·
            refine ⟨9263778344456371230808163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175852229637580820538775 9263778344456371230808163)
            ·
              refine ⟨13895667516684556846212245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9263778344456371230808163 13895667516684556846212245)
              ·
                refine ⟨651359414844588602166199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13895667516684556846212245 651359414844588602166199)
                ·
                  refine ⟨977039122266882903249299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651359414844588602166199 977039122266882903249299)
                  ·
                    refine ⟨1465558683400324354873949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 977039122266882903249299 1465558683400324354873949)
                    ·
                      refine ⟨549584506275121633077731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1465558683400324354873949 549584506275121633077731)
                      ·
                        rfl

theorem cell23_1070312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_1070312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070312 prefixEnd_1070312 := by exact prefixLift 1070312
  have htrace : WordTrace (prefixWord ++ tailWord_1070312) baseStart_1070312 baseEnd_1070312 := by
    simpa [prefixWord, tailWord_1070312, baseEnd_1070312] using wordTrace_append hprefix tailTrace_1070312
  have hstable : (prefixWord ++ tailWord_1070312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070312).length < 2 ^ (prefixWord ++ tailWord_1070312).sum := by decide
  have hdescent : baseEnd_1070312 < baseStart_1070312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070318 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1070318 : Nat := 118140960795 + 1070318 * 2 ^ 59
def prefixEnd_1070318 : Nat := 4983230072969 + 3 ^ 40 * 1070318 * 2
def baseEnd_1070318 : Nat := 549587587159048609602703

theorem tailTrace_1070318 : CollatzResearch.WordTrace tailWord_1070318 prefixEnd_1070318 549587587159048609602703 := by
  unfold tailWord_1070318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879713067053519575799451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26025136357618771070930405 4879713067053519575799451)
  ·
    refine ⟨7319569600580279363699177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4879713067053519575799451 7319569600580279363699177)
    ·
      refine ⟨5489677200435209522774383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7319569600580279363699177 5489677200435209522774383)
      ·
        refine ⟨8234515800652814284161575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5489677200435209522774383 8234515800652814284161575)
        ·
          refine ⟨12351773700979221426242363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8234515800652814284161575 12351773700979221426242363)
          ·
            refine ⟨18527660551468832139363545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12351773700979221426242363 18527660551468832139363545)
            ·
              refine ⟨13895745413601624104522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18527660551468832139363545 13895745413601624104522659)
              ·
                refine ⟨20843618120402436156783989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13895745413601624104522659 20843618120402436156783989)
                ·
                  refine ⟨1954089198787728389698499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20843618120402436156783989 1954089198787728389698499)
                  ·
                    refine ⟨2931133798181592584547749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954089198787728389698499 2931133798181592584547749)
                    ·
                      refine ⟨549587587159048609602703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2931133798181592584547749 549587587159048609602703)
                      ·
                        rfl

theorem cell23_1070318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1070318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070318 prefixEnd_1070318 := by exact prefixLift 1070318
  have htrace : WordTrace (prefixWord ++ tailWord_1070318) baseStart_1070318 baseEnd_1070318 := by
    simpa [prefixWord, tailWord_1070318, baseEnd_1070318] using wordTrace_append hprefix tailTrace_1070318
  have hstable : (prefixWord ++ tailWord_1070318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070318).length < 2 ^ (prefixWord ++ tailWord_1070318).sum := by decide
  have hdescent : baseEnd_1070318 < baseStart_1070318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070335 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 4]
def baseStart_1070335 : Nat := 118140960795 + 1070335 * 2 ^ 59
def prefixEnd_1070335 : Nat := 4983230072969 + 3 ^ 40 * 1070335 * 2
def baseEnd_1070335 : Nat := 549596316330175043090125

theorem tailTrace_1070335 : CollatzResearch.WordTrace tailWord_1070335 prefixEnd_1070335 549596316330175043090125 := by
  unfold tailWord_1070335
  simp only [CollatzResearch.WordTrace]
  refine ⟨39038324577366568509764459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26025549718244379006509639 39038324577366568509764459)
  ·
    refine ⟨58557486866049852764646689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39038324577366568509764459 58557486866049852764646689)
    ·
      refine ⟨43918115149537389573485017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58557486866049852764646689 43918115149537389573485017)
      ·
        refine ⟨32938586362153042180113763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43918115149537389573485017 32938586362153042180113763)
        ·
          refine ⟨49407879543229563270170645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32938586362153042180113763 49407879543229563270170645)
          ·
            refine ⟨2315994353588885778289249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49407879543229563270170645 2315994353588885778289249)
            ·
              refine ⟨1736995765191664333716937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315994353588885778289249 1736995765191664333716937)
              ·
                refine ⟨1302746823893748250287703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736995765191664333716937 1302746823893748250287703)
                ·
                  refine ⟨1954120235840622375431555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302746823893748250287703 1954120235840622375431555)
                  ·
                    refine ⟨2931180353760933563147333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954120235840622375431555 2931180353760933563147333)
                    ·
                      refine ⟨549596316330175043090125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2931180353760933563147333 549596316330175043090125)
                      ·
                        rfl

theorem cell23_1070335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_1070335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070335 prefixEnd_1070335 := by exact prefixLift 1070335
  have htrace : WordTrace (prefixWord ++ tailWord_1070335) baseStart_1070335 baseEnd_1070335 := by
    simpa [prefixWord, tailWord_1070335, baseEnd_1070335] using wordTrace_append hprefix tailTrace_1070335
  have hstable : (prefixWord ++ tailWord_1070335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070335).length < 2 ^ (prefixWord ++ tailWord_1070335).sum := by decide
  have hdescent : baseEnd_1070335 < baseStart_1070335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070341 : List Nat := [1, 3, 1, 1, 2, 1, 5, 9]
def baseStart_1070341 : Nat := 118140960795 + 1070341 * 2 ^ 59
def prefixEnd_1070341 : Nat := 4983230072969 + 3 ^ 40 * 1070341 * 2
def baseEnd_1070341 : Nat := 20355533230151926652411

theorem tailTrace_1070341 : CollatzResearch.WordTrace tailWord_1070341 prefixEnd_1070341 20355533230151926652411 := by
  unfold tailWord_1070341
  simp only [CollatzResearch.WordTrace]
  refine ⟨39038543415344831534482877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26025695610229887689655251 39038543415344831534482877)
  ·
    refine ⟨14639453780754311825431079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39038543415344831534482877 14639453780754311825431079)
    ·
      refine ⟨21959180671131467738146619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14639453780754311825431079 21959180671131467738146619)
      ·
        refine ⟨32938771006697201607219929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21959180671131467738146619 32938771006697201607219929)
        ·
          refine ⟨24704078255022901205414947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32938771006697201607219929 24704078255022901205414947)
          ·
            refine ⟨37056117382534351808122421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24704078255022901205414947 37056117382534351808122421)
            ·
              refine ⟨3474011004612595482011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37056117382534351808122421 3474011004612595482011477)
              ·
                refine ⟨20355533230151926652411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3474011004612595482011477 20355533230151926652411)
                ·
                  rfl

theorem cell23_1070341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 9].length) (baseStart_1070341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070341 prefixEnd_1070341 := by exact prefixLift 1070341
  have htrace : WordTrace (prefixWord ++ tailWord_1070341) baseStart_1070341 baseEnd_1070341 := by
    simpa [prefixWord, tailWord_1070341, baseEnd_1070341] using wordTrace_append hprefix tailTrace_1070341
  have hstable : (prefixWord ++ tailWord_1070341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070341).length < 2 ^ (prefixWord ++ tailWord_1070341).sum := by decide
  have hdescent : baseEnd_1070341 < baseStart_1070341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070391 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1070391 : Nat := 118140960795 + 1070391 * 2 ^ 59
def prefixEnd_1070391 : Nat := 4983230072969 + 3 ^ 40 * 1070391 * 2
def baseEnd_1070391 : Nat := 549625071246826823989867

theorem tailTrace_1070391 : CollatzResearch.WordTrace tailWord_1070391 prefixEnd_1070391 549625071246826823989867 := by
  unfold tailWord_1070391
  simp only [CollatzResearch.WordTrace]
  refine ⟨39040367065163690073803027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26026911376775793382535351 39040367065163690073803027)
  ·
    refine ⟨58560550597745535110704541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39040367065163690073803027 58560550597745535110704541)
    ·
      refine ⟨21960206474154575666514203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58560550597745535110704541 21960206474154575666514203)
      ·
        refine ⟨32940309711231863499771305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21960206474154575666514203 32940309711231863499771305)
        ·
          refine ⟨24705232283423897624828479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32940309711231863499771305 24705232283423897624828479)
          ·
            refine ⟨37057848425135846437242719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24705232283423897624828479 37057848425135846437242719)
            ·
              refine ⟨55586772637703769655864079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37057848425135846437242719 55586772637703769655864079)
              ·
                refine ⟨83380158956555654483796119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55586772637703769655864079 83380158956555654483796119)
                ·
                  refine ⟨125070238434833481725694179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83380158956555654483796119 125070238434833481725694179)
                  ·
                    refine ⟨187605357652250222588541269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125070238434833481725694179 187605357652250222588541269)
                    ·
                      refine ⟨549625071246826823989867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 187605357652250222588541269 549625071246826823989867)
                      ·
                        rfl

theorem cell23_1070391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1070391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070391 prefixEnd_1070391 := by exact prefixLift 1070391
  have htrace : WordTrace (prefixWord ++ tailWord_1070391) baseStart_1070391 baseEnd_1070391 := by
    simpa [prefixWord, tailWord_1070391, baseEnd_1070391] using wordTrace_append hprefix tailTrace_1070391
  have hstable : (prefixWord ++ tailWord_1070391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070391).length < 2 ^ (prefixWord ++ tailWord_1070391).sum := by decide
  have hdescent : baseEnd_1070391 < baseStart_1070391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070406 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1070406 : Nat := 118140960795 + 1070406 * 2 ^ 59
def prefixEnd_1070406 : Nat := 4983230072969 + 3 ^ 40 * 1070406 * 2
def baseEnd_1070406 : Nat := 549632773456644265302299

theorem tailTrace_1070406 : CollatzResearch.WordTrace tailWord_1070406 prefixEnd_1070406 549632773456644265302299 := by
  unfold tailWord_1070406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220028567503417113612471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26027276106739565090399381 1220028567503417113612471)
  ·
    refine ⟨1830042851255125670418707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1220028567503417113612471 1830042851255125670418707)
    ·
      refine ⟨2745064276882688505628061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830042851255125670418707 2745064276882688505628061)
      ·
        refine ⟨1029399103831008189610523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2745064276882688505628061 1029399103831008189610523)
        ·
          refine ⟨1544098655746512284415785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029399103831008189610523 1544098655746512284415785)
          ·
            refine ⟨1158073991809884213311839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544098655746512284415785 1158073991809884213311839)
            ·
              refine ⟨1737110987714826319967759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158073991809884213311839 1737110987714826319967759)
              ·
                refine ⟨2605666481572239479951639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737110987714826319967759 2605666481572239479951639)
                ·
                  refine ⟨3908499722358359219927459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605666481572239479951639 3908499722358359219927459)
                  ·
                    refine ⟨5862749583537538829891189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3908499722358359219927459 5862749583537538829891189)
                    ·
                      refine ⟨549632773456644265302299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5862749583537538829891189 549632773456644265302299)
                      ·
                        rfl

theorem cell23_1070406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1070406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070406 prefixEnd_1070406 := by exact prefixLift 1070406
  have htrace : WordTrace (prefixWord ++ tailWord_1070406) baseStart_1070406 baseEnd_1070406 := by
    simpa [prefixWord, tailWord_1070406, baseEnd_1070406] using wordTrace_append hprefix tailTrace_1070406
  have hstable : (prefixWord ++ tailWord_1070406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070406).length < 2 ^ (prefixWord ++ tailWord_1070406).sum := by decide
  have hdescent : baseEnd_1070406 < baseStart_1070406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070418 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1070418 : Nat := 118140960795 + 1070418 * 2 ^ 59
def prefixEnd_1070418 : Nat := 4983230072969 + 3 ^ 40 * 1070418 * 2
def baseEnd_1070418 : Nat := 183212978408166072784081

theorem tailTrace_1070418 : CollatzResearch.WordTrace tailWord_1070418 prefixEnd_1070418 183212978408166072784081 := by
  unfold tailWord_1070418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9760337959016468421258977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26027567890710582456690605 9760337959016468421258977)
  ·
    refine ⟨7320253469262351315944233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9760337959016468421258977 7320253469262351315944233)
    ·
      refine ⟨5490190101946763486958175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7320253469262351315944233 5490190101946763486958175)
      ·
        refine ⟨8235285152920145230437263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5490190101946763486958175 8235285152920145230437263)
        ·
          refine ⟨12352927729380217845655895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8235285152920145230437263 12352927729380217845655895)
          ·
            refine ⟨18529391594070326768483843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12352927729380217845655895 18529391594070326768483843)
            ·
              refine ⟨27794087391105490152725765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18529391594070326768483843 27794087391105490152725765)
              ·
                refine ⟨5211391385832279403636081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27794087391105490152725765 5211391385832279403636081)
                ·
                  refine ⟨3908543539374209552727061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5211391385832279403636081 3908543539374209552727061)
                  ·
                    refine ⟨183212978408166072784081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3908543539374209552727061 183212978408166072784081)
                    ·
                      rfl

theorem cell23_1070418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1070418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070418 prefixEnd_1070418 := by exact prefixLift 1070418
  have htrace : WordTrace (prefixWord ++ tailWord_1070418) baseStart_1070418 baseEnd_1070418 := by
    simpa [prefixWord, tailWord_1070418, baseEnd_1070418] using wordTrace_append hprefix tailTrace_1070418
  have hstable : (prefixWord ++ tailWord_1070418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070418).length < 2 ^ (prefixWord ++ tailWord_1070418).sum := by decide
  have hdescent : baseEnd_1070418 < baseStart_1070418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070448 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 7]
def baseStart_1070448 : Nat := 118140960795 + 1070448 * 2 ^ 59
def prefixEnd_1070448 : Nat := 4983230072969 + 3 ^ 40 * 1070448 * 2
def baseEnd_1070448 : Nat := 61072704404903677886345

theorem tailTrace_1070448 : CollatzResearch.WordTrace tailWord_1070448 prefixEnd_1070448 61072704404903677886345 := by
  unfold tailWord_1070448
  simp only [CollatzResearch.WordTrace]
  refine ⟨19521223012978594404313999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26028297350638125872418665 19521223012978594404313999)
  ·
    refine ⟨29281834519467891606470999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19521223012978594404313999 29281834519467891606470999)
    ·
      refine ⟨43922751779201837409706499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29281834519467891606470999 43922751779201837409706499)
      ·
        refine ⟨65884127668802756114559749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43922751779201837409706499 65884127668802756114559749)
        ·
          refine ⟨12353273937900516771479953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65884127668802756114559749 12353273937900516771479953)
          ·
            refine ⟨9264955453425387578609965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12353273937900516771479953 9264955453425387578609965)
            ·
              refine ⟨3474358295034520341978737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9264955453425387578609965 3474358295034520341978737)
              ·
                refine ⟨2605768721275890256484053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474358295034520341978737 2605768721275890256484053)
                ·
                  refine ⟨61072704404903677886345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2605768721275890256484053 61072704404903677886345)
                  ·
                    rfl

theorem cell23_1070448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_1070448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070448 prefixEnd_1070448 := by exact prefixLift 1070448
  have htrace : WordTrace (prefixWord ++ tailWord_1070448) baseStart_1070448 baseEnd_1070448 := by
    simpa [prefixWord, tailWord_1070448, baseEnd_1070448] using wordTrace_append hprefix tailTrace_1070448
  have hstable : (prefixWord ++ tailWord_1070448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070448).length < 2 ^ (prefixWord ++ tailWord_1070448).sum := by decide
  have hdescent : baseEnd_1070448 < baseStart_1070448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070485 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_1070485 : Nat := 118140960795 + 1070485 * 2 ^ 59
def prefixEnd_1070485 : Nat := 4983230072969 + 3 ^ 40 * 1070485 * 2
def baseEnd_1070485 : Nat := 549673338428349456214435

theorem tailTrace_1070485 : CollatzResearch.WordTrace tailWord_1070485 prefixEnd_1070485 549673338428349456214435 := by
  unfold tailWord_1070485
  simp only [CollatzResearch.WordTrace]
  refine ⟨39043795526823144127724909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26029197017882096085149939 39043795526823144127724909)
  ·
    refine ⟨14641423322558679047896841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39043795526823144127724909 14641423322558679047896841)
    ·
      refine ⟨10981067491919009285922631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14641423322558679047896841 10981067491919009285922631)
      ·
        refine ⟨16471601237878513928883947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10981067491919009285922631 16471601237878513928883947)
        ·
          refine ⟨24707401856817770893325921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16471601237878513928883947 24707401856817770893325921)
          ·
            refine ⟨18530551392613328169994441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24707401856817770893325921 18530551392613328169994441)
            ·
              refine ⟨13897913544459996127495831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18530551392613328169994441 13897913544459996127495831)
              ·
                refine ⟨20846870316689994191243747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13897913544459996127495831 20846870316689994191243747)
                ·
                  refine ⟨31270305475034991286865621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20846870316689994191243747 31270305475034991286865621)
                  ·
                    refine ⟨732897784571132608285913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31270305475034991286865621 732897784571132608285913)
                    ·
                      refine ⟨549673338428349456214435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732897784571132608285913 549673338428349456214435)
                      ·
                        rfl

theorem cell23_1070485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_1070485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070485 prefixEnd_1070485 := by exact prefixLift 1070485
  have htrace : WordTrace (prefixWord ++ tailWord_1070485) baseStart_1070485 baseEnd_1070485 := by
    simpa [prefixWord, tailWord_1070485, baseEnd_1070485] using wordTrace_append hprefix tailTrace_1070485
  have hstable : (prefixWord ++ tailWord_1070485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070485).length < 2 ^ (prefixWord ++ tailWord_1070485).sum := by decide
  have hdescent : baseEnd_1070485 < baseStart_1070485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070515 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 6, 2]
def baseStart_1070515 : Nat := 118140960795 + 1070515 * 2 ^ 59
def prefixEnd_1070515 : Nat := 4983230072969 + 3 ^ 40 * 1070515 * 2
def baseEnd_1070515 : Nat := 549688742847984338839297

theorem tailTrace_1070515 : CollatzResearch.WordTrace tailWord_1070515 prefixEnd_1070515 549688742847984338839297 := by
  unfold tailWord_1070515
  simp only [CollatzResearch.WordTrace]
  refine ⟨39044889716714459251316999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26029926477809639500877999 39044889716714459251316999)
  ·
    refine ⟨58567334575071688876975499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39044889716714459251316999 58567334575071688876975499)
    ·
      refine ⟨87851001862607533315463249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58567334575071688876975499 87851001862607533315463249)
      ·
        refine ⟨65888251396955649986597437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87851001862607533315463249 65888251396955649986597437)
        ·
          refine ⟨24708094273858368744974039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65888251396955649986597437 24708094273858368744974039)
          ·
            refine ⟨37062141410787553117461059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24708094273858368744974039 37062141410787553117461059)
            ·
              refine ⟨55593212116181329676191589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37062141410787553117461059 55593212116181329676191589)
              ·
                refine ⟨10423727271783999314285923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55593212116181329676191589 10423727271783999314285923)
                ·
                  refine ⟨15635590907675998971428885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10423727271783999314285923 15635590907675998971428885)
                  ·
                    refine ⟨732918323797312451785729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15635590907675998971428885 732918323797312451785729)
                    ·
                      refine ⟨549688742847984338839297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 732918323797312451785729 549688742847984338839297)
                      ·
                        rfl

theorem cell23_1070515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6, 2].length) (baseStart_1070515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070515 prefixEnd_1070515 := by exact prefixLift 1070515
  have htrace : WordTrace (prefixWord ++ tailWord_1070515) baseStart_1070515 baseEnd_1070515 := by
    simpa [prefixWord, tailWord_1070515, baseEnd_1070515] using wordTrace_append hprefix tailTrace_1070515
  have hstable : (prefixWord ++ tailWord_1070515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070515).length < 2 ^ (prefixWord ++ tailWord_1070515).sum := by decide
  have hdescent : baseEnd_1070515 < baseStart_1070515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070528 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_1070528 : Nat := 118140960795 + 1070528 * 2 ^ 59
def prefixEnd_1070528 : Nat := 4983230072969 + 3 ^ 40 * 1070528 * 2
def baseEnd_1070528 : Nat := 549695418096492787976737

theorem tailTrace_1070528 : CollatzResearch.WordTrace tailWord_1070528 prefixEnd_1070528 549695418096492787976737 := by
  unfold tailWord_1070528
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522681932833681235770119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26030242577111574981026825 19522681932833681235770119)
  ·
    refine ⟨29284022899250521853655179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19522681932833681235770119 29284022899250521853655179)
    ·
      refine ⟨43926034348875782780482769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29284022899250521853655179 43926034348875782780482769)
      ·
        refine ⟨32944525761656837085362077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43926034348875782780482769 32944525761656837085362077)
        ·
          refine ⟨12354197160621313907010779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32944525761656837085362077 12354197160621313907010779)
          ·
            refine ⟨18531295740931970860516169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12354197160621313907010779 18531295740931970860516169)
            ·
              refine ⟨13898471805698978145387127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18531295740931970860516169 13898471805698978145387127)
              ·
                refine ⟨20847707708548467218080691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13898471805698978145387127 20847707708548467218080691)
                ·
                  refine ⟨31271561562822700827121037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20847707708548467218080691 31271561562822700827121037)
                  ·
                    refine ⟨11726835586058512810170389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31271561562822700827121037 11726835586058512810170389)
                    ·
                      refine ⟨549695418096492787976737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11726835586058512810170389 549695418096492787976737)
                      ·
                        rfl

theorem cell23_1070528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_1070528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070528 prefixEnd_1070528 := by exact prefixLift 1070528
  have htrace : WordTrace (prefixWord ++ tailWord_1070528) baseStart_1070528 baseEnd_1070528 := by
    simpa [prefixWord, tailWord_1070528, baseEnd_1070528] using wordTrace_append hprefix tailTrace_1070528
  have hstable : (prefixWord ++ tailWord_1070528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070528).length < 2 ^ (prefixWord ++ tailWord_1070528).sum := by decide
  have hdescent : baseEnd_1070528 < baseStart_1070528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070532 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1070532 : Nat := 118140960795 + 1070532 * 2 ^ 59
def prefixEnd_1070532 : Nat := 4983230072969 + 3 ^ 40 * 1070532 * 2
def baseEnd_1070532 : Nat := 549697472019110772326719

theorem tailTrace_1070532 : CollatzResearch.WordTrace tailWord_1070532 prefixEnd_1070532 549697472019110772326719 := by
  unfold tailWord_1070532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522754878826435577342925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26030339838435247436457233 19522754878826435577342925)
  ·
    refine ⟨7321033079559913341503597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19522754878826435577342925 7321033079559913341503597)
    ·
      refine ⟨2745387404834967503063849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7321033079559913341503597 2745387404834967503063849)
      ·
        refine ⟨2059040553626225627297887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2745387404834967503063849 2059040553626225627297887)
        ·
          refine ⟨3088560830439338440946831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059040553626225627297887 3088560830439338440946831)
          ·
            refine ⟨4632841245659007661420247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088560830439338440946831 4632841245659007661420247)
            ·
              refine ⟨6949261868488511492130371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632841245659007661420247 6949261868488511492130371)
              ·
                refine ⟨10423892802732767238195557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949261868488511492130371 10423892802732767238195557)
                ·
                  refine ⟨1954479900512393857161667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10423892802732767238195557 1954479900512393857161667)
                  ·
                    refine ⟨2931719850768590785742501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954479900512393857161667 2931719850768590785742501)
                    ·
                      refine ⟨549697472019110772326719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2931719850768590785742501 549697472019110772326719)
                      ·
                        rfl

theorem cell23_1070532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1070532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070532 prefixEnd_1070532 := by exact prefixLift 1070532
  have htrace : WordTrace (prefixWord ++ tailWord_1070532) baseStart_1070532 baseEnd_1070532 := by
    simpa [prefixWord, tailWord_1070532, baseEnd_1070532] using wordTrace_append hprefix tailTrace_1070532
  have hstable : (prefixWord ++ tailWord_1070532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070532).length < 2 ^ (prefixWord ++ tailWord_1070532).sum := by decide
  have hdescent : baseEnd_1070532 < baseStart_1070532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070542 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_1070542 : Nat := 118140960795 + 1070542 * 2 ^ 59
def prefixEnd_1070542 : Nat := 4983230072969 + 3 ^ 40 * 1070542 * 2
def baseEnd_1070542 : Nat := 183234202275218577733891

theorem tailTrace_1070542 : CollatzResearch.WordTrace tailWord_1070542 prefixEnd_1070542 183234202275218577733891 := by
  unfold tailWord_1070542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880734310952080357818735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26030582991744428575033253 4880734310952080357818735)
  ·
    refine ⟨7321101466428120536728103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4880734310952080357818735 7321101466428120536728103)
    ·
      refine ⟨10981652199642180805092155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7321101466428120536728103 10981652199642180805092155)
      ·
        refine ⟨16472478299463271207638233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10981652199642180805092155 16472478299463271207638233)
        ·
          refine ⟨12354358724597453405728675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16472478299463271207638233 12354358724597453405728675)
          ·
            refine ⟨18531538086896180108593013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12354358724597453405728675 18531538086896180108593013)
            ·
              refine ⟨1737331695646516885180595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18531538086896180108593013 1737331695646516885180595)
              ·
                refine ⟨2605997543469775327770893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737331695646516885180595 2605997543469775327770893)
                ·
                  refine ⟨977249078801165747914085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2605997543469775327770893 977249078801165747914085)
                  ·
                    refine ⟨183234202275218577733891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977249078801165747914085 183234202275218577733891)
                    ·
                      rfl

theorem cell23_1070542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_1070542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070542 prefixEnd_1070542 := by exact prefixLift 1070542
  have htrace : WordTrace (prefixWord ++ tailWord_1070542) baseStart_1070542 baseEnd_1070542 := by
    simpa [prefixWord, tailWord_1070542, baseEnd_1070542] using wordTrace_append hprefix tailTrace_1070542
  have hstable : (prefixWord ++ tailWord_1070542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070542).length < 2 ^ (prefixWord ++ tailWord_1070542).sum := by decide
  have hdescent : baseEnd_1070542 < baseStart_1070542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070593 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1070593 : Nat := 118140960795 + 1070593 * 2 ^ 59
def prefixEnd_1070593 : Nat := 4983230072969 + 3 ^ 40 * 1070593 * 2
def baseEnd_1070593 : Nat := 183242931446345011221313

theorem tailTrace_1070593 : CollatzResearch.WordTrace tailWord_1070593 prefixEnd_1070593 183242931446345011221313 := by
  unfold tailWord_1070593
  simp only [CollatzResearch.WordTrace]
  refine ⟨39047734610431878572656433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26031823073621252381770955 39047734610431878572656433)
  ·
    refine ⟨29285800957823908929492325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39047734610431878572656433 29285800957823908929492325)
    ·
      refine ⟨5491087679591982924279811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29285800957823908929492325 5491087679591982924279811)
      ·
        refine ⟨8236631519387974386419717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5491087679591982924279811 8236631519387974386419717)
        ·
          refine ⟨1544368409885245197453697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8236631519387974386419717 1544368409885245197453697)
          ·
            refine ⟨1158276307413933898090273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544368409885245197453697 1158276307413933898090273)
            ·
              refine ⟨868707230560450423567705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158276307413933898090273 868707230560450423567705)
              ·
                refine ⟨651530422920337817675779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868707230560450423567705 651530422920337817675779)
                ·
                  refine ⟨977295634380506726513669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651530422920337817675779 977295634380506726513669)
                  ·
                    refine ⟨183242931446345011221313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977295634380506726513669 183242931446345011221313)
                    ·
                      rfl

theorem cell23_1070593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1070593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070593 prefixEnd_1070593 := by exact prefixLift 1070593
  have htrace : WordTrace (prefixWord ++ tailWord_1070593) baseStart_1070593 baseEnd_1070593 := by
    simpa [prefixWord, tailWord_1070593, baseEnd_1070593] using wordTrace_append hprefix tailTrace_1070593
  have hstable : (prefixWord ++ tailWord_1070593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070593).length < 2 ^ (prefixWord ++ tailWord_1070593).sum := by decide
  have hdescent : baseEnd_1070593 < baseStart_1070593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070645 : List Nat := [1, 3, 3, 1, 1, 4, 10]
def baseStart_1070645 : Nat := 118140960795 + 1070645 * 2 ^ 59
def prefixEnd_1070645 : Nat := 4983230072969 + 3 ^ 40 * 1070645 * 2
def baseEnd_1070645 : Nat := 6787104880655170743379

theorem tailTrace_1070645 : CollatzResearch.WordTrace tailWord_1070645 prefixEnd_1070645 6787104880655170743379 := by
  unfold tailWord_1070645
  simp only [CollatzResearch.WordTrace]
  refine ⟨39049631206243491453549389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26033087470828994302366259 39049631206243491453549389)
  ·
    refine ⟨14643611702341309295081021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39049631206243491453549389 14643611702341309295081021)
    ·
      refine ⟨5491354388377990985655383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14643611702341309295081021 5491354388377990985655383)
      ·
        refine ⟨8237031582566986478483075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5491354388377990985655383 8237031582566986478483075)
        ·
          refine ⟨12355547373850479717724613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237031582566986478483075 12355547373850479717724613)
          ·
            refine ⟨2316665132596964947073365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12355547373850479717724613 2316665132596964947073365)
            ·
              refine ⟨6787104880655170743379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2316665132596964947073365 6787104880655170743379)
              ·
                rfl

theorem cell23_1070645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 10].length) (baseStart_1070645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070645 prefixEnd_1070645 := by exact prefixLift 1070645
  have htrace : WordTrace (prefixWord ++ tailWord_1070645) baseStart_1070645 baseEnd_1070645 := by
    simpa [prefixWord, tailWord_1070645, baseEnd_1070645] using wordTrace_append hprefix tailTrace_1070645
  have hstable : (prefixWord ++ tailWord_1070645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070645).length < 2 ^ (prefixWord ++ tailWord_1070645).sum := by decide
  have hdescent : baseEnd_1070645 < baseStart_1070645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070649 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 2, 4]
def baseStart_1070649 : Nat := 118140960795 + 1070649 * 2 ^ 59
def prefixEnd_1070649 : Nat := 4983230072969 + 3 ^ 40 * 1070649 * 2
def baseEnd_1070649 : Nat := 183252516418562271521227

theorem tailTrace_1070649 : CollatzResearch.WordTrace tailWord_1070649 prefixEnd_1070649 183252516418562271521227 := by
  unfold tailWord_1070649
  simp only [CollatzResearch.WordTrace]
  refine ⟨39049777098229000136695001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26033184732152666757796667 39049777098229000136695001)
  ·
    refine ⟨29287332823671750102521251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39049777098229000136695001 29287332823671750102521251)
    ·
      refine ⟨43930999235507625153781877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29287332823671750102521251 43930999235507625153781877)
      ·
        refine ⟨4118531178328839858167051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43930999235507625153781877 4118531178328839858167051)
        ·
          refine ⟨6177796767493259787250577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4118531178328839858167051 6177796767493259787250577)
          ·
            refine ⟨4633347575619944840437933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6177796767493259787250577 4633347575619944840437933)
            ·
              refine ⟨1737505340857479315164225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4633347575619944840437933 1737505340857479315164225)
              ·
                refine ⟨1303129005643109486373169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737505340857479315164225 1303129005643109486373169)
                ·
                  refine ⟨977346754232332114779877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303129005643109486373169 977346754232332114779877)
                  ·
                    refine ⟨183252516418562271521227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977346754232332114779877 183252516418562271521227)
                    ·
                      rfl

theorem cell23_1070649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_1070649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070649 prefixEnd_1070649 := by exact prefixLift 1070649
  have htrace : WordTrace (prefixWord ++ tailWord_1070649) baseStart_1070649 baseEnd_1070649 := by
    simpa [prefixWord, tailWord_1070649, baseEnd_1070649] using wordTrace_append hprefix tailTrace_1070649
  have hstable : (prefixWord ++ tailWord_1070649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070649).length < 2 ^ (prefixWord ++ tailWord_1070649).sum := by decide
  have hdescent : baseEnd_1070649 < baseStart_1070649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070669 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1070669 : Nat := 118140960795 + 1070669 * 2 ^ 59
def prefixEnd_1070669 : Nat := 4983230072969 + 3 ^ 40 * 1070669 * 2
def baseEnd_1070669 : Nat := 549767818868776736313589

theorem tailTrace_1070669 : CollatzResearch.WordTrace tailWord_1070669 prefixEnd_1070669 549767818868776736313589 := by
  unfold tailWord_1070669
  simp only [CollatzResearch.WordTrace]
  refine ⟨39050506558156543552423061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26033671038771029034948707 39050506558156543552423061)
  ·
    refine ⟨1830492494913587979019831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39050506558156543552423061 1830492494913587979019831)
    ·
      refine ⟨2745738742370381968529747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830492494913587979019831 2745738742370381968529747)
      ·
        refine ⟨4118608113555572952794621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745738742370381968529747 4118608113555572952794621)
        ·
          refine ⟨1544478042583339857297983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4118608113555572952794621 1544478042583339857297983)
          ·
            refine ⟨2316717063875009785946975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544478042583339857297983 2316717063875009785946975)
            ·
              refine ⟨3475075595812514678920463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316717063875009785946975 3475075595812514678920463)
              ·
                refine ⟨5212613393718772018380695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475075595812514678920463 5212613393718772018380695)
                ·
                  refine ⟨7818920090578158027571043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212613393718772018380695 7818920090578158027571043)
                  ·
                    refine ⟨11728380135867237041356565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7818920090578158027571043 11728380135867237041356565)
                    ·
                      refine ⟨549767818868776736313589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11728380135867237041356565 549767818868776736313589)
                      ·
                        rfl

theorem cell23_1070669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1070669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070669 prefixEnd_1070669 := by exact prefixLift 1070669
  have htrace : WordTrace (prefixWord ++ tailWord_1070669) baseStart_1070669 baseEnd_1070669 := by
    simpa [prefixWord, tailWord_1070669, baseEnd_1070669] using wordTrace_append hprefix tailTrace_1070669
  have hstable : (prefixWord ++ tailWord_1070669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070669).length < 2 ^ (prefixWord ++ tailWord_1070669).sum := by decide
  have hdescent : baseEnd_1070669 < baseStart_1070669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070682 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2]
def baseStart_1070682 : Nat := 118140960795 + 1070682 * 2 ^ 59
def prefixEnd_1070682 : Nat := 4983230072969 + 3 ^ 40 * 1070682 * 2
def baseEnd_1070682 : Nat := 549774494117285185451029

theorem tailTrace_1070682 : CollatzResearch.WordTrace tailWord_1070682 prefixEnd_1070682 549774494117285185451029 := by
  unfold tailWord_1070682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762745176777361693161575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26033987138072964515097533 9762745176777361693161575)
  ·
    refine ⟨14644117765166042539742363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762745176777361693161575 14644117765166042539742363)
    ·
      refine ⟨21966176647749063809613545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14644117765166042539742363 21966176647749063809613545)
      ·
        refine ⟨16474632485811797857210159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21966176647749063809613545 16474632485811797857210159)
        ·
          refine ⟨24711948728717696785815239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16474632485811797857210159 24711948728717696785815239)
          ·
            refine ⟨37067923093076545178722859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24711948728717696785815239 37067923093076545178722859)
            ·
              refine ⟨55601884639614817768084289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37067923093076545178722859 55601884639614817768084289)
              ·
                refine ⟨41701413479711113326063217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55601884639614817768084289 41701413479711113326063217)
                ·
                  refine ⟨31276060109783334994547413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41701413479711113326063217 31276060109783334994547413)
                  ·
                    refine ⟨733032658823046913934705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31276060109783334994547413 733032658823046913934705)
                    ·
                      refine ⟨549774494117285185451029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733032658823046913934705 549774494117285185451029)
                      ·
                        rfl

theorem cell23_1070682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_1070682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070682 prefixEnd_1070682 := by exact prefixLift 1070682
  have htrace : WordTrace (prefixWord ++ tailWord_1070682) baseStart_1070682 baseEnd_1070682 := by
    simpa [prefixWord, tailWord_1070682, baseEnd_1070682] using wordTrace_append hprefix tailTrace_1070682
  have hstable : (prefixWord ++ tailWord_1070682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070682).length < 2 ^ (prefixWord ++ tailWord_1070682).sum := by decide
  have hdescent : baseEnd_1070682 < baseStart_1070682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070705 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_1070705 : Nat := 118140960795 + 1070705 * 2 ^ 59
def prefixEnd_1070705 : Nat := 4983230072969 + 3 ^ 40 * 1070705 * 2
def baseEnd_1070705 : Nat := 183262101390779531821141

theorem tailTrace_1070705 : CollatzResearch.WordTrace tailWord_1070705 prefixEnd_1070705 183262101390779531821141 := by
  unfold tailWord_1070705
  simp only [CollatzResearch.WordTrace]
  refine ⟨39051819586026121700733569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26034546390684081133822379 39051819586026121700733569)
  ·
    refine ⟨29288864689519591275550177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39051819586026121700733569 29288864689519591275550177)
    ·
      refine ⟨21966648517139693456662633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29288864689519591275550177 21966648517139693456662633)
      ·
        refine ⟨16474986387854770092496975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21966648517139693456662633 16474986387854770092496975)
        ·
          refine ⟨24712479581782155138745463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16474986387854770092496975 24712479581782155138745463)
          ·
            refine ⟨37068719372673232708118195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24712479581782155138745463 37068719372673232708118195)
            ·
              refine ⟨55603079059009849062177293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37068719372673232708118195 55603079059009849062177293)
              ·
                refine ⟨20851154647128693398316485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55603079059009849062177293 20851154647128693398316485)
                ·
                  refine ⟨3909591496336630012184341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20851154647128693398316485 3909591496336630012184341)
                  ·
                    refine ⟨183262101390779531821141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3909591496336630012184341 183262101390779531821141)
                    ·
                      rfl

theorem cell23_1070705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_1070705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070705 prefixEnd_1070705 := by exact prefixLift 1070705
  have htrace : WordTrace (prefixWord ++ tailWord_1070705) baseStart_1070705 baseEnd_1070705 := by
    simpa [prefixWord, tailWord_1070705, baseEnd_1070705] using wordTrace_append hprefix tailTrace_1070705
  have hstable : (prefixWord ++ tailWord_1070705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070705).length < 2 ^ (prefixWord ++ tailWord_1070705).sum := by decide
  have hdescent : baseEnd_1070705 < baseStart_1070705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070712 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 8, 2]
def baseStart_1070712 : Nat := 118140960795 + 1070712 * 2 ^ 59
def prefixEnd_1070712 : Nat := 4983230072969 + 3 ^ 40 * 1070712 * 2
def baseEnd_1070712 : Nat := 549789898536920068075891

theorem tailTrace_1070712 : CollatzResearch.WordTrace tailWord_1070712 prefixEnd_1070712 549789898536920068075891 := by
  unfold tailWord_1070712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19526037448500380948119195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26034716598000507930825593 19526037448500380948119195)
  ·
    refine ⟨29289056172750571422178793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19526037448500380948119195 29289056172750571422178793)
    ·
      refine ⟨21966792129562928566634095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29289056172750571422178793 21966792129562928566634095)
      ·
        refine ⟨32950188194344392849951143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21966792129562928566634095 32950188194344392849951143)
        ·
          refine ⟨49425282291516589274926715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32950188194344392849951143 49425282291516589274926715)
          ·
            refine ⟨74137923437274883912390073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49425282291516589274926715 74137923437274883912390073)
            ·
              refine ⟨55603442577956162934292555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74137923437274883912390073 55603442577956162934292555)
              ·
                refine ⟨83405163866934244401438833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55603442577956162934292555 83405163866934244401438833)
                ·
                  refine ⟨62553872900200683301079125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83405163866934244401438833 62553872900200683301079125)
                  ·
                    refine ⟨733053198049226757434521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62553872900200683301079125 733053198049226757434521)
                    ·
                      refine ⟨549789898536920068075891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733053198049226757434521 549789898536920068075891)
                      ·
                        rfl

theorem cell23_1070712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_1070712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070712 prefixEnd_1070712 := by exact prefixLift 1070712
  have htrace : WordTrace (prefixWord ++ tailWord_1070712) baseStart_1070712 baseEnd_1070712 := by
    simpa [prefixWord, tailWord_1070712, baseEnd_1070712] using wordTrace_append hprefix tailTrace_1070712
  have hstable : (prefixWord ++ tailWord_1070712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070712).length < 2 ^ (prefixWord ++ tailWord_1070712).sum := by decide
  have hdescent : baseEnd_1070712 < baseStart_1070712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070715 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_1070715 : Nat := 118140960795 + 1070715 * 2 ^ 59
def prefixEnd_1070715 : Nat := 4983230072969 + 3 ^ 40 * 1070715 * 2
def baseEnd_1070715 : Nat := 549791438978883556338377

theorem tailTrace_1070715 : CollatzResearch.WordTrace tailWord_1070715 prefixEnd_1070715 549791438978883556338377 := by
  unfold tailWord_1070715
  simp only [CollatzResearch.WordTrace]
  refine ⟨39052184315989893408597599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26034789543993262272398399 39052184315989893408597599)
  ·
    refine ⟨58578276473984840112896399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39052184315989893408597599 58578276473984840112896399)
    ·
      refine ⟨87867414710977260169344599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58578276473984840112896399 87867414710977260169344599)
      ·
        refine ⟨131801122066465890254016899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87867414710977260169344599 131801122066465890254016899)
        ·
          refine ⟨197701683099698835381025349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131801122066465890254016899 197701683099698835381025349)
          ·
            refine ⟨37069065581193531633942253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197701683099698835381025349 37069065581193531633942253)
            ·
              refine ⟨13900899592947574362728345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37069065581193531633942253 13900899592947574362728345)
              ·
                refine ⟨10425674694710680772046259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13900899592947574362728345 10425674694710680772046259)
                ·
                  refine ⟨15638512042066021158069389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10425674694710680772046259 15638512042066021158069389)
                  ·
                    refine ⟨5864442015774757934276021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15638512042066021158069389 5864442015774757934276021)
                    ·
                      refine ⟨549791438978883556338377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5864442015774757934276021 549791438978883556338377)
                      ·
                        rfl

theorem cell23_1070715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_1070715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070715 prefixEnd_1070715 := by exact prefixLift 1070715
  have htrace : WordTrace (prefixWord ++ tailWord_1070715) baseStart_1070715 baseEnd_1070715 := by
    simpa [prefixWord, tailWord_1070715, baseEnd_1070715] using wordTrace_append hprefix tailTrace_1070715
  have hstable : (prefixWord ++ tailWord_1070715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070715).length < 2 ^ (prefixWord ++ tailWord_1070715).sum := by decide
  have hdescent : baseEnd_1070715 < baseStart_1070715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070745 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_1070745 : Nat := 118140960795 + 1070745 * 2 ^ 59
def prefixEnd_1070745 : Nat := 4983230072969 + 3 ^ 40 * 1070745 * 2
def baseEnd_1070745 : Nat := 549806843398518438963239

theorem tailTrace_1070745 : CollatzResearch.WordTrace tailWord_1070745 prefixEnd_1070745 549806843398518438963239 := by
  unfold tailWord_1070745
  simp only [CollatzResearch.WordTrace]
  refine ⟨39053278505881208532189689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26035519003920805688126459 39053278505881208532189689)
  ·
    refine ⟨29289958879410906399142267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39053278505881208532189689 29289958879410906399142267)
    ·
      refine ⟨43934938319116359598713401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29289958879410906399142267 43934938319116359598713401)
      ·
        refine ⟨32951203739337269699035051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43934938319116359598713401 32951203739337269699035051)
        ·
          refine ⟨49426805609005904548552577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32951203739337269699035051 49426805609005904548552577)
          ·
            refine ⟨37070104206754428411414433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49426805609005904548552577 37070104206754428411414433)
            ·
              refine ⟨27802578155065821308560825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37070104206754428411414433 27802578155065821308560825)
              ·
                refine ⟨20851933616299365981420619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27802578155065821308560825 20851933616299365981420619)
                ·
                  refine ⟨31277900424449048972130929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20851933616299365981420619 31277900424449048972130929)
                  ·
                    refine ⟨23458425318336786729098197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31277900424449048972130929 23458425318336786729098197)
                    ·
                      refine ⟨549806843398518438963239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23458425318336786729098197 549806843398518438963239)
                      ·
                        rfl

theorem cell23_1070745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_1070745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070745 prefixEnd_1070745 := by exact prefixLift 1070745
  have htrace : WordTrace (prefixWord ++ tailWord_1070745) baseStart_1070745 baseEnd_1070745 := by
    simpa [prefixWord, tailWord_1070745, baseEnd_1070745] using wordTrace_append hprefix tailTrace_1070745
  have hstable : (prefixWord ++ tailWord_1070745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070745).length < 2 ^ (prefixWord ++ tailWord_1070745).sum := by decide
  have hdescent : baseEnd_1070745 < baseStart_1070745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070750 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_1070750 : Nat := 118140960795 + 1070750 * 2 ^ 59
def prefixEnd_1070750 : Nat := 4983230072969 + 3 ^ 40 * 1070750 * 2
def baseEnd_1070750 : Nat := 549809410801790919400717

theorem tailTrace_1070750 : CollatzResearch.WordTrace tailWord_1070750 prefixEnd_1070750 549809410801790919400717 := by
  unfold tailWord_1070750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881682608857886798265213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26035640580575396257414469 4881682608857886798265213)
  ·
    refine ⟨1830630978321707549349455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4881682608857886798265213 1830630978321707549349455)
    ·
      refine ⟨2745946467482561324024183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830630978321707549349455 2745946467482561324024183)
      ·
        refine ⟨4118919701223841986036275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745946467482561324024183 4118919701223841986036275)
        ·
          refine ⟨6178379551835762979054413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4118919701223841986036275 6178379551835762979054413)
          ·
            refine ⟨2316892331938411117145405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6178379551835762979054413 2316892331938411117145405)
            ·
              refine ⟨868834624476904168929527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2316892331938411117145405 868834624476904168929527)
              ·
                refine ⟨1303251936715356253394291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868834624476904168929527 1303251936715356253394291)
                ·
                  refine ⟨1954877905073034380091437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303251936715356253394291 1954877905073034380091437)
                  ·
                    refine ⟨733079214402387892534289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954877905073034380091437 733079214402387892534289)
                    ·
                      refine ⟨549809410801790919400717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733079214402387892534289 549809410801790919400717)
                      ·
                        rfl

theorem cell23_1070750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_1070750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070750 prefixEnd_1070750 := by exact prefixLift 1070750
  have htrace : WordTrace (prefixWord ++ tailWord_1070750) baseStart_1070750 baseEnd_1070750 := by
    simpa [prefixWord, tailWord_1070750, baseEnd_1070750] using wordTrace_append hprefix tailTrace_1070750
  have hstable : (prefixWord ++ tailWord_1070750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070750).length < 2 ^ (prefixWord ++ tailWord_1070750).sum := by decide
  have hdescent : baseEnd_1070750 < baseStart_1070750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070906 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_1070906 : Nat := 118140960795 + 1070906 * 2 ^ 59
def prefixEnd_1070906 : Nat := 4983230072969 + 3 ^ 40 * 1070906 * 2
def baseEnd_1070906 : Nat := 183296504594630769683333

theorem tailTrace_1070906 : CollatzResearch.WordTrace tailWord_1070906 prefixEnd_1070906 183296504594630769683333 := by
  unfold tailWord_1070906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764787664574483257200143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26039433772198622019200381 9764787664574483257200143)
  ·
    refine ⟨14647181496861724885800215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9764787664574483257200143 14647181496861724885800215)
    ·
      refine ⟨21970772245292587328700323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14647181496861724885800215 21970772245292587328700323)
      ·
        refine ⟨32956158367938880993050485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21970772245292587328700323 32956158367938880993050485)
        ·
          refine ⟨3089639846994270093098483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32956158367938880993050485 3089639846994270093098483)
          ·
            refine ⟨4634459770491405139647725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089639846994270093098483 4634459770491405139647725)
            ·
              refine ⟨1737922413934276927367897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4634459770491405139647725 1737922413934276927367897)
              ·
                refine ⟨1303441810450707695525923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737922413934276927367897 1303441810450707695525923)
                ·
                  refine ⟨1955162715676061543288885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303441810450707695525923 1955162715676061543288885)
                  ·
                    refine ⟨183296504594630769683333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1955162715676061543288885 183296504594630769683333)
                    ·
                      rfl

theorem cell23_1070906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_1070906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070906 prefixEnd_1070906 := by exact prefixLift 1070906
  have htrace : WordTrace (prefixWord ++ tailWord_1070906) baseStart_1070906 baseEnd_1070906 := by
    simpa [prefixWord, tailWord_1070906, baseEnd_1070906] using wordTrace_append hprefix tailTrace_1070906
  have hstable : (prefixWord ++ tailWord_1070906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070906).length < 2 ^ (prefixWord ++ tailWord_1070906).sum := by decide
  have hdescent : baseEnd_1070906 < baseStart_1070906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070912 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_1070912 : Nat := 118140960795 + 1070912 * 2 ^ 59
def prefixEnd_1070912 : Nat := 4983230072969 + 3 ^ 40 * 1070912 * 2
def baseEnd_1070912 : Nat := 549892594667819285574971

theorem tailTrace_1070912 : CollatzResearch.WordTrace tailWord_1070912 prefixEnd_1070912 549892594667819285574971 := by
  unfold tailWord_1070912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19529684748138098026759495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26039579664184130702345993 19529684748138098026759495)
  ·
    refine ⟨29294527122207147040139243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19529684748138098026759495 29294527122207147040139243)
    ·
      refine ⟨43941790683310720560208865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29294527122207147040139243 43941790683310720560208865)
      ·
        refine ⟨32956343012483040420156649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43941790683310720560208865 32956343012483040420156649)
        ·
          refine ⟨24717257259362280315117487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32956343012483040420156649 24717257259362280315117487)
          ·
            refine ⟨37075885889043420472676231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24717257259362280315117487 37075885889043420472676231)
            ·
              refine ⟨55613828833565130709014347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37075885889043420472676231 55613828833565130709014347)
              ·
                refine ⟨83420743250347696063521521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55613828833565130709014347 83420743250347696063521521)
                ·
                  refine ⟨62565557437760772047641141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83420743250347696063521521 62565557437760772047641141)
                  ·
                    refine ⟨5865521009790072379466357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62565557437760772047641141 5865521009790072379466357)
                    ·
                      refine ⟨549892594667819285574971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5865521009790072379466357 549892594667819285574971)
                      ·
                        rfl

theorem cell23_1070912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_1070912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070912 prefixEnd_1070912 := by exact prefixLift 1070912
  have htrace : WordTrace (prefixWord ++ tailWord_1070912) baseStart_1070912 baseEnd_1070912 := by
    simpa [prefixWord, tailWord_1070912, baseEnd_1070912] using wordTrace_append hprefix tailTrace_1070912
  have hstable : (prefixWord ++ tailWord_1070912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070912).length < 2 ^ (prefixWord ++ tailWord_1070912).sum := by decide
  have hdescent : baseEnd_1070912 < baseStart_1070912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070919 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 6, 4]
def baseStart_1070919 : Nat := 118140960795 + 1070919 * 2 ^ 59
def prefixEnd_1070919 : Nat := 4983230072969 + 3 ^ 40 * 1070919 * 2
def baseEnd_1070919 : Nat := 183298729677466919395813

theorem tailTrace_1070919 : CollatzResearch.WordTrace tailWord_1070919 prefixEnd_1070919 183298729677466919395813 := by
  unfold tailWord_1070919
  simp only [CollatzResearch.WordTrace]
  refine ⟨39059624807250836249023811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26039749871500557499349207 39059624807250836249023811)
  ·
    refine ⟨58589437210876254373535717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39059624807250836249023811 58589437210876254373535717)
    ·
      refine ⟨10985519477039297695037947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58589437210876254373535717 10985519477039297695037947)
      ·
        refine ⟨16478279215558946542556921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10985519477039297695037947 16478279215558946542556921)
        ·
          refine ⟨12358709411669209906917691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16478279215558946542556921 12358709411669209906917691)
          ·
            refine ⟨18538064117503814860376537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12358709411669209906917691 18538064117503814860376537)
            ·
              refine ⟨13903548088127861145282403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18538064117503814860376537 13903548088127861145282403)
              ·
                refine ⟨20855322132191791717923605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13903548088127861145282403 20855322132191791717923605)
                ·
                  refine ⟨977593224946490236777669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20855322132191791717923605 977593224946490236777669)
                  ·
                    refine ⟨183298729677466919395813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977593224946490236777669 183298729677466919395813)
                    ·
                      rfl

theorem cell23_1070919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_1070919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070919 prefixEnd_1070919 := by exact prefixLift 1070919
  have htrace : WordTrace (prefixWord ++ tailWord_1070919) baseStart_1070919 baseEnd_1070919 := by
    simpa [prefixWord, tailWord_1070919, baseEnd_1070919] using wordTrace_append hprefix tailTrace_1070919
  have hstable : (prefixWord ++ tailWord_1070919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070919).length < 2 ^ (prefixWord ++ tailWord_1070919).sum := by decide
  have hdescent : baseEnd_1070919 < baseStart_1070919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070956 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_1070956 : Nat := 118140960795 + 1070956 * 2 ^ 59
def prefixEnd_1070956 : Nat := 4983230072969 + 3 ^ 40 * 1070956 * 2
def baseEnd_1070956 : Nat := 549915187816617113424769

theorem tailTrace_1070956 : CollatzResearch.WordTrace tailWord_1070956 prefixEnd_1070956 549915187816617113424769 := by
  unfold tailWord_1070956
  simp only [CollatzResearch.WordTrace]
  refine ⟨19530487154058395784060361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26040649538744527712080481 19530487154058395784060361)
  ·
    refine ⟨14647865365543796838045271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19530487154058395784060361 14647865365543796838045271)
    ·
      refine ⟨21971798048315695257067907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14647865365543796838045271 21971798048315695257067907)
      ·
        refine ⟨32957697072473542885601861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21971798048315695257067907 32957697072473542885601861)
        ·
          refine ⟨6179568201088789291050349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32957697072473542885601861 6179568201088789291050349)
          ·
            refine ⟨2317338075408295984143881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6179568201088789291050349 2317338075408295984143881)
            ·
              refine ⟨1738003556556221988107911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317338075408295984143881 1738003556556221988107911)
              ·
                refine ⟨2607005334834332982161867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738003556556221988107911 2607005334834332982161867)
                ·
                  refine ⟨3910508002251499473242801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607005334834332982161867 3910508002251499473242801)
                  ·
                    refine ⟨2932881001688624604932101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3910508002251499473242801 2932881001688624604932101)
                    ·
                      refine ⟨549915187816617113424769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2932881001688624604932101 549915187816617113424769)
                      ·
                        rfl

theorem cell23_1070956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_1070956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070956 prefixEnd_1070956 := by exact prefixLift 1070956
  have htrace : WordTrace (prefixWord ++ tailWord_1070956) baseStart_1070956 baseEnd_1070956 := by
    simpa [prefixWord, tailWord_1070956, baseEnd_1070956] using wordTrace_append hprefix tailTrace_1070956
  have hstable : (prefixWord ++ tailWord_1070956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070956).length < 2 ^ (prefixWord ++ tailWord_1070956).sum := by decide
  have hdescent : baseEnd_1070956 < baseStart_1070956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070976 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 4, 1, 3]
def baseStart_1070976 : Nat := 118140960795 + 1070976 * 2 ^ 59
def prefixEnd_1070976 : Nat := 4983230072969 + 3 ^ 40 * 1070976 * 2
def baseEnd_1070976 : Nat := 549925457429707035174677

theorem tailTrace_1070976 : CollatzResearch.WordTrace tailWord_1070976 prefixEnd_1070976 549925457429707035174677 := by
  unfold tailWord_1070976
  simp only [CollatzResearch.WordTrace]
  refine ⟨19530851884022167491924391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26041135845362889989232521 19530851884022167491924391)
  ·
    refine ⟨29296277826033251237886587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19530851884022167491924391 29296277826033251237886587)
    ·
      refine ⟨43944416739049876856829881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29296277826033251237886587 43944416739049876856829881)
      ·
        refine ⟨32958312554287407642622411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43944416739049876856829881 32958312554287407642622411)
        ·
          refine ⟨49437468831431111463933617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32958312554287407642622411 49437468831431111463933617)
          ·
            refine ⟨37078101623573333597950213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49437468831431111463933617 37078101623573333597950213)
            ·
              refine ⟨6952144054420000049615665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37078101623573333597950213 6952144054420000049615665)
              ·
                refine ⟨5214108040815000037211749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6952144054420000049615665 5214108040815000037211749)
                ·
                  refine ⟨977645257652812506977203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5214108040815000037211749 977645257652812506977203)
                  ·
                    refine ⟨1466467886479218760465805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 977645257652812506977203 1466467886479218760465805)
                    ·
                      refine ⟨549925457429707035174677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1466467886479218760465805 549925457429707035174677)
                      ·
                        rfl

theorem cell23_1070976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_1070976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070976 prefixEnd_1070976 := by exact prefixLift 1070976
  have htrace : WordTrace (prefixWord ++ tailWord_1070976) baseStart_1070976 baseEnd_1070976 := by
    simpa [prefixWord, tailWord_1070976, baseEnd_1070976] using wordTrace_append hprefix tailTrace_1070976
  have hstable : (prefixWord ++ tailWord_1070976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070976).length < 2 ^ (prefixWord ++ tailWord_1070976).sum := by decide
  have hdescent : baseEnd_1070976 < baseStart_1070976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070977 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1070977 : Nat := 118140960795 + 1070977 * 2 ^ 59
def prefixEnd_1070977 : Nat := 4983230072969 + 3 ^ 40 * 1070977 * 2
def baseEnd_1070977 : Nat := 549925970910361531262173

theorem tailTrace_1070977 : CollatzResearch.WordTrace tailWord_1070977 prefixEnd_1070977 549925970910361531262173 := by
  unfold tailWord_1070977
  simp only [CollatzResearch.WordTrace]
  refine ⟨39061740241040712154635185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26041160160693808103090123 39061740241040712154635185)
  ·
    refine ⟨29296305180780534115976389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39061740241040712154635185 29296305180780534115976389)
    ·
      refine ⟨5493057221396350146745573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29296305180780534115976389 5493057221396350146745573)
      ·
        refine ⟨1029948229011815652514795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5493057221396350146745573 1029948229011815652514795)
        ·
          refine ⟨1544922343517723478772193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029948229011815652514795 1544922343517723478772193)
          ·
            refine ⟨1158691757638292609079145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544922343517723478772193 1158691757638292609079145)
            ·
              refine ⟨869018818228719456809359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158691757638292609079145 869018818228719456809359)
              ·
                refine ⟨1303528227343079185214039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869018818228719456809359 1303528227343079185214039)
                ·
                  refine ⟨1955292341014618777821059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303528227343079185214039 1955292341014618777821059)
                  ·
                    refine ⟨2932938511521928166731589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1955292341014618777821059 2932938511521928166731589)
                    ·
                      refine ⟨549925970910361531262173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2932938511521928166731589 549925970910361531262173)
                      ·
                        rfl

theorem cell23_1070977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1070977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070977 prefixEnd_1070977 := by exact prefixLift 1070977
  have htrace : WordTrace (prefixWord ++ tailWord_1070977) baseStart_1070977 baseEnd_1070977 := by
    simpa [prefixWord, tailWord_1070977, baseEnd_1070977] using wordTrace_append hprefix tailTrace_1070977
  have hstable : (prefixWord ++ tailWord_1070977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070977).length < 2 ^ (prefixWord ++ tailWord_1070977).sum := by decide
  have hdescent : baseEnd_1070977 < baseStart_1070977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070993 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_1070993 : Nat := 118140960795 + 1070993 * 2 ^ 59
def prefixEnd_1070993 : Nat := 4983230072969 + 3 ^ 40 * 1070993 * 2
def baseEnd_1070993 : Nat := 549934186600833468662099

theorem tailTrace_1070993 : CollatzResearch.WordTrace tailWord_1070993 prefixEnd_1070993 549934186600833468662099 := by
  unfold tailWord_1070993
  simp only [CollatzResearch.WordTrace]
  refine ⟨39062323808982746887217633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26041549205988497924811755 39062323808982746887217633)
  ·
    refine ⟨29296742856737060165413225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39062323808982746887217633 29296742856737060165413225)
    ·
      refine ⟨21972557142552795124059919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29296742856737060165413225 21972557142552795124059919)
      ·
        refine ⟨32958835713829192686089879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21972557142552795124059919 32958835713829192686089879)
        ·
          refine ⟨49438253570743789029134819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32958835713829192686089879 49438253570743789029134819)
          ·
            refine ⟨74157380356115683543702229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49438253570743789029134819 74157380356115683543702229)
            ·
              refine ⟨1738063602096461333055521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74157380356115683543702229 1738063602096461333055521)
              ·
                refine ⟨1303547701572345999791641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738063602096461333055521 1303547701572345999791641)
                ·
                  refine ⟨977660776179259499843731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303547701572345999791641 977660776179259499843731)
                  ·
                    refine ⟨1466491164268889249765597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 977660776179259499843731 1466491164268889249765597)
                    ·
                      refine ⟨549934186600833468662099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1466491164268889249765597 549934186600833468662099)
                      ·
                        rfl

theorem cell23_1070993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_1070993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1070993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1070993 prefixEnd_1070993 := by exact prefixLift 1070993
  have htrace : WordTrace (prefixWord ++ tailWord_1070993) baseStart_1070993 baseEnd_1070993 := by
    simpa [prefixWord, tailWord_1070993, baseEnd_1070993] using wordTrace_append hprefix tailTrace_1070993
  have hstable : (prefixWord ++ tailWord_1070993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070993).length < 2 ^ (prefixWord ++ tailWord_1070993).sum := by decide
  have hdescent : baseEnd_1070993 < baseStart_1070993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071010 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1071010 : Nat := 118140960795 + 1071010 * 2 ^ 59
def prefixEnd_1071010 : Nat := 4983230072969 + 3 ^ 40 * 1071010 * 2
def baseEnd_1071010 : Nat := 549942915771959902149521

theorem tailTrace_1071010 : CollatzResearch.WordTrace tailWord_1071010 prefixEnd_1071010 549942915771959902149521 := by
  unfold tailWord_1071010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765735962480289697646621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26041962566614105860390989 9765735962480289697646621)
  ·
    refine ⟨3662150985930108636617483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9765735962480289697646621 3662150985930108636617483)
    ·
      refine ⟨5493226478895162954926225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3662150985930108636617483 5493226478895162954926225)
      ·
        refine ⟨4119919859171372216194669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493226478895162954926225 4119919859171372216194669)
        ·
          refine ⟨1544969947189264581073001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4119919859171372216194669 1544969947189264581073001)
          ·
            refine ⟨1158727460391948435804751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544969947189264581073001 1158727460391948435804751)
            ·
              refine ⟨1738091190587922653707127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158727460391948435804751 1738091190587922653707127)
              ·
                refine ⟨2607136785881883980560691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738091190587922653707127 2607136785881883980560691)
                ·
                  refine ⟨3910705178822825970841037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607136785881883980560691 3910705178822825970841037)
                  ·
                    refine ⟨1466514442058559739065389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3910705178822825970841037 1466514442058559739065389)
                    ·
                      refine ⟨549942915771959902149521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1466514442058559739065389 549942915771959902149521)
                      ·
                        rfl

theorem cell23_1071010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1071010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071010 prefixEnd_1071010 := by exact prefixLift 1071010
  have htrace : WordTrace (prefixWord ++ tailWord_1071010) baseStart_1071010 baseEnd_1071010 := by
    simpa [prefixWord, tailWord_1071010, baseEnd_1071010] using wordTrace_append hprefix tailTrace_1071010
  have hstable : (prefixWord ++ tailWord_1071010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071010).length < 2 ^ (prefixWord ++ tailWord_1071010).sum := by decide
  have hdescent : baseEnd_1071010 < baseStart_1071010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071028 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1071028 : Nat := 118140960795 + 1071028 * 2 ^ 59
def prefixEnd_1071028 : Nat := 4983230072969 + 3 ^ 40 * 1071028 * 2
def baseEnd_1071028 : Nat := 549952158423740831724439

theorem tailTrace_1071028 : CollatzResearch.WordTrace tailWord_1071028 prefixEnd_1071028 549952158423740831724439 := by
  unfold tailWord_1071028
  simp only [CollatzResearch.WordTrace]
  refine ⟨19531800181927973932370869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26042400242570631909827825 19531800181927973932370869)
  ·
    refine ⟨1831106267055747556159769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19531800181927973932370869 1831106267055747556159769)
    ·
      refine ⟨1373329700291810667119827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1831106267055747556159769 1373329700291810667119827)
      ·
        refine ⟨2059994550437716000679741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373329700291810667119827 2059994550437716000679741)
        ·
          refine ⟨772497956414143500254903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2059994550437716000679741 772497956414143500254903)
          ·
            refine ⟨1158746934621215250382355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772497956414143500254903 1158746934621215250382355)
            ·
              refine ⟨1738120401931822875573533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158746934621215250382355 1738120401931822875573533)
              ·
                refine ⟨651795150724433578340075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1738120401931822875573533 651795150724433578340075)
                ·
                  refine ⟨977692726086650367510113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651795150724433578340075 977692726086650367510113)
                  ·
                    refine ⟨733269544564987775632585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 977692726086650367510113 733269544564987775632585)
                    ·
                      refine ⟨549952158423740831724439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733269544564987775632585 549952158423740831724439)
                      ·
                        rfl

theorem cell23_1071028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1071028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071028 prefixEnd_1071028 := by exact prefixLift 1071028
  have htrace : WordTrace (prefixWord ++ tailWord_1071028) baseStart_1071028 baseEnd_1071028 := by
    simpa [prefixWord, tailWord_1071028, baseEnd_1071028] using wordTrace_append hprefix tailTrace_1071028
  have hstable : (prefixWord ++ tailWord_1071028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071028).length < 2 ^ (prefixWord ++ tailWord_1071028).sum := by decide
  have hdescent : baseEnd_1071028 < baseStart_1071028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071033 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 6, 2, 2]
def baseStart_1071033 : Nat := 118140960795 + 1071033 * 2 ^ 59
def prefixEnd_1071033 : Nat := 4983230072969 + 3 ^ 40 * 1071033 * 2
def baseEnd_1071033 : Nat := 549954725827013312161915

theorem tailTrace_1071033 : CollatzResearch.WordTrace tailWord_1071033 prefixEnd_1071033 549954725827013312161915 := by
  unfold tailWord_1071033
  simp only [CollatzResearch.WordTrace]
  refine ⟨39063782728837833718673753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26042521819225222479115835 39063782728837833718673753)
  ·
    refine ⟨29297837046628375289005315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39063782728837833718673753 29297837046628375289005315)
    ·
      refine ⟨43946755569942562933507973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29297837046628375289005315 43946755569942562933507973)
      ·
        refine ⟨8240016669364230550032745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43946755569942562933507973 8240016669364230550032745)
        ·
          refine ⟨6180012502023172912524559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8240016669364230550032745 6180012502023172912524559)
          ·
            refine ⟨9270018753034759368786839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6180012502023172912524559 9270018753034759368786839)
            ·
              refine ⟨13905028129552139053180259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9270018753034759368786839 13905028129552139053180259)
              ·
                refine ⟨20857542194328208579770389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13905028129552139053180259 20857542194328208579770389)
                ·
                  refine ⟨977697290359134777176737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20857542194328208579770389 977697290359134777176737)
                  ·
                    refine ⟨733272967769351082882553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 977697290359134777176737 733272967769351082882553)
                    ·
                      refine ⟨549954725827013312161915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733272967769351082882553 549954725827013312161915)
                      ·
                        rfl

theorem cell23_1071033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_1071033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071033 prefixEnd_1071033 := by exact prefixLift 1071033
  have htrace : WordTrace (prefixWord ++ tailWord_1071033) baseStart_1071033 baseEnd_1071033 := by
    simpa [prefixWord, tailWord_1071033, baseEnd_1071033] using wordTrace_append hprefix tailTrace_1071033
  have hstable : (prefixWord ++ tailWord_1071033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071033).length < 2 ^ (prefixWord ++ tailWord_1071033).sum := by decide
  have hdescent : baseEnd_1071033 < baseStart_1071033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071056 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 5]
def baseStart_1071056 : Nat := 118140960795 + 1071056 * 2 ^ 59
def prefixEnd_1071056 : Nat := 4983230072969 + 3 ^ 40 * 1071056 * 2
def baseEnd_1071056 : Nat := 61107392875785191352701

theorem tailTrace_1071056 : CollatzResearch.WordTrace tailWord_1071056 prefixEnd_1071056 61107392875785191352701 := by
  unfold tailWord_1071056
  simp only [CollatzResearch.WordTrace]
  refine ⟨19532310803877254323380511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26043081071836339097840681 19532310803877254323380511)
  ·
    refine ⟨29298466205815881485070767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19532310803877254323380511 29298466205815881485070767)
    ·
      refine ⟨43947699308723822227606151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29298466205815881485070767 43947699308723822227606151)
      ·
        refine ⟨65921548963085733341409227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43947699308723822227606151 65921548963085733341409227)
        ·
          refine ⟨98882323444628600012113841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65921548963085733341409227 98882323444628600012113841)
          ·
            refine ⟨74161742583471450009085381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98882323444628600012113841 74161742583471450009085381)
            ·
              refine ⟨13905326734400896876703509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74161742583471450009085381 13905326734400896876703509)
              ·
                refine ⟨651812190675042041095477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13905326734400896876703509 651812190675042041095477)
                ·
                  refine ⟨61107392875785191352701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 651812190675042041095477 61107392875785191352701)
                  ·
                    rfl

theorem cell23_1071056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 5].length) (baseStart_1071056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071056 prefixEnd_1071056 := by exact prefixLift 1071056
  have htrace : WordTrace (prefixWord ++ tailWord_1071056) baseStart_1071056 baseEnd_1071056 := by
    simpa [prefixWord, tailWord_1071056, baseEnd_1071056] using wordTrace_append hprefix tailTrace_1071056
  have hstable : (prefixWord ++ tailWord_1071056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071056).length < 2 ^ (prefixWord ++ tailWord_1071056).sum := by decide
  have hdescent : baseEnd_1071056 < baseStart_1071056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071129 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 10]
def baseStart_1071129 : Nat := 118140960795 + 1071129 * 2 ^ 59
def prefixEnd_1071129 : Nat := 4983230072969 + 3 ^ 40 * 1071129 * 2
def baseEnd_1071129 : Nat := 61111557774427215173497

theorem tailTrace_1071129 : CollatzResearch.WordTrace tailWord_1071129 prefixEnd_1071129 61111557774427215173497 := by
  unfold tailWord_1071129
  simp only [CollatzResearch.WordTrace]
  refine ⟨39067284136490042114168441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26044856090993361409445627 39067284136490042114168441)
  ·
    refine ⟨29300463102367531585626331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39067284136490042114168441 29300463102367531585626331)
    ·
      refine ⟨43950694653551297378439497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29300463102367531585626331 43950694653551297378439497)
      ·
        refine ⟨32963020990163473033829623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43950694653551297378439497 32963020990163473033829623)
        ·
          refine ⟨49444531485245209550744435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32963020990163473033829623 49444531485245209550744435)
          ·
            refine ⟨74166797227867814326116653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49444531485245209550744435 74166797227867814326116653)
            ·
              refine ⟨27812548960450430372293745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74166797227867814326116653 27812548960450430372293745)
              ·
                refine ⟨20859411720337822779220309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27812548960450430372293745 20859411720337822779220309)
                ·
                  refine ⟨61111557774427215173497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20859411720337822779220309 61111557774427215173497)
                  ·
                    rfl

theorem cell23_1071129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_1071129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071129 prefixEnd_1071129 := by exact prefixLift 1071129
  have htrace : WordTrace (prefixWord ++ tailWord_1071129) baseStart_1071129 baseEnd_1071129 := by
    simpa [prefixWord, tailWord_1071129, baseEnd_1071129] using wordTrace_append hprefix tailTrace_1071129
  have hstable : (prefixWord ++ tailWord_1071129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071129).length < 2 ^ (prefixWord ++ tailWord_1071129).sum := by decide
  have hdescent : baseEnd_1071129 < baseStart_1071129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071133 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1071133 : Nat := 118140960795 + 1071133 * 2 ^ 59
def prefixEnd_1071133 : Nat := 4983230072969 + 3 ^ 40 * 1071133 * 2
def baseEnd_1071133 : Nat := 183335357964154306970485

theorem tailTrace_1071133 : CollatzResearch.WordTrace tailWord_1071133 prefixEnd_1071133 183335357964154306970485 := by
  unfold tailWord_1071133
  simp only [CollatzResearch.WordTrace]
  refine ⟨39067430028475550797314053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26044953352317033864876035 39067430028475550797314053)
  ·
    refine ⟨7325143130339165774496385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39067430028475550797314053 7325143130339165774496385)
    ·
      refine ⟨5493857347754374330872289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7325143130339165774496385 5493857347754374330872289)
      ·
        refine ⟨4120393010815780748154217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493857347754374330872289 4120393010815780748154217)
        ·
          refine ⟨3090294758111835561115663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4120393010815780748154217 3090294758111835561115663)
          ·
            refine ⟨4635442137167753341673495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090294758111835561115663 4635442137167753341673495)
            ·
              refine ⟨6953163205751630012510243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635442137167753341673495 6953163205751630012510243)
              ·
                refine ⟨10429744808627445018765365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953163205751630012510243 10429744808627445018765365)
                ·
                  refine ⟨977788575808822970509253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10429744808627445018765365 977788575808822970509253)
                  ·
                    refine ⟨183335357964154306970485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977788575808822970509253 183335357964154306970485)
                    ·
                      rfl

theorem cell23_1071133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1071133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071133 prefixEnd_1071133 := by exact prefixLift 1071133
  have htrace : WordTrace (prefixWord ++ tailWord_1071133) baseStart_1071133 baseEnd_1071133 := by
    simpa [prefixWord, tailWord_1071133, baseEnd_1071133] using wordTrace_append hprefix tailTrace_1071133
  have hstable : (prefixWord ++ tailWord_1071133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071133).length < 2 ^ (prefixWord ++ tailWord_1071133).sum := by decide
  have hdescent : baseEnd_1071133 < baseStart_1071133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071176 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1071176 : Nat := 118140960795 + 1071176 * 2 ^ 59
def prefixEnd_1071176 : Nat := 4983230072969 + 3 ^ 40 * 1071176 * 2
def baseEnd_1071176 : Nat := 183342717853535417557919

theorem tailTrace_1071176 : CollatzResearch.WordTrace tailWord_1071176 prefixEnd_1071176 183342717853535417557919 := by
  unfold tailWord_1071176
  simp only [CollatzResearch.WordTrace]
  refine ⟨19534499183659884570564691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26045998911546512760752921 19534499183659884570564691)
  ·
    refine ⟨29301748775489826855847037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19534499183659884570564691 29301748775489826855847037)
    ·
      refine ⟨10988155790808685070942639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29301748775489826855847037 10988155790808685070942639)
      ·
        refine ⟨16482233686213027606413959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10988155790808685070942639 16482233686213027606413959)
        ·
          refine ⟨24723350529319541409620939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16482233686213027606413959 24723350529319541409620939)
          ·
            refine ⟨37085025793979312114431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24723350529319541409620939 37085025793979312114431409)
            ·
              refine ⟨27813769345484484085823557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37085025793979312114431409 27813769345484484085823557)
              ·
                refine ⟨5215081752278340766091917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27813769345484484085823557 5215081752278340766091917)
                ·
                  refine ⟨1955655657104377787284469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5215081752278340766091917 1955655657104377787284469)
                  ·
                    refine ⟨183342717853535417557919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1955655657104377787284469 183342717853535417557919)
                    ·
                      rfl

theorem cell23_1071176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1071176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071176 prefixEnd_1071176 := by exact prefixLift 1071176
  have htrace : WordTrace (prefixWord ++ tailWord_1071176) baseStart_1071176 baseEnd_1071176 := by
    simpa [prefixWord, tailWord_1071176, baseEnd_1071176] using wordTrace_append hprefix tailTrace_1071176
  have hstable : (prefixWord ++ tailWord_1071176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071176).length < 2 ^ (prefixWord ++ tailWord_1071176).sum := by decide
  have hdescent : baseEnd_1071176 < baseStart_1071176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071183 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 4, 3, 2]
def baseStart_1071183 : Nat := 118140960795 + 1071183 * 2 ^ 59
def prefixEnd_1071183 : Nat := 4983230072969 + 3 ^ 40 * 1071183 * 2
def baseEnd_1071183 : Nat := 550031747925187725286225

theorem tailTrace_1071183 : CollatzResearch.WordTrace tailWord_1071183 prefixEnd_1071183 550031747925187725286225 := by
  unfold tailWord_1071183
  simp only [CollatzResearch.WordTrace]
  refine ⟨39069253678294409336634203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26046169118862939557756135 39069253678294409336634203)
  ·
    refine ⟨58603880517441614004951305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39069253678294409336634203 58603880517441614004951305)
    ·
      refine ⟨43952910388081210503713479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58603880517441614004951305 43952910388081210503713479)
      ·
        refine ⟨65929365582121815755570219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43952910388081210503713479 65929365582121815755570219)
        ·
          refine ⟨98894048373182723633355329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65929365582121815755570219 98894048373182723633355329)
          ·
            refine ⟨74170536279887042725016497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98894048373182723633355329 74170536279887042725016497)
            ·
              refine ⟨55627902209915282043762373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74170536279887042725016497 55627902209915282043762373)
              ·
                refine ⟨10430231664359115383205445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55627902209915282043762373 10430231664359115383205445)
                ·
                  refine ⟨1955668437067334134351021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10430231664359115383205445 1955668437067334134351021)
                  ·
                    refine ⟨733375663900250300381633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955668437067334134351021 733375663900250300381633)
                    ·
                      refine ⟨550031747925187725286225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733375663900250300381633 550031747925187725286225)
                      ·
                        rfl

theorem cell23_1071183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3, 2].length) (baseStart_1071183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071183 prefixEnd_1071183 := by exact prefixLift 1071183
  have htrace : WordTrace (prefixWord ++ tailWord_1071183) baseStart_1071183 baseEnd_1071183 := by
    simpa [prefixWord, tailWord_1071183, baseEnd_1071183] using wordTrace_append hprefix tailTrace_1071183
  have hstable : (prefixWord ++ tailWord_1071183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071183).length < 2 ^ (prefixWord ++ tailWord_1071183).sum := by decide
  have hdescent : baseEnd_1071183 < baseStart_1071183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071193 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 1, 5]
def baseStart_1071193 : Nat := 118140960795 + 1071193 * 2 ^ 59
def prefixEnd_1071193 : Nat := 4983230072969 + 3 ^ 40 * 1071193 * 2
def baseEnd_1071193 : Nat := 183345627577244228720393

theorem tailTrace_1071193 : CollatzResearch.WordTrace tailWord_1071193 prefixEnd_1071193 183345627577244228720393 := by
  unfold tailWord_1071193
  simp only [CollatzResearch.WordTrace]
  refine ⟨39069618408258181044498233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26046412272172120696332155 39069618408258181044498233)
  ·
    refine ⟨29302213806193635783373675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39069618408258181044498233 29302213806193635783373675)
    ·
      refine ⟨43953320709290453675060513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29302213806193635783373675 43953320709290453675060513)
      ·
        refine ⟨32964990531967840256295385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43953320709290453675060513 32964990531967840256295385)
        ·
          refine ⟨24723742898975880192221539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32964990531967840256295385 24723742898975880192221539)
          ·
            refine ⟨37085614348463820288332309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24723742898975880192221539 37085614348463820288332309)
            ·
              refine ⟨1738388172584241576015577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37085614348463820288332309 1738388172584241576015577)
              ·
                refine ⟨1303791129438181182011683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738388172584241576015577 1303791129438181182011683)
                ·
                  refine ⟨1955686694157271773017525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303791129438181182011683 1955686694157271773017525)
                  ·
                    refine ⟨183345627577244228720393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1955686694157271773017525 183345627577244228720393)
                    ·
                      rfl

theorem cell23_1071193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_1071193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071193 prefixEnd_1071193 := by exact prefixLift 1071193
  have htrace : WordTrace (prefixWord ++ tailWord_1071193) baseStart_1071193 baseEnd_1071193 := by
    simpa [prefixWord, tailWord_1071193, baseEnd_1071193] using wordTrace_append hprefix tailTrace_1071193
  have hstable : (prefixWord ++ tailWord_1071193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071193).length < 2 ^ (prefixWord ++ tailWord_1071193).sum := by decide
  have hdescent : baseEnd_1071193 < baseStart_1071193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071223 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 4, 4]
def baseStart_1071223 : Nat := 118140960795 + 1071223 * 2 ^ 59
def prefixEnd_1071223 : Nat := 4983230072969 + 3 ^ 40 * 1071223 * 2
def baseEnd_1071223 : Nat := 183350762383789189595347

theorem tailTrace_1071223 : CollatzResearch.WordTrace tailWord_1071223 prefixEnd_1071223 183350762383789189595347 := by
  unfold tailWord_1071223
  simp only [CollatzResearch.WordTrace]
  refine ⟨39070712598149496168090323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26047141732099664112060215 39070712598149496168090323)
  ·
    refine ⟨58606068897224244252135485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39070712598149496168090323 58606068897224244252135485)
    ·
      refine ⟨21977275836459091594550807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58606068897224244252135485 21977275836459091594550807)
      ·
        refine ⟨32965913754688637391826211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21977275836459091594550807 32965913754688637391826211)
        ·
          refine ⟨49448870632032956087739317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32965913754688637391826211 49448870632032956087739317)
          ·
            refine ⟨4635831621753089633225561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49448870632032956087739317 4635831621753089633225561)
            ·
              refine ⟨3476873716314817224919171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4635831621753089633225561 3476873716314817224919171)
              ·
                refine ⟨5215310574472225837378757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476873716314817224919171 5215310574472225837378757)
                ·
                  refine ⟨977870732713542344508517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5215310574472225837378757 977870732713542344508517)
                  ·
                    refine ⟨183350762383789189595347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977870732713542344508517 183350762383789189595347)
                    ·
                      rfl

theorem cell23_1071223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_1071223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071223 prefixEnd_1071223 := by exact prefixLift 1071223
  have htrace : WordTrace (prefixWord ++ tailWord_1071223) baseStart_1071223 baseEnd_1071223 := by
    simpa [prefixWord, tailWord_1071223, baseEnd_1071223] using wordTrace_append hprefix tailTrace_1071223
  have hstable : (prefixWord ++ tailWord_1071223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071223).length < 2 ^ (prefixWord ++ tailWord_1071223).sum := by decide
  have hdescent : baseEnd_1071223 < baseStart_1071223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071250 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1071250 : Nat := 118140960795 + 1071250 * 2 ^ 59
def prefixEnd_1071250 : Nat := 4983230072969 + 3 ^ 40 * 1071250 * 2
def baseEnd_1071250 : Nat := 550066151129038963148417

theorem tailTrace_1071250 : CollatzResearch.WordTrace tailWord_1071250 prefixEnd_1071250 550066151129038963148417 := by
  unfold tailWord_1071250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9767924342262919944830801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26047798246034453186215469 9767924342262919944830801)
  ·
    refine ⟨7325943256697189958623101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9767924342262919944830801 7325943256697189958623101)
    ·
      refine ⟨2747228721261446234483663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7325943256697189958623101 2747228721261446234483663)
      ·
        refine ⟨4120843081892169351725495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747228721261446234483663 4120843081892169351725495)
        ·
          refine ⟨6181264622838254027588243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120843081892169351725495 6181264622838254027588243)
          ·
            refine ⟨9271896934257381041382365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6181264622838254027588243 9271896934257381041382365)
            ·
              refine ⟨3476961350346517890518387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9271896934257381041382365 3476961350346517890518387)
              ·
                refine ⟨5215442025519776835777581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476961350346517890518387 5215442025519776835777581)
                ·
                  refine ⟨1955790759569916313416593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5215442025519776835777581 1955790759569916313416593)
                  ·
                    refine ⟨1466843069677437235062445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1955790759569916313416593 1466843069677437235062445)
                    ·
                      refine ⟨550066151129038963148417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1466843069677437235062445 550066151129038963148417)
                      ·
                        rfl

theorem cell23_1071250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1071250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071250 prefixEnd_1071250 := by exact prefixLift 1071250
  have htrace : WordTrace (prefixWord ++ tailWord_1071250) baseStart_1071250 baseEnd_1071250 := by
    simpa [prefixWord, tailWord_1071250, baseEnd_1071250] using wordTrace_append hprefix tailTrace_1071250
  have hstable : (prefixWord ++ tailWord_1071250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071250).length < 2 ^ (prefixWord ++ tailWord_1071250).sum := by decide
  have hdescent : baseEnd_1071250 < baseStart_1071250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071274 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1071274 : Nat := 118140960795 + 1071274 * 2 ^ 59
def prefixEnd_1071274 : Nat := 4983230072969 + 3 ^ 40 * 1071274 * 2
def baseEnd_1071274 : Nat := 183359491554915623082769

theorem tailTrace_1071274 : CollatzResearch.WordTrace tailWord_1071274 prefixEnd_1071274 183359491554915623082769 := by
  unfold tailWord_1071274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768143180241182969549219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26048381813976487918797917 9768143180241182969549219)
  ·
    refine ⟨14652214770361774454323829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9768143180241182969549219 14652214770361774454323829)
    ·
      refine ⟨1373645134721416355092859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14652214770361774454323829 1373645134721416355092859)
      ·
        refine ⟨2060467702082124532639289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373645134721416355092859 2060467702082124532639289)
        ·
          refine ⟨1545350776561593399479467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2060467702082124532639289 1545350776561593399479467)
          ·
            refine ⟨2318026164842390099219201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545350776561593399479467 2318026164842390099219201)
            ·
              refine ⟨1738519623631792574414401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2318026164842390099219201 1738519623631792574414401)
              ·
                refine ⟨1303889717723844430810801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738519623631792574414401 1303889717723844430810801)
                ·
                  refine ⟨977917288292883323108101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303889717723844430810801 977917288292883323108101)
                  ·
                    refine ⟨183359491554915623082769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977917288292883323108101 183359491554915623082769)
                    ·
                      rfl

theorem cell23_1071274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1071274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071274 prefixEnd_1071274 := by exact prefixLift 1071274
  have htrace : WordTrace (prefixWord ++ tailWord_1071274) baseStart_1071274 baseEnd_1071274 := by
    simpa [prefixWord, tailWord_1071274, baseEnd_1071274] using wordTrace_append hprefix tailTrace_1071274
  have hstable : (prefixWord ++ tailWord_1071274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071274).length < 2 ^ (prefixWord ++ tailWord_1071274).sum := by decide
  have hdescent : baseEnd_1071274 < baseStart_1071274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071276 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_1071276 : Nat := 118140960795 + 1071276 * 2 ^ 59
def prefixEnd_1071276 : Nat := 4983230072969 + 3 ^ 40 * 1071276 * 2
def baseEnd_1071276 : Nat := 550079501626055861423297

theorem tailTrace_1071276 : CollatzResearch.WordTrace tailWord_1071276 prefixEnd_1071276 550079501626055861423297 := by
  unfold tailWord_1071276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19536322833478743109884841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26048430444638324146513121 19536322833478743109884841)
  ·
    refine ⟨14652242125109057332413631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19536322833478743109884841 14652242125109057332413631)
    ·
      refine ⟨21978363187663585998620447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14652242125109057332413631 21978363187663585998620447)
      ·
        refine ⟨32967544781495378997930671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21978363187663585998620447 32967544781495378997930671)
        ·
          refine ⟨49451317172243068496896007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32967544781495378997930671 49451317172243068496896007)
          ·
            refine ⟨74176975758364602745344011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49451317172243068496896007 74176975758364602745344011)
            ·
              refine ⟨111265463637546904118016017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74176975758364602745344011 111265463637546904118016017)
              ·
                refine ⟨83449097728160178088512013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111265463637546904118016017 83449097728160178088512013)
                ·
                  refine ⟨31293411648060066783192005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83449097728160178088512013 31293411648060066783192005)
                  ·
                    refine ⟨5867514684011262521848501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31293411648060066783192005 5867514684011262521848501)
                    ·
                      refine ⟨550079501626055861423297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5867514684011262521848501 550079501626055861423297)
                      ·
                        rfl

theorem cell23_1071276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_1071276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071276 prefixEnd_1071276 := by exact prefixLift 1071276
  have htrace : WordTrace (prefixWord ++ tailWord_1071276) baseStart_1071276 baseEnd_1071276 := by
    simpa [prefixWord, tailWord_1071276, baseEnd_1071276] using wordTrace_append hprefix tailTrace_1071276
  have hstable : (prefixWord ++ tailWord_1071276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071276).length < 2 ^ (prefixWord ++ tailWord_1071276).sum := by decide
  have hdescent : baseEnd_1071276 < baseStart_1071276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071281 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1071281 : Nat := 118140960795 + 1071281 * 2 ^ 59
def prefixEnd_1071281 : Nat := 4983230072969 + 3 ^ 40 * 1071281 * 2
def baseEnd_1071281 : Nat := 550082069029328341860775

theorem tailTrace_1071281 : CollatzResearch.WordTrace tailWord_1071281 prefixEnd_1071281 550082069029328341860775 := by
  unfold tailWord_1071281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39072828031939372073701697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26048552021292914715801131 39072828031939372073701697)
  ·
    refine ⟨29304621023954529055276273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39072828031939372073701697 29304621023954529055276273)
    ·
      refine ⟨21978465767965896791457205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29304621023954529055276273 21978465767965896791457205)
      ·
        refine ⟨2060481165746802824199113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21978465767965896791457205 2060481165746802824199113)
        ·
          refine ⟨1545360874310102118149335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2060481165746802824199113 1545360874310102118149335)
          ·
            refine ⟨2318041311465153177224003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545360874310102118149335 2318041311465153177224003)
            ·
              refine ⟨3477061967197729765836005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318041311465153177224003 3477061967197729765836005)
              ·
                refine ⟨651949118849574331094251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3477061967197729765836005 651949118849574331094251)
                ·
                  refine ⟨977923678274361496641377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651949118849574331094251 977923678274361496641377)
                  ·
                    refine ⟨733442758705771122481033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 977923678274361496641377 733442758705771122481033)
                    ·
                      refine ⟨550082069029328341860775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733442758705771122481033 550082069029328341860775)
                      ·
                        rfl

theorem cell23_1071281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1071281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071281 prefixEnd_1071281 := by exact prefixLift 1071281
  have htrace : WordTrace (prefixWord ++ tailWord_1071281) baseStart_1071281 baseEnd_1071281 := by
    simpa [prefixWord, tailWord_1071281, baseEnd_1071281] using wordTrace_append hprefix tailTrace_1071281
  have hstable : (prefixWord ++ tailWord_1071281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071281).length < 2 ^ (prefixWord ++ tailWord_1071281).sum := by decide
  have hdescent : baseEnd_1071281 < baseStart_1071281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071290 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2]
def baseStart_1071290 : Nat := 118140960795 + 1071290 * 2 ^ 59
def prefixEnd_1071290 : Nat := 4983230072969 + 3 ^ 40 * 1071290 * 2
def baseEnd_1071290 : Nat := 550086690355218806648233

theorem tailTrace_1071290 : CollatzResearch.WordTrace tailWord_1071290 prefixEnd_1071290 550086690355218806648233 := by
  unfold tailWord_1071290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768289072226691652694831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26048770859271177740519549 9768289072226691652694831)
  ·
    refine ⟨14652433608340037479042247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9768289072226691652694831 14652433608340037479042247)
    ·
      refine ⟨21978650412510056218563371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14652433608340037479042247 21978650412510056218563371)
      ·
        refine ⟨32967975618765084327845057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21978650412510056218563371 32967975618765084327845057)
        ·
          refine ⟨24725981714073813245883793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32967975618765084327845057 24725981714073813245883793)
          ·
            refine ⟨18544486285555359934412845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24725981714073813245883793 18544486285555359934412845)
            ·
              refine ⟨6954182357083259975404817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18544486285555359934412845 6954182357083259975404817)
              ·
                refine ⟨5215636767812444981553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6954182357083259975404817 5215636767812444981553613)
                ·
                  refine ⟨1955863787929666868082605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5215636767812444981553613 1955863787929666868082605)
                  ·
                    refine ⟨733448920473625075530977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955863787929666868082605 733448920473625075530977)
                    ·
                      refine ⟨550086690355218806648233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733448920473625075530977 550086690355218806648233)
                      ·
                        rfl

theorem cell23_1071290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_1071290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071290 prefixEnd_1071290 := by exact prefixLift 1071290
  have htrace : WordTrace (prefixWord ++ tailWord_1071290) baseStart_1071290 baseEnd_1071290 := by
    simpa [prefixWord, tailWord_1071290, baseEnd_1071290] using wordTrace_append hprefix tailTrace_1071290
  have hstable : (prefixWord ++ tailWord_1071290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071290).length < 2 ^ (prefixWord ++ tailWord_1071290).sum := by decide
  have hdescent : baseEnd_1071290 < baseStart_1071290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071331 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1071331 : Nat := 118140960795 + 1071331 * 2 ^ 59
def prefixEnd_1071331 : Nat := 4983230072969 + 3 ^ 40 * 1071331 * 2
def baseEnd_1071331 : Nat := 550107743062053146235545

theorem tailTrace_1071331 : CollatzResearch.WordTrace tailWord_1071331 prefixEnd_1071331 550107743062053146235545 := by
  unfold tailWord_1071331
  simp only [CollatzResearch.WordTrace]
  refine ⟨39074651681758230613021847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26049767787838820408681231 39074651681758230613021847)
  ·
    refine ⟨58611977522637345919532771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39074651681758230613021847 58611977522637345919532771)
    ·
      refine ⟨87917966283956018879299157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58611977522637345919532771 87917966283956018879299157)
      ·
        refine ⟨1030288667390109596241787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 87917966283956018879299157 1030288667390109596241787)
        ·
          refine ⟨1545433001085164394362681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030288667390109596241787 1545433001085164394362681)
          ·
            refine ⟨1159074750813873295772011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1545433001085164394362681 1159074750813873295772011)
            ·
              refine ⟨1738612126220809943658017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159074750813873295772011 1738612126220809943658017)
              ·
                refine ⟨1303959094665607457743513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738612126220809943658017 1303959094665607457743513)
                ·
                  refine ⟨977969320999205593307635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303959094665607457743513 977969320999205593307635)
                  ·
                    refine ⟨1466953981498808389961453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 977969320999205593307635 1466953981498808389961453)
                    ·
                      refine ⟨550107743062053146235545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1466953981498808389961453 550107743062053146235545)
                      ·
                        rfl

theorem cell23_1071331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1071331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071331 prefixEnd_1071331 := by exact prefixLift 1071331
  have htrace : WordTrace (prefixWord ++ tailWord_1071331) baseStart_1071331 baseEnd_1071331 := by
    simpa [prefixWord, tailWord_1071331, baseEnd_1071331] using wordTrace_append hprefix tailTrace_1071331
  have hstable : (prefixWord ++ tailWord_1071331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071331).length < 2 ^ (prefixWord ++ tailWord_1071331).sum := by decide
  have hdescent : baseEnd_1071331 < baseStart_1071331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071343 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 7]
def baseStart_1071343 : Nat := 118140960795 + 1071343 * 2 ^ 59
def prefixEnd_1071343 : Nat := 4983230072969 + 3 ^ 40 * 1071343 * 2
def baseEnd_1071343 : Nat := 61123767203323011031721

theorem tailTrace_1071343 : CollatzResearch.WordTrace tailWord_1071343 prefixEnd_1071343 61123767203323011031721 := by
  unfold tailWord_1071343
  simp only [CollatzResearch.WordTrace]
  refine ⟨39075089357714756662458683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26050059571809837774972455 39075089357714756662458683)
  ·
    refine ⟨58612634036572134993688025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39075089357714756662458683 58612634036572134993688025)
    ·
      refine ⟨43959475527429101245266019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58612634036572134993688025 43959475527429101245266019)
      ·
        refine ⟨65939213291143651867899029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43959475527429101245266019 65939213291143651867899029)
        ·
          refine ⟨3090900623022358681307767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65939213291143651867899029 3090900623022358681307767)
          ·
            refine ⟨4636350934533538021961651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090900623022358681307767 4636350934533538021961651)
            ·
              refine ⟨6954526401800307032942477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636350934533538021961651 6954526401800307032942477)
              ·
                refine ⟨2607947400675115137353429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6954526401800307032942477 2607947400675115137353429)
                ·
                  refine ⟨61123767203323011031721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2607947400675115137353429 61123767203323011031721)
                  ·
                    rfl

theorem cell23_1071343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 7].length) (baseStart_1071343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071343 prefixEnd_1071343 := by exact prefixLift 1071343
  have htrace : WordTrace (prefixWord ++ tailWord_1071343) baseStart_1071343 baseEnd_1071343 := by
    simpa [prefixWord, tailWord_1071343, baseEnd_1071343] using wordTrace_append hprefix tailTrace_1071343
  have hstable : (prefixWord ++ tailWord_1071343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071343).length < 2 ^ (prefixWord ++ tailWord_1071343).sum := by decide
  have hdescent : baseEnd_1071343 < baseStart_1071343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071350 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1071350 : Nat := 118140960795 + 1071350 * 2 ^ 59
def prefixEnd_1071350 : Nat := 4983230072969 + 3 ^ 40 * 1071350 * 2
def baseEnd_1071350 : Nat := 550117499194488571897957

theorem tailTrace_1071350 : CollatzResearch.WordTrace tailWord_1071350 prefixEnd_1071350 550117499194488571897957 := by
  unfold tailWord_1071350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442209041793087303622719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26050229779126264571975669 2442209041793087303622719)
  ·
    refine ⟨3663313562689630955434079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2442209041793087303622719 3663313562689630955434079)
    ·
      refine ⟨5494970344034446433151119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663313562689630955434079 5494970344034446433151119)
      ·
        refine ⟨8242455516051669649726679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494970344034446433151119 8242455516051669649726679)
        ·
          refine ⟨12363683274077504474590019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8242455516051669649726679 12363683274077504474590019)
          ·
            refine ⟨18545524911116256711885029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12363683274077504474590019 18545524911116256711885029)
            ·
              refine ⟨3477285920834298133478443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18545524911116256711885029 3477285920834298133478443)
              ·
                refine ⟨5215928881251447200217665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477285920834298133478443 5215928881251447200217665)
                ·
                  refine ⟨3911946660938585400163249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5215928881251447200217665 3911946660938585400163249)
                  ·
                    refine ⟨2933959995703939050122437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3911946660938585400163249 2933959995703939050122437)
                    ·
                      refine ⟨550117499194488571897957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2933959995703939050122437 550117499194488571897957)
                      ·
                        rfl

theorem cell23_1071350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1071350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071350 prefixEnd_1071350 := by exact prefixLift 1071350
  have htrace : WordTrace (prefixWord ++ tailWord_1071350) baseStart_1071350 baseEnd_1071350 := by
    simpa [prefixWord, tailWord_1071350, baseEnd_1071350] using wordTrace_append hprefix tailTrace_1071350
  have hstable : (prefixWord ++ tailWord_1071350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071350).length < 2 ^ (prefixWord ++ tailWord_1071350).sum := by decide
  have hdescent : baseEnd_1071350 < baseStart_1071350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071353 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_1071353 : Nat := 118140960795 + 1071353 * 2 ^ 59
def prefixEnd_1071353 : Nat := 4983230072969 + 3 ^ 40 * 1071353 * 2
def baseEnd_1071353 : Nat := 550119039636452060160443

theorem tailTrace_1071353 : CollatzResearch.WordTrace tailWord_1071353 prefixEnd_1071353 550119039636452060160443 := by
  unfold tailWord_1071353
  simp only [CollatzResearch.WordTrace]
  refine ⟨39075454087678528370322713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26050302725119018913548475 39075454087678528370322713)
  ·
    refine ⟨29306590565758896277742035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39075454087678528370322713 29306590565758896277742035)
    ·
      refine ⟨43959885848638344416613053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29306590565758896277742035 43959885848638344416613053)
      ·
        refine ⟨16484957193239379156229895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43959885848638344416613053 16484957193239379156229895)
        ·
          refine ⟨24727435789859068734344843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16484957193239379156229895 24727435789859068734344843)
          ·
            refine ⟨37091153684788603101517265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24727435789859068734344843 37091153684788603101517265)
            ·
              refine ⟨27818365263591452326137949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37091153684788603101517265 27818365263591452326137949)
              ·
                refine ⟨10431886973846794622301731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27818365263591452326137949 10431886973846794622301731)
                ·
                  refine ⟨15647830460770191933452597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10431886973846794622301731 15647830460770191933452597)
                  ·
                    refine ⟨1466984105697205493761181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15647830460770191933452597 1466984105697205493761181)
                    ·
                      refine ⟨550119039636452060160443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1466984105697205493761181 550119039636452060160443)
                      ·
                        rfl

theorem cell23_1071353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_1071353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071353 prefixEnd_1071353 := by exact prefixLift 1071353
  have htrace : WordTrace (prefixWord ++ tailWord_1071353) baseStart_1071353 baseEnd_1071353 := by
    simpa [prefixWord, tailWord_1071353, baseEnd_1071353] using wordTrace_append hprefix tailTrace_1071353
  have hstable : (prefixWord ++ tailWord_1071353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071353).length < 2 ^ (prefixWord ++ tailWord_1071353).sum := by decide
  have hdescent : baseEnd_1071353 < baseStart_1071353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071377 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 5]
def baseStart_1071377 : Nat := 118140960795 + 1071377 * 2 ^ 59
def prefixEnd_1071377 : Nat := 4983230072969 + 3 ^ 40 * 1071377 * 2
def baseEnd_1071377 : Nat := 61125707019128885140037

theorem tailTrace_1071377 : CollatzResearch.WordTrace tailWord_1071377 prefixEnd_1071377 61125707019128885140037 := by
  unfold tailWord_1071377
  simp only [CollatzResearch.WordTrace]
  refine ⟨39076329439591580469196385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26050886293061053646130923 39076329439591580469196385)
  ·
    refine ⟨29307247079693685351897289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39076329439591580469196385 29307247079693685351897289)
    ·
      refine ⟨21980435309770264013922967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29307247079693685351897289 21980435309770264013922967)
      ·
        refine ⟨32970652964655396020884451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21980435309770264013922967 32970652964655396020884451)
        ·
          refine ⟨49455979446983094031326677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32970652964655396020884451 49455979446983094031326677)
          ·
            refine ⟨1159124518288666266359219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 49455979446983094031326677 1159124518288666266359219)
            ·
              refine ⟨1738686777432999399538829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159124518288666266359219 1738686777432999399538829)
              ·
                refine ⟨652007541537374774827061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1738686777432999399538829 652007541537374774827061)
                ·
                  refine ⟨61125707019128885140037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 652007541537374774827061 61125707019128885140037)
                  ·
                    rfl

theorem cell23_1071377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 5].length) (baseStart_1071377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071377 prefixEnd_1071377 := by exact prefixLift 1071377
  have htrace : WordTrace (prefixWord ++ tailWord_1071377) baseStart_1071377 baseEnd_1071377 := by
    simpa [prefixWord, tailWord_1071377, baseEnd_1071377] using wordTrace_append hprefix tailTrace_1071377
  have hstable : (prefixWord ++ tailWord_1071377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071377).length < 2 ^ (prefixWord ++ tailWord_1071377).sum := by decide
  have hdescent : baseEnd_1071377 < baseStart_1071377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071394 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1071394 : Nat := 118140960795 + 1071394 * 2 ^ 59
def prefixEnd_1071394 : Nat := 4983230072969 + 3 ^ 40 * 1071394 * 2
def baseEnd_1071394 : Nat := 61126676927031822194195

theorem tailTrace_1071394 : CollatzResearch.WordTrace tailWord_1071394 prefixEnd_1071394 61126676927031822194195 := by
  unfold tailWord_1071394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9769237370132498093141309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26051299653686661581710157 9769237370132498093141309)
  ·
    refine ⟨3663464013799686784927991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9769237370132498093141309 3663464013799686784927991)
    ·
      refine ⟨5495196020699530177391987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663464013799686784927991 5495196020699530177391987)
      ·
        refine ⟨8242794031049295266087981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5495196020699530177391987 8242794031049295266087981)
        ·
          refine ⟨3091047761643485724782993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8242794031049295266087981 3091047761643485724782993)
          ·
            refine ⟨2318285821232614293587245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3091047761643485724782993 2318285821232614293587245)
            ·
              refine ⟨869357182962230360095217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2318285821232614293587245 869357182962230360095217)
              ·
                refine ⟨652017887221672770071413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869357182962230360095217 652017887221672770071413)
                ·
                  refine ⟨61126676927031822194195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 652017887221672770071413 61126676927031822194195)
                  ·
                    rfl

theorem cell23_1071394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1071394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071394 prefixEnd_1071394 := by exact prefixLift 1071394
  have htrace : WordTrace (prefixWord ++ tailWord_1071394) baseStart_1071394 baseEnd_1071394 := by
    simpa [prefixWord, tailWord_1071394, baseEnd_1071394] using wordTrace_append hprefix tailTrace_1071394
  have hstable : (prefixWord ++ tailWord_1071394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071394).length < 2 ^ (prefixWord ++ tailWord_1071394).sum := by decide
  have hdescent : baseEnd_1071394 < baseStart_1071394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071405 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1071405 : Nat := 118140960795 + 1071405 * 2 ^ 59
def prefixEnd_1071405 : Nat := 4983230072969 + 3 ^ 40 * 1071405 * 2
def baseEnd_1071405 : Nat := 550145740630485856710205

theorem tailTrace_1071405 : CollatzResearch.WordTrace tailWord_1071405 prefixEnd_1071405 550145740630485856710205 := by
  unfold tailWord_1071405
  simp only [CollatzResearch.WordTrace]
  refine ⟨39077350683490141251215669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26051567122326760834143779 39077350683490141251215669)
  ·
    refine ⟨3663501626577200742301469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39077350683490141251215669 3663501626577200742301469)
    ·
      refine ⟨1373813109966450278363051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3663501626577200742301469 1373813109966450278363051)
      ·
        refine ⟨2060719664949675417544577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373813109966450278363051 2060719664949675417544577)
        ·
          refine ⟨1545539748712256563158433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2060719664949675417544577 1545539748712256563158433)
          ·
            refine ⟨1159154811534192422368825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1545539748712256563158433 1159154811534192422368825)
            ·
              refine ⟨869366108650644316776619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159154811534192422368825 869366108650644316776619)
              ·
                refine ⟨1304049162975966475164929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869366108650644316776619 1304049162975966475164929)
                ·
                  refine ⟨978036872231974856373697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304049162975966475164929 978036872231974856373697)
                  ·
                    refine ⟨733527654173981142280273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 978036872231974856373697 733527654173981142280273)
                    ·
                      refine ⟨550145740630485856710205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733527654173981142280273 550145740630485856710205)
                      ·
                        rfl

theorem cell23_1071405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1071405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071405 prefixEnd_1071405 := by exact prefixLift 1071405
  have htrace : WordTrace (prefixWord ++ tailWord_1071405) baseStart_1071405 baseEnd_1071405 := by
    simpa [prefixWord, tailWord_1071405, baseEnd_1071405] using wordTrace_append hprefix tailTrace_1071405
  have hstable : (prefixWord ++ tailWord_1071405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071405).length < 2 ^ (prefixWord ++ tailWord_1071405).sum := by decide
  have hdescent : baseEnd_1071405 < baseStart_1071405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071420 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_1071420 : Nat := 118140960795 + 1071420 * 2 ^ 59
def prefixEnd_1071420 : Nat := 4983230072969 + 3 ^ 40 * 1071420 * 2
def baseEnd_1071420 : Nat := 183384480946767766007545

theorem tailTrace_1071420 : CollatzResearch.WordTrace tailWord_1071420 prefixEnd_1071420 183384480946767766007545 := by
  unfold tailWord_1071420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19538948889217899406505857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26051931852290532542007809 19538948889217899406505857)
  ·
    refine ⟨14654211666913424554879393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19538948889217899406505857 14654211666913424554879393)
    ·
      refine ⟨10990658750185068416159545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14654211666913424554879393 10990658750185068416159545)
      ·
        refine ⟨8242994062638801312119659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10990658750185068416159545 8242994062638801312119659)
        ·
          refine ⟨12364491093958201968179489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8242994062638801312119659 12364491093958201968179489)
          ·
            refine ⟨9273368320468651476134617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12364491093958201968179489 9273368320468651476134617)
            ·
              refine ⟨6955026240351488607100963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9273368320468651476134617 6955026240351488607100963)
              ·
                refine ⟨10432539360527232910651445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6955026240351488607100963 10432539360527232910651445)
                ·
                  refine ⟨978050565049428085373573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10432539360527232910651445 978050565049428085373573)
                  ·
                    refine ⟨183384480946767766007545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 978050565049428085373573 183384480946767766007545)
                    ·
                      rfl

theorem cell23_1071420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_1071420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071420 prefixEnd_1071420 := by exact prefixLift 1071420
  have htrace : WordTrace (prefixWord ++ tailWord_1071420) baseStart_1071420 baseEnd_1071420 := by
    simpa [prefixWord, tailWord_1071420, baseEnd_1071420] using wordTrace_append hprefix tailTrace_1071420
  have hstable : (prefixWord ++ tailWord_1071420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071420).length < 2 ^ (prefixWord ++ tailWord_1071420).sum := by decide
  have hdescent : baseEnd_1071420 < baseStart_1071420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071473 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_1071473 : Nat := 118140960795 + 1071473 * 2 ^ 59
def prefixEnd_1071473 : Nat := 4983230072969 + 3 ^ 40 * 1071473 * 2
def baseEnd_1071473 : Nat := 550180657314991590659891

theorem tailTrace_1071473 : CollatzResearch.WordTrace tailWord_1071473 prefixEnd_1071473 550180657314991590659891 := by
  unfold tailWord_1071473
  simp only [CollatzResearch.WordTrace]
  refine ⟨39079830847243788864691073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26053220564829192576460715 39079830847243788864691073)
  ·
    refine ⟨29309873135432841648518305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39079830847243788864691073 29309873135432841648518305)
    ·
      refine ⟨21982404851574631236388729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29309873135432841648518305 21982404851574631236388729)
      ·
        refine ⟨16486803638680973427291547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21982404851574631236388729 16486803638680973427291547)
        ·
          refine ⟨24730205458021460140937321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16486803638680973427291547 24730205458021460140937321)
          ·
            refine ⟨18547654093516095105702991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24730205458021460140937321 18547654093516095105702991)
            ·
              refine ⟨27821481140274142658554487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18547654093516095105702991 27821481140274142658554487)
              ·
                refine ⟨41732221710411213987831731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27821481140274142658554487 41732221710411213987831731)
                ·
                  refine ⟨62598332565616820981747597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41732221710411213987831731 62598332565616820981747597)
                  ·
                    refine ⟨23474374712106307868155349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62598332565616820981747597 23474374712106307868155349)
                    ·
                      refine ⟨550180657314991590659891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23474374712106307868155349 550180657314991590659891)
                      ·
                        rfl

theorem cell23_1071473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_1071473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071473 prefixEnd_1071473 := by exact prefixLift 1071473
  have htrace : WordTrace (prefixWord ++ tailWord_1071473) baseStart_1071473 baseEnd_1071473 := by
    simpa [prefixWord, tailWord_1071473, baseEnd_1071473] using wordTrace_append hprefix tailTrace_1071473
  have hstable : (prefixWord ++ tailWord_1071473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071473).length < 2 ^ (prefixWord ++ tailWord_1071473).sum := by decide
  have hdescent : baseEnd_1071473 < baseStart_1071473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071478 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1071478 : Nat := 118140960795 + 1071478 * 2 ^ 59
def prefixEnd_1071478 : Nat := 4983230072969 + 3 ^ 40 * 1071478 * 2
def baseEnd_1071478 : Nat := 550183224718264071097369

theorem tailTrace_1071478 : CollatzResearch.WordTrace tailWord_1071478 prefixEnd_1071478 550183224718264071097369 := by
  unfold tailWord_1071478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442500825764104669913943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26053342141483783145748725 2442500825764104669913943)
  ·
    refine ⟨3663751238646157004870915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2442500825764104669913943 3663751238646157004870915)
    ·
      refine ⟨5495626857969235507306373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663751238646157004870915 5495626857969235507306373)
      ·
        refine ⟨1030430035869231657619945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5495626857969235507306373 1030430035869231657619945)
        ·
          refine ⟨772822526901923743214959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030430035869231657619945 772822526901923743214959)
          ·
            refine ⟨1159233790352885614822439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772822526901923743214959 1159233790352885614822439)
            ·
              refine ⟨1738850685529328422233659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159233790352885614822439 1738850685529328422233659)
              ·
                refine ⟨2608276028293992633350489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738850685529328422233659 2608276028293992633350489)
                ·
                  refine ⟨1956207021220494475012867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2608276028293992633350489 1956207021220494475012867)
                  ·
                    refine ⟨2934310531830741712519301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1956207021220494475012867 2934310531830741712519301)
                    ·
                      refine ⟨550183224718264071097369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2934310531830741712519301 550183224718264071097369)
                      ·
                        rfl

theorem cell23_1071478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1071478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071478 prefixEnd_1071478 := by exact prefixLift 1071478
  have htrace : WordTrace (prefixWord ++ tailWord_1071478) baseStart_1071478 baseEnd_1071478 := by
    simpa [prefixWord, tailWord_1071478, baseEnd_1071478] using wordTrace_append hprefix tailTrace_1071478
  have hstable : (prefixWord ++ tailWord_1071478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071478).length < 2 ^ (prefixWord ++ tailWord_1071478).sum := by decide
  have hdescent : baseEnd_1071478 < baseStart_1071478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071497 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 1, 5]
def baseStart_1071497 : Nat := 118140960795 + 1071497 * 2 ^ 59
def prefixEnd_1071497 : Nat := 4983230072969 + 3 ^ 40 * 1071497 * 2
def baseEnd_1071497 : Nat := 183397660283566498919927

theorem tailTrace_1071497 : CollatzResearch.WordTrace tailWord_1071497 prefixEnd_1071497 183397660283566498919927 := by
  unfold tailWord_1071497
  simp only [CollatzResearch.WordTrace]
  refine ⟨39080706199156840963564745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26053804132771227309043163 39080706199156840963564745)
  ·
    refine ⟨29310529649367630722673559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39080706199156840963564745 29310529649367630722673559)
    ·
      refine ⟨43965794474051446084010339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29310529649367630722673559 43965794474051446084010339)
      ·
        refine ⟨65948691711077169126015509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43965794474051446084010339 65948691711077169126015509)
        ·
          refine ⟨3091344923956742302781977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65948691711077169126015509 3091344923956742302781977)
          ·
            refine ⟨2318508692967556727086483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3091344923956742302781977 2318508692967556727086483)
            ·
              refine ⟨3477763039451335090629725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318508692967556727086483 3477763039451335090629725)
              ·
                refine ⟨1304161139794250658986147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3477763039451335090629725 1304161139794250658986147)
                ·
                  refine ⟨1956241709691375988479221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304161139794250658986147 1956241709691375988479221)
                  ·
                    refine ⟨183397660283566498919927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1956241709691375988479221 183397660283566498919927)
                    ·
                      rfl

theorem cell23_1071497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_1071497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071497 prefixEnd_1071497 := by exact prefixLift 1071497
  have htrace : WordTrace (prefixWord ++ tailWord_1071497) baseStart_1071497 baseEnd_1071497 := by
    simpa [prefixWord, tailWord_1071497, baseEnd_1071497] using wordTrace_append hprefix tailTrace_1071497
  have hstable : (prefixWord ++ tailWord_1071497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071497).length < 2 ^ (prefixWord ++ tailWord_1071497).sum := by decide
  have hdescent : baseEnd_1071497 < baseStart_1071497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071520 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1071520 : Nat := 118140960795 + 1071520 * 2 ^ 59
def prefixEnd_1071520 : Nat := 4983230072969 + 3 ^ 40 * 1071520 * 2
def baseEnd_1071520 : Nat := 550204790905752906772175

theorem tailTrace_1071520 : CollatzResearch.WordTrace tailWord_1071520 prefixEnd_1071520 550204790905752906772175 := by
  unfold tailWord_1071520
  simp only [CollatzResearch.WordTrace]
  refine ⟨19540772539036757945826007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26054363385382343927768009 19540772539036757945826007)
  ·
    refine ⟨29311158808555136918739011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19540772539036757945826007 29311158808555136918739011)
    ·
      refine ⟨43966738212832705378108517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29311158808555136918739011 43966738212832705378108517)
      ·
        refine ⟨8243763414906132258395347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43966738212832705378108517 8243763414906132258395347)
        ·
          refine ⟨12365645122359198387593021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8243763414906132258395347 12365645122359198387593021)
          ·
            refine ⟨4637116920884699395347383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12365645122359198387593021 4637116920884699395347383)
            ·
              refine ⟨6955675381327049093021075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637116920884699395347383 6955675381327049093021075)
              ·
                refine ⟨10433513071990573639531613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6955675381327049093021075 10433513071990573639531613)
                ·
                  refine ⟨3912567401996465114824355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10433513071990573639531613 3912567401996465114824355)
                  ·
                    refine ⟨5868851102994697672236533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3912567401996465114824355 5868851102994697672236533)
                    ·
                      refine ⟨550204790905752906772175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5868851102994697672236533 550204790905752906772175)
                      ·
                        rfl

theorem cell23_1071520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1071520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071520 prefixEnd_1071520 := by exact prefixLift 1071520
  have htrace : WordTrace (prefixWord ++ tailWord_1071520) baseStart_1071520 baseEnd_1071520 := by
    simpa [prefixWord, tailWord_1071520, baseEnd_1071520] using wordTrace_append hprefix tailTrace_1071520
  have hstable : (prefixWord ++ tailWord_1071520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071520).length < 2 ^ (prefixWord ++ tailWord_1071520).sum := by decide
  have hdescent : baseEnd_1071520 < baseStart_1071520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071527 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1071527 : Nat := 118140960795 + 1071527 * 2 ^ 59
def prefixEnd_1071527 : Nat := 4983230072969 + 3 ^ 40 * 1071527 * 2
def baseEnd_1071527 : Nat := 183402795090111459794881

theorem tailTrace_1071527 : CollatzResearch.WordTrace tailWord_1071527 prefixEnd_1071527 183402795090111459794881 := by
  unfold tailWord_1071527
  simp only [CollatzResearch.WordTrace]
  refine ⟨39081800389048156087156835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26054533592698770724771223 39081800389048156087156835)
  ·
    refine ⟨58622700583572234130735253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39081800389048156087156835 58622700583572234130735253)
    ·
      refine ⟨2747939089854948474878215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58622700583572234130735253 2747939089854948474878215)
      ·
        refine ⟨4121908634782422712317323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747939089854948474878215 4121908634782422712317323)
        ·
          refine ⟨6182862952173634068475985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121908634782422712317323 6182862952173634068475985)
          ·
            refine ⟨4637147214130225551356989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6182862952173634068475985 4637147214130225551356989)
            ·
              refine ⟨1738930205298834581758871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4637147214130225551356989 1738930205298834581758871)
              ·
                refine ⟨2608395307948251872638307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738930205298834581758871 2608395307948251872638307)
                ·
                  refine ⟨3912592961922377808957461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2608395307948251872638307 3912592961922377808957461)
                  ·
                    refine ⟨183402795090111459794881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3912592961922377808957461 183402795090111459794881)
                    ·
                      rfl

theorem cell23_1071527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1071527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071527 prefixEnd_1071527 := by exact prefixLift 1071527
  have htrace : WordTrace (prefixWord ++ tailWord_1071527) baseStart_1071527 baseEnd_1071527 := by
    simpa [prefixWord, tailWord_1071527, baseEnd_1071527] using wordTrace_append hprefix tailTrace_1071527
  have hstable : (prefixWord ++ tailWord_1071527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071527).length < 2 ^ (prefixWord ++ tailWord_1071527).sum := by decide
  have hdescent : baseEnd_1071527 < baseStart_1071527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071584 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 2, 1, 3]
def baseStart_1071584 : Nat := 118140960795 + 1071584 * 2 ^ 59
def prefixEnd_1071584 : Nat := 4983230072969 + 3 ^ 40 * 1071584 * 2
def baseEnd_1071584 : Nat := 550237653667640656371881

theorem tailTrace_1071584 : CollatzResearch.WordTrace tailWord_1071584 prefixEnd_1071584 550237653667640656371881 := by
  unfold tailWord_1071584
  simp only [CollatzResearch.WordTrace]
  refine ⟨19541939674920827410990903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26055919566561103214654537 19541939674920827410990903)
  ·
    refine ⟨29312909512381241116486355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19541939674920827410990903 29312909512381241116486355)
    ·
      refine ⟨43969364268571861674729533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29312909512381241116486355 43969364268571861674729533)
      ·
        refine ⟨16488511600714448128023575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43969364268571861674729533 16488511600714448128023575)
        ·
          refine ⟨24732767401071672192035363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16488511600714448128023575 24732767401071672192035363)
          ·
            refine ⟨37099151101607508288053045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24732767401071672192035363 37099151101607508288053045)
            ·
              refine ⟨3478045415775703902004973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37099151101607508288053045 3478045415775703902004973)
              ·
                refine ⟨1304267030915888963251865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3478045415775703902004973 1304267030915888963251865)
                ·
                  refine ⟨978200273186916722438899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304267030915888963251865 978200273186916722438899)
                  ·
                    refine ⟨1467300409780375083658349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 978200273186916722438899 1467300409780375083658349)
                    ·
                      refine ⟨550237653667640656371881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1467300409780375083658349 550237653667640656371881)
                      ·
                        rfl

theorem cell23_1071584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_1071584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071584 prefixEnd_1071584 := by exact prefixLift 1071584
  have htrace : WordTrace (prefixWord ++ tailWord_1071584) baseStart_1071584 baseEnd_1071584 := by
    simpa [prefixWord, tailWord_1071584, baseEnd_1071584] using wordTrace_append hprefix tailTrace_1071584
  have hstable : (prefixWord ++ tailWord_1071584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071584).length < 2 ^ (prefixWord ++ tailWord_1071584).sum := by decide
  have hdescent : baseEnd_1071584 < baseStart_1071584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071610 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1071610 : Nat := 118140960795 + 1071610 * 2 ^ 59
def prefixEnd_1071610 : Nat := 4983230072969 + 3 ^ 40 * 1071610 * 2
def baseEnd_1071610 : Nat := 550251004164657554646761

theorem tailTrace_1071610 : CollatzResearch.WordTrace tailWord_1071610 prefixEnd_1071610 550251004164657554646761 := by
  unfold tailWord_1071610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9771206911936865315607071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26056551765164974174952189 9771206911936865315607071)
  ·
    refine ⟨14656810367905297973410607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9771206911936865315607071 14656810367905297973410607)
    ·
      refine ⟨21985215551857946960115911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14656810367905297973410607 21985215551857946960115911)
      ·
        refine ⟨32977823327786920440173867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21985215551857946960115911 32977823327786920440173867)
        ·
          refine ⟨49466734991680380660260801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32977823327786920440173867 49466734991680380660260801)
          ·
            refine ⟨37100051243760285495195601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49466734991680380660260801 37100051243760285495195601)
            ·
              refine ⟨27825038432820214121396701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37100051243760285495195601 27825038432820214121396701)
              ·
                refine ⟨10434389412307580295523763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27825038432820214121396701 10434389412307580295523763)
                ·
                  refine ⟨15651584118461370443285645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10434389412307580295523763 15651584118461370443285645)
                  ·
                    refine ⟨5869344044423013916232117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15651584118461370443285645 5869344044423013916232117)
                    ·
                      refine ⟨550251004164657554646761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5869344044423013916232117 550251004164657554646761)
                      ·
                        rfl

theorem cell23_1071610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1071610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071610 prefixEnd_1071610 := by exact prefixLift 1071610
  have htrace : WordTrace (prefixWord ++ tailWord_1071610) baseStart_1071610 baseEnd_1071610 := by
    simpa [prefixWord, tailWord_1071610, baseEnd_1071610] using wordTrace_append hprefix tailTrace_1071610
  have hstable : (prefixWord ++ tailWord_1071610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071610).length < 2 ^ (prefixWord ++ tailWord_1071610).sum := by decide
  have hdescent : baseEnd_1071610 < baseStart_1071610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071627 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 3]
def baseStart_1071627 : Nat := 118140960795 + 1071627 * 2 ^ 59
def prefixEnd_1071627 : Nat := 4983230072969 + 3 ^ 40 * 1071627 * 2
def baseEnd_1071627 : Nat := 550259733335783988134183

theorem tailTrace_1071627 : CollatzResearch.WordTrace tailWord_1071627 prefixEnd_1071627 550259733335783988134183 := by
  unfold tailWord_1071627
  simp only [CollatzResearch.WordTrace]
  refine ⟨39085447688685873165797135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26056965125790582110531423 39085447688685873165797135)
  ·
    refine ⟨58628171533028809748695703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39085447688685873165797135 58628171533028809748695703)
    ·
      refine ⟨87942257299543214623043555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58628171533028809748695703 87942257299543214623043555)
      ·
        refine ⟨131913385949314821934565333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87942257299543214623043555 131913385949314821934565333)
        ·
          refine ⟨3091719983187066139091375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 131913385949314821934565333 3091719983187066139091375)
          ·
            refine ⟨4637579974780599208637063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091719983187066139091375 4637579974780599208637063)
            ·
              refine ⟨6956369962170898812955595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637579974780599208637063 6956369962170898812955595)
              ·
                refine ⟨10434554943256348219433393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6956369962170898812955595 10434554943256348219433393)
                ·
                  refine ⟨7825916207442261164575045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10434554943256348219433393 7825916207442261164575045)
                  ·
                    refine ⟨1467359288895423968357821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7825916207442261164575045 1467359288895423968357821)
                    ·
                      refine ⟨550259733335783988134183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1467359288895423968357821 550259733335783988134183)
                      ·
                        rfl

theorem cell23_1071627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 3].length) (baseStart_1071627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071627 prefixEnd_1071627 := by exact prefixLift 1071627
  have htrace : WordTrace (prefixWord ++ tailWord_1071627) baseStart_1071627 baseEnd_1071627 := by
    simpa [prefixWord, tailWord_1071627, baseEnd_1071627] using wordTrace_append hprefix tailTrace_1071627
  have hstable : (prefixWord ++ tailWord_1071627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071627).length < 2 ^ (prefixWord ++ tailWord_1071627).sum := by decide
  have hdescent : baseEnd_1071627 < baseStart_1071627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071637 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1071637 : Nat := 118140960795 + 1071637 * 2 ^ 59
def prefixEnd_1071637 : Nat := 4983230072969 + 3 ^ 40 * 1071637 * 2
def baseEnd_1071637 : Nat := 550264868142328949009137

theorem tailTrace_1071637 : CollatzResearch.WordTrace tailWord_1071637 prefixEnd_1071637 550264868142328949009137 := by
  unfold tailWord_1071637
  simp only [CollatzResearch.WordTrace]
  refine ⟨39085812418649644873661165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26057208279099763249107443 39085812418649644873661165)
  ·
    refine ⟨14657179656993616827622937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39085812418649644873661165 14657179656993616827622937)
    ·
      refine ⟨10992884742745212620717203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14657179656993616827622937 10992884742745212620717203)
      ·
        refine ⟨16489327114117818931075805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10992884742745212620717203 16489327114117818931075805)
        ·
          refine ⟨6183497667794182099153427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16489327114117818931075805 6183497667794182099153427)
          ·
            refine ⟨9275246501691273148730141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183497667794182099153427 9275246501691273148730141)
            ·
              refine ⟨3478217438134227430773803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9275246501691273148730141 3478217438134227430773803)
              ·
                refine ⟨5217326157201341146160705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478217438134227430773803 5217326157201341146160705)
                ·
                  refine ⟨3912994617901005859620529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5217326157201341146160705 3912994617901005859620529)
                  ·
                    refine ⟨2934745963425754394715397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3912994617901005859620529 2934745963425754394715397)
                    ·
                      refine ⟨550264868142328949009137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2934745963425754394715397 550264868142328949009137)
                      ·
                        rfl

theorem cell23_1071637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1071637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071637 prefixEnd_1071637 := by exact prefixLift 1071637
  have htrace : WordTrace (prefixWord ++ tailWord_1071637) baseStart_1071637 baseEnd_1071637 := by
    simpa [prefixWord, tailWord_1071637, baseEnd_1071637] using wordTrace_append hprefix tailTrace_1071637
  have hstable : (prefixWord ++ tailWord_1071637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071637).length < 2 ^ (prefixWord ++ tailWord_1071637).sum := by decide
  have hdescent : baseEnd_1071637 < baseStart_1071637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071662 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1071662 : Nat := 118140960795 + 1071662 * 2 ^ 59
def prefixEnd_1071662 : Nat := 4983230072969 + 3 ^ 40 * 1071662 * 2
def baseEnd_1071662 : Nat := 550277705158691351196523

theorem tailTrace_1071662 : CollatzResearch.WordTrace tailWord_1071662 prefixEnd_1071662 550277705158691351196523 := by
  unfold tailWord_1071662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885840530444884267915155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26057816162372716095547493 4885840530444884267915155)
  ·
    refine ⟨7328760795667326401872733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4885840530444884267915155 7328760795667326401872733)
    ·
      refine ⟨2748285298375247400702275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7328760795667326401872733 2748285298375247400702275)
      ·
        refine ⟨4122427947562871101053413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2748285298375247400702275 4122427947562871101053413)
        ·
          refine ⟨772955240168038331447515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4122427947562871101053413 772955240168038331447515)
          ·
            refine ⟨1159432860252057497171273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772955240168038331447515 1159432860252057497171273)
            ·
              refine ⟨869574645189043122878455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159432860252057497171273 869574645189043122878455)
              ·
                refine ⟨1304361967783564684317683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869574645189043122878455 1304361967783564684317683)
                ·
                  refine ⟨1956542951675347026476525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304361967783564684317683 1956542951675347026476525)
                  ·
                    refine ⟨733703606878255134928697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956542951675347026476525 733703606878255134928697)
                    ·
                      refine ⟨550277705158691351196523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733703606878255134928697 550277705158691351196523)
                      ·
                        rfl

theorem cell23_1071662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1071662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071662 prefixEnd_1071662 := by exact prefixLift 1071662
  have htrace : WordTrace (prefixWord ++ tailWord_1071662) baseStart_1071662 baseEnd_1071662 := by
    simpa [prefixWord, tailWord_1071662, baseEnd_1071662] using wordTrace_append hprefix tailTrace_1071662
  have hstable : (prefixWord ++ tailWord_1071662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071662).length < 2 ^ (prefixWord ++ tailWord_1071662).sum := by decide
  have hdescent : baseEnd_1071662 < baseStart_1071662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071697 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_1071697 : Nat := 118140960795 + 1071697 * 2 ^ 59
def prefixEnd_1071697 : Nat := 4983230072969 + 3 ^ 40 * 1071697 * 2
def baseEnd_1071697 : Nat := 550295676981598714258861

theorem tailTrace_1071697 : CollatzResearch.WordTrace tailWord_1071697 prefixEnd_1071697 550295676981598714258861 := by
  unfold tailWord_1071697
  simp only [CollatzResearch.WordTrace]
  refine ⟨39088000798432275120845345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26058667198954850080563563 39088000798432275120845345)
  ·
    refine ⟨29316000598824206340634009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39088000798432275120845345 29316000598824206340634009)
    ·
      refine ⟨21987000449118154755475507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29316000598824206340634009 21987000449118154755475507)
      ·
        refine ⟨32980500673677232133213261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21987000449118154755475507 32980500673677232133213261)
        ·
          refine ⟨12367687752628962049954973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32980500673677232133213261 12367687752628962049954973)
          ·
            refine ⟨4637882907235860768733115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12367687752628962049954973 4637882907235860768733115)
            ·
              refine ⟨6956824360853791153099673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637882907235860768733115 6956824360853791153099673)
              ·
                refine ⟨5217618270640343364824755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6956824360853791153099673 5217618270640343364824755)
                ·
                  refine ⟨7826427405960515047237133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217618270640343364824755 7826427405960515047237133)
                  ·
                    refine ⟨2934910277235193142713925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7826427405960515047237133 2934910277235193142713925)
                    ·
                      refine ⟨550295676981598714258861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2934910277235193142713925 550295676981598714258861)
                      ·
                        rfl

theorem cell23_1071697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_1071697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071697 prefixEnd_1071697 := by exact prefixLift 1071697
  have htrace : WordTrace (prefixWord ++ tailWord_1071697) baseStart_1071697 baseEnd_1071697 := by
    simpa [prefixWord, tailWord_1071697, baseEnd_1071697] using wordTrace_append hprefix tailTrace_1071697
  have hstable : (prefixWord ++ tailWord_1071697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071697).length < 2 ^ (prefixWord ++ tailWord_1071697).sum := by decide
  have hdescent : baseEnd_1071697 < baseStart_1071697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071737 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 8]
def baseStart_1071737 : Nat := 118140960795 + 1071737 * 2 ^ 59
def prefixEnd_1071737 : Nat := 4983230072969 + 3 ^ 40 * 1071737 * 2
def baseEnd_1071737 : Nat := 61146246245308728639853

theorem tailTrace_1071737 : CollatzResearch.WordTrace tailWord_1071737 prefixEnd_1071737 61146246245308728639853 := by
  unfold tailWord_1071737
  simp only [CollatzResearch.WordTrace]
  refine ⟨39089459718287361952301465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26059639812191574634867643 39089459718287361952301465)
  ·
    refine ⟨29317094788715521464226099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39089459718287361952301465 29317094788715521464226099)
    ·
      refine ⟨43975642183073282196339149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29317094788715521464226099 43975642183073282196339149)
      ·
        refine ⟨16490865818652480823627181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43975642183073282196339149 16490865818652480823627181)
        ·
          refine ⟨6184074681994680308860193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16490865818652480823627181 6184074681994680308860193)
          ·
            refine ⟨4638056011496010231645145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6184074681994680308860193 4638056011496010231645145)
            ·
              refine ⟨3478542008622007673733859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638056011496010231645145 3478542008622007673733859)
              ·
                refine ⟨5217813012933011510600789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478542008622007673733859 5217813012933011510600789)
                ·
                  refine ⟨61146246245308728639853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5217813012933011510600789 61146246245308728639853)
                  ·
                    rfl

theorem cell23_1071737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_1071737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071737 prefixEnd_1071737 := by exact prefixLift 1071737
  have htrace : WordTrace (prefixWord ++ tailWord_1071737) baseStart_1071737 baseEnd_1071737 := by
    simpa [prefixWord, tailWord_1071737, baseEnd_1071737] using wordTrace_append hprefix tailTrace_1071737
  have hstable : (prefixWord ++ tailWord_1071737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071737).length < 2 ^ (prefixWord ++ tailWord_1071737).sum := by decide
  have hdescent : baseEnd_1071737 < baseStart_1071737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071791 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 2, 3, 2]
def baseStart_1071791 : Nat := 118140960795 + 1071791 * 2 ^ 59
def prefixEnd_1071791 : Nat := 4983230072969 + 3 ^ 40 * 1071791 * 2
def baseEnd_1071791 : Nat := 550343944163121346483429

theorem tailTrace_1071791 : CollatzResearch.WordTrace tailWord_1071791 prefixEnd_1071791 550343944163121346483429 := by
  unfold tailWord_1071791
  simp only [CollatzResearch.WordTrace]
  refine ⟨39091429260091729174767227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26060952840061152783178151 39091429260091729174767227)
  ·
    refine ⟨58637143890137593762150841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39091429260091729174767227 58637143890137593762150841)
    ·
      refine ⟨43977857917603195321613131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58637143890137593762150841 43977857917603195321613131)
      ·
        refine ⟨65966786876404792982419697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43977857917603195321613131 65966786876404792982419697)
        ·
          refine ⟨49475090157303594736814773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65966786876404792982419697 49475090157303594736814773)
          ·
            refine ⟨4638289702247212006576385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49475090157303594736814773 4638289702247212006576385)
            ·
              refine ⟨3478717276685409004932289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638289702247212006576385 3478717276685409004932289)
              ·
                refine ⟨2609037957514056753699217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478717276685409004932289 2609037957514056753699217)
                ·
                  refine ⟨1956778468135542565274413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609037957514056753699217 1956778468135542565274413)
                  ·
                    refine ⟨733791925550828461977905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956778468135542565274413 733791925550828461977905)
                    ·
                      refine ⟨550343944163121346483429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 733791925550828461977905 550343944163121346483429)
                      ·
                        rfl

theorem cell23_1071791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3, 2].length) (baseStart_1071791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071791 prefixEnd_1071791 := by exact prefixLift 1071791
  have htrace : WordTrace (prefixWord ++ tailWord_1071791) baseStart_1071791 baseEnd_1071791 := by
    simpa [prefixWord, tailWord_1071791, baseEnd_1071791] using wordTrace_append hprefix tailTrace_1071791
  have hstable : (prefixWord ++ tailWord_1071791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071791).length < 2 ^ (prefixWord ++ tailWord_1071791).sum := by decide
  have hdescent : baseEnd_1071791 < baseStart_1071791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071804 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1071804 : Nat := 118140960795 + 1071804 * 2 ^ 59
def prefixEnd_1071804 : Nat := 4983230072969 + 3 ^ 40 * 1071804 * 2
def baseEnd_1071804 : Nat := 550350619411629795620869

theorem tailTrace_1071804 : CollatzResearch.WordTrace tailWord_1071804 prefixEnd_1071804 550350619411629795620869 := by
  unfold tailWord_1071804
  simp only [CollatzResearch.WordTrace]
  refine ⟨19545951704522316197495233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26061268939363088263326977 19545951704522316197495233)
  ·
    refine ⟨14659463778391737148121425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19545951704522316197495233 14659463778391737148121425)
    ·
      refine ⟨10994597833793802861091069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14659463778391737148121425 10994597833793802861091069)
      ·
        refine ⟨4122974187672676072909151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10994597833793802861091069 4122974187672676072909151)
        ·
          refine ⟨6184461281509014109363727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122974187672676072909151 6184461281509014109363727)
          ·
            refine ⟨9276691922263521164045591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6184461281509014109363727 9276691922263521164045591)
            ·
              refine ⟨13915037883395281746068387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9276691922263521164045591 13915037883395281746068387)
              ·
                refine ⟨20872556825092922619102581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13915037883395281746068387 20872556825092922619102581)
                ·
                  refine ⟨1956802202352461495540867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20872556825092922619102581 1956802202352461495540867)
                  ·
                    refine ⟨2935203303528692243311301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1956802202352461495540867 2935203303528692243311301)
                    ·
                      refine ⟨550350619411629795620869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2935203303528692243311301 550350619411629795620869)
                      ·
                        rfl

theorem cell23_1071804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1071804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1071804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1071804 prefixEnd_1071804 := by exact prefixLift 1071804
  have htrace : WordTrace (prefixWord ++ tailWord_1071804) baseStart_1071804 baseEnd_1071804 := by
    simpa [prefixWord, tailWord_1071804, baseEnd_1071804] using wordTrace_append hprefix tailTrace_1071804
  have hstable : (prefixWord ++ tailWord_1071804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071804).length < 2 ^ (prefixWord ++ tailWord_1071804).sum := by decide
  have hdescent : baseEnd_1071804 < baseStart_1071804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
