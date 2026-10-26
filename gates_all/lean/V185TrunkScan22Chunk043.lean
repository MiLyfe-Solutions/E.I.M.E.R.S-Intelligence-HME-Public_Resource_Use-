import V185TrunkScan22Chunk042

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_385580 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_385580 : Nat := 118140960795 + 385580 * 2 ^ 59
def prefixEnd_385580 : Nat := 4983230072969 + 3 ^ 40 * 385580 * 2
def baseEnd_385580 : Nat := 131991913840471100117837

theorem tailTrace_385580 : CollatzResearch.WordTrace tailWord_385580 prefixEnd_385580 131991913840471100117837 := by
  unfold tailWord_385580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031628971558493333189097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9375505295411324444252129 7031628971558493333189097)
  ·
    refine ⟨5273721728668869999891823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7031628971558493333189097 5273721728668869999891823)
    ·
      refine ⟨7910582593003304999837735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5273721728668869999891823 7910582593003304999837735)
      ·
        refine ⟨11865873889504957499756603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910582593003304999837735 11865873889504957499756603)
        ·
          refine ⟨17798810834257436249634905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11865873889504957499756603 17798810834257436249634905)
          ·
            refine ⟨13349108125693077187226179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17798810834257436249634905 13349108125693077187226179)
            ·
              refine ⟨20023662188539615780839269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13349108125693077187226179 20023662188539615780839269)
              ·
                refine ⟨3754436660351177958907363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20023662188539615780839269 3754436660351177958907363)
                ·
                  refine ⟨5631654990526766938361045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754436660351177958907363 5631654990526766938361045)
                  ·
                    refine ⟨131991913840471100117837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5631654990526766938361045 131991913840471100117837)
                    ·
                      rfl

theorem cell22_385580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_385580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385580 prefixEnd_385580 := by exact prefixLift 385580
  have htrace : WordTrace (prefixWord ++ tailWord_385580) baseStart_385580 baseEnd_385580 := by
    simpa [prefixWord, tailWord_385580, baseEnd_385580] using wordTrace_append hprefix tailTrace_385580
  have hstable : (prefixWord ++ tailWord_385580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385580).length < 2 ^ (prefixWord ++ tailWord_385580).sum := by decide
  have hdescent : baseEnd_385580 < baseStart_385580 := by decide
  rcases family_descends (prefixWord ++ tailWord_385580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385586 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_385586 : Nat := 118140960795 + 385586 * 2 ^ 59
def prefixEnd_385586 : Nat := 4983230072969 + 3 ^ 40 * 385586 * 2
def baseEnd_385586 : Nat := 131993967763089084467819

theorem tailTrace_385586 : CollatzResearch.WordTrace tailWord_385586 prefixEnd_385586 131993967763089084467819 := by
  unfold tailWord_385586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515869195273812422774153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9375651187396833127397741 3515869195273812422774153)
  ·
    refine ⟨2636901896455359317080615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3515869195273812422774153 2636901896455359317080615)
    ·
      refine ⟨3955352844683038975620923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636901896455359317080615 3955352844683038975620923)
      ·
        refine ⟨5933029267024558463431385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955352844683038975620923 5933029267024558463431385)
        ·
          refine ⟨4449771950268418847573539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5933029267024558463431385 4449771950268418847573539)
          ·
            refine ⟨6674657925402628271360309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449771950268418847573539 6674657925402628271360309)
            ·
              refine ⟨625749180506496400440029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6674657925402628271360309 625749180506496400440029)
              ·
                refine ⟨234655942689936150165011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 625749180506496400440029 234655942689936150165011)
                ·
                  refine ⟨351983914034904225247517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234655942689936150165011 351983914034904225247517)
                  ·
                    refine ⟨131993967763089084467819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351983914034904225247517 131993967763089084467819)
                    ·
                      rfl

theorem cell22_385586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_385586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385586 prefixEnd_385586 := by exact prefixLift 385586
  have htrace : WordTrace (prefixWord ++ tailWord_385586) baseStart_385586 baseEnd_385586 := by
    simpa [prefixWord, tailWord_385586, baseEnd_385586] using wordTrace_append hprefix tailTrace_385586
  have hstable : (prefixWord ++ tailWord_385586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385586).length < 2 ^ (prefixWord ++ tailWord_385586).sum := by decide
  have hdescent : baseEnd_385586 < baseStart_385586 := by decide
  rcases family_descends (prefixWord ++ tailWord_385586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385612 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_385612 : Nat := 118140960795 + 385612 * 2 ^ 59
def prefixEnd_385612 : Nat := 4983230072969 + 3 ^ 40 * 385612 * 2
def baseEnd_385612 : Nat := 132002868094433683317739

theorem tailTrace_385612 : CollatzResearch.WordTrace tailWord_385612 prefixEnd_385612 132002868094433683317739 := by
  unfold tailWord_385612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7032212539500528065771545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9376283386000704087695393 7032212539500528065771545)
  ·
    refine ⟨5274159404625396049328659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7032212539500528065771545 5274159404625396049328659)
    ·
      refine ⟨7911239106938094073992989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5274159404625396049328659 7911239106938094073992989)
      ·
        refine ⟨2966714665101785277747371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7911239106938094073992989 2966714665101785277747371)
        ·
          refine ⟨4450071997652677916621057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966714665101785277747371 4450071997652677916621057)
          ·
            refine ⟨3337553998239508437465793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450071997652677916621057 3337553998239508437465793)
            ·
              refine ⟨2503165498679631328099345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337553998239508437465793 2503165498679631328099345)
              ·
                refine ⟨1877374124009723496074509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503165498679631328099345 1877374124009723496074509)
                ·
                  refine ⟨704015296503646311027941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1877374124009723496074509 704015296503646311027941)
                  ·
                    refine ⟨132002868094433683317739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704015296503646311027941 132002868094433683317739)
                    ·
                      rfl

theorem cell22_385612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_385612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385612 prefixEnd_385612 := by exact prefixLift 385612
  have htrace : WordTrace (prefixWord ++ tailWord_385612) baseStart_385612 baseEnd_385612 := by
    simpa [prefixWord, tailWord_385612, baseEnd_385612] using wordTrace_append hprefix tailTrace_385612
  have hstable : (prefixWord ++ tailWord_385612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385612).length < 2 ^ (prefixWord ++ tailWord_385612).sum := by decide
  have hdescent : baseEnd_385612 < baseStart_385612 := by decide
  rcases family_descends (prefixWord ++ tailWord_385612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385661 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 4]
def baseStart_385661 : Nat := 118140960795 + 385661 * 2 ^ 59
def prefixEnd_385661 : Nat := 4983230072969 + 3 ^ 40 * 385661 * 2
def baseEnd_385661 : Nat := 44006547265271296280863

theorem tailTrace_385661 : CollatzResearch.WordTrace tailWord_385661 prefixEnd_385661 44006547265271296280863 := by
  unfold tailWord_385661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14066212255823537500076837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9377474837215691666717891 14066212255823537500076837)
  ·
    refine ⟨2637414797966913281264407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14066212255823537500076837 2637414797966913281264407)
    ·
      refine ⟨3956122196950369921896611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637414797966913281264407 3956122196950369921896611)
      ·
        refine ⟨5934183295425554882844917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956122196950369921896611 5934183295425554882844917)
        ·
          refine ⟨556329683946145770266711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5934183295425554882844917 556329683946145770266711)
          ·
            refine ⟨834494525919218655400067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556329683946145770266711 834494525919218655400067)
            ·
              refine ⟨1251741788878827983100101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834494525919218655400067 1251741788878827983100101)
              ·
                refine ⟨234701585414780246831269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1251741788878827983100101 234701585414780246831269)
                ·
                  refine ⟨44006547265271296280863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234701585414780246831269 44006547265271296280863)
                  ·
                    rfl

theorem cell22_385661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_385661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385661 prefixEnd_385661 := by exact prefixLift 385661
  have htrace : WordTrace (prefixWord ++ tailWord_385661) baseStart_385661 baseEnd_385661 := by
    simpa [prefixWord, tailWord_385661, baseEnd_385661] using wordTrace_append hprefix tailTrace_385661
  have hstable : (prefixWord ++ tailWord_385661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385661).length < 2 ^ (prefixWord ++ tailWord_385661).sum := by decide
  have hdescent : baseEnd_385661 < baseStart_385661 := by decide
  rcases family_descends (prefixWord ++ tailWord_385661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385706 : List Nat := [3, 1, 5, 2, 1, 1, 9]
def baseStart_385706 : Nat := 118140960795 + 385706 * 2 ^ 59
def prefixEnd_385706 : Nat := 4983230072969 + 3 ^ 40 * 385706 * 2
def baseEnd_385706 : Nat := 4890186896868473017313

theorem tailTrace_385706 : CollatzResearch.WordTrace tailWord_385706 prefixEnd_385706 4890186896868473017313 := by
  unfold tailWord_385706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516963385165127546366243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9378569027107006790309981 3516963385165127546366243)
  ·
    refine ⟨5275445077747691319549365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3516963385165127546366243 5275445077747691319549365)
    ·
      refine ⟨494572976038846061207753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5275445077747691319549365 494572976038846061207753)
      ·
        refine ⟨370929732029134545905815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494572976038846061207753 370929732029134545905815)
        ·
          refine ⟨556394598043701818858723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370929732029134545905815 556394598043701818858723)
          ·
            refine ⟨834591897065552728288085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556394598043701818858723 834591897065552728288085)
            ·
              refine ⟨4890186896868473017313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 834591897065552728288085 4890186896868473017313)
              ·
                rfl

theorem cell22_385706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 9].length) (baseStart_385706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385706 prefixEnd_385706 := by exact prefixLift 385706
  have htrace : WordTrace (prefixWord ++ tailWord_385706) baseStart_385706 baseEnd_385706 := by
    simpa [prefixWord, tailWord_385706, baseEnd_385706] using wordTrace_append hprefix tailTrace_385706
  have hstable : (prefixWord ++ tailWord_385706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385706).length < 2 ^ (prefixWord ++ tailWord_385706).sum := by decide
  have hdescent : baseEnd_385706 < baseStart_385706 := by decide
  rcases family_descends (prefixWord ++ tailWord_385706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385710 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_385710 : Nat := 118140960795 + 385710 * 2 ^ 59
def prefixEnd_385710 : Nat := 4983230072969 + 3 ^ 40 * 385710 * 2
def baseEnd_385710 : Nat := 132036415497194094367439

theorem tailTrace_385710 : CollatzResearch.WordTrace tailWord_385710 prefixEnd_385710 132036415497194094367439 := by
  unfold tailWord_385710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758499929080752358576323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9378666288430679245740389 1758499929080752358576323)
  ·
    refine ⟨2637749893621128537864485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1758499929080752358576323 2637749893621128537864485)
    ·
      refine ⟨494578105053961600849591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2637749893621128537864485 494578105053961600849591)
      ·
        refine ⟨741867157580942401274387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494578105053961600849591 741867157580942401274387)
        ·
          refine ⟨1112800736371413601911581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741867157580942401274387 1112800736371413601911581)
          ·
            refine ⟨417300276139280100716843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1112800736371413601911581 417300276139280100716843)
            ·
              refine ⟨625950414208920151075265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417300276139280100716843 625950414208920151075265)
              ·
                refine ⟨469462810656690113306449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625950414208920151075265 469462810656690113306449)
                ·
                  refine ⟨352097107992517584979837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469462810656690113306449 352097107992517584979837)
                  ·
                    refine ⟨132036415497194094367439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352097107992517584979837 132036415497194094367439)
                    ·
                      rfl

theorem cell22_385710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_385710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385710 prefixEnd_385710 := by exact prefixLift 385710
  have htrace : WordTrace (prefixWord ++ tailWord_385710) baseStart_385710 baseEnd_385710 := by
    simpa [prefixWord, tailWord_385710, baseEnd_385710] using wordTrace_append hprefix tailTrace_385710
  have hstable : (prefixWord ++ tailWord_385710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385710).length < 2 ^ (prefixWord ++ tailWord_385710).sum := by decide
  have hdescent : baseEnd_385710 < baseStart_385710 := by decide
  rcases family_descends (prefixWord ++ tailWord_385710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385807 : List Nat := [1, 1, 2, 1, 1, 1, 5, 10]
def baseStart_385807 : Nat := 118140960795 + 385807 * 2 ^ 59
def prefixEnd_385807 : Nat := 4983230072969 + 3 ^ 40 * 385807 * 2
def baseEnd_385807 : Nat := 14674402286613130521349

theorem tailTrace_385807 : CollatzResearch.WordTrace tailWord_385807 prefixEnd_385807 14674402286613130521349 := by
  unfold tailWord_385807
  simp only [CollatzResearch.WordTrace]
  refine ⟨14071537313294604434891675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9381024875529736289927783 14071537313294604434891675)
  ·
    refine ⟨21107305969941906652337513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14071537313294604434891675 21107305969941906652337513)
    ·
      refine ⟨15830479477456429989253135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21107305969941906652337513 15830479477456429989253135)
      ·
        refine ⟨23745719216184644983879703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15830479477456429989253135 23745719216184644983879703)
        ·
          refine ⟨35618578824276967475819555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23745719216184644983879703 35618578824276967475819555)
          ·
            refine ⟨53427868236415451213729333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35618578824276967475819555 53427868236415451213729333)
            ·
              refine ⟨5008862647163948551287125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53427868236415451213729333 5008862647163948551287125)
              ·
                refine ⟨14674402286613130521349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5008862647163948551287125 14674402286613130521349)
                ·
                  rfl

theorem cell22_385807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 10].length) (baseStart_385807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385807 prefixEnd_385807 := by exact prefixLift 385807
  have htrace : WordTrace (prefixWord ++ tailWord_385807) baseStart_385807 baseEnd_385807 := by
    simpa [prefixWord, tailWord_385807, baseEnd_385807] using wordTrace_append hprefix tailTrace_385807
  have hstable : (prefixWord ++ tailWord_385807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385807).length < 2 ^ (prefixWord ++ tailWord_385807).sum := by decide
  have hdescent : baseEnd_385807 < baseStart_385807 := by decide
  rcases family_descends (prefixWord ++ tailWord_385807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385809 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_385809 : Nat := 118140960795 + 385809 * 2 ^ 59
def prefixEnd_385809 : Nat := 4983230072969 + 3 ^ 40 * 385809 * 2
def baseEnd_385809 : Nat := 132070305220390836142135

theorem tailTrace_385809 : CollatzResearch.WordTrace tailWord_385809 prefixEnd_385809 132070305220390836142135 := by
  unfold tailWord_385809
  simp only [CollatzResearch.WordTrace]
  refine ⟨14071610259287358776464481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9381073506191572517642987 14071610259287358776464481)
  ·
    refine ⟨10553707694465519082348361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14071610259287358776464481 10553707694465519082348361)
    ·
      refine ⟨7915280770849139311761271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10553707694465519082348361 7915280770849139311761271)
      ·
        refine ⟨11872921156273708967641907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915280770849139311761271 11872921156273708967641907)
        ·
          refine ⟨17809381734410563451462861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11872921156273708967641907 17809381734410563451462861)
          ·
            refine ⟨6678518150403961294298573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17809381734410563451462861 6678518150403961294298573)
            ·
              refine ⟨2504444306401485485361965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6678518150403961294298573 2504444306401485485361965)
              ·
                refine ⟨939166614900557057010737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2504444306401485485361965 939166614900557057010737)
                ·
                  refine ⟨704374961175417792758053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939166614900557057010737 704374961175417792758053)
                  ·
                    refine ⟨132070305220390836142135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704374961175417792758053 132070305220390836142135)
                    ·
                      rfl

theorem cell22_385809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_385809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385809 prefixEnd_385809 := by exact prefixLift 385809
  have htrace : WordTrace (prefixWord ++ tailWord_385809) baseStart_385809 baseEnd_385809 := by
    simpa [prefixWord, tailWord_385809, baseEnd_385809] using wordTrace_append hprefix tailTrace_385809
  have hstable : (prefixWord ++ tailWord_385809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385809).length < 2 ^ (prefixWord ++ tailWord_385809).sum := by decide
  have hdescent : baseEnd_385809 < baseStart_385809 := by decide
  rcases family_descends (prefixWord ++ tailWord_385809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385826 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_385826 : Nat := 118140960795 + 385826 * 2 ^ 59
def prefixEnd_385826 : Nat := 4983230072969 + 3 ^ 40 * 385826 * 2
def baseEnd_385826 : Nat := 132076124667808458467083

theorem tailTrace_385826 : CollatzResearch.WordTrace tailWord_385826 prefixEnd_385826 132076124667808458467083 := by
  unfold tailWord_385826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3518057575056442669958333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9381486866817180453222221 3518057575056442669958333)
  ·
    refine ⟨1319271590646166001234375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3518057575056442669958333 1319271590646166001234375)
    ·
      refine ⟨1978907385969249001851563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319271590646166001234375 1978907385969249001851563)
      ·
        refine ⟨2968361078953873502777345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978907385969249001851563 2968361078953873502777345)
        ·
          refine ⟨2226270809215405127083009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2968361078953873502777345 2226270809215405127083009)
          ·
            refine ⟨1669703106911553845312257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226270809215405127083009 1669703106911553845312257)
            ·
              refine ⟨1252277330183665383984193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669703106911553845312257 1252277330183665383984193)
              ·
                refine ⟨939207997637749037988145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252277330183665383984193 939207997637749037988145)
                ·
                  refine ⟨704405998228311778491109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939207997637749037988145 704405998228311778491109)
                  ·
                    refine ⟨132076124667808458467083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704405998228311778491109 132076124667808458467083)
                    ·
                      rfl

theorem cell22_385826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_385826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385826 prefixEnd_385826 := by exact prefixLift 385826
  have htrace : WordTrace (prefixWord ++ tailWord_385826) baseStart_385826 baseEnd_385826 := by
    simpa [prefixWord, tailWord_385826, baseEnd_385826] using wordTrace_append hprefix tailTrace_385826
  have hstable : (prefixWord ++ tailWord_385826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385826).length < 2 ^ (prefixWord ++ tailWord_385826).sum := by decide
  have hdescent : baseEnd_385826 < baseStart_385826 := by decide
  rcases family_descends (prefixWord ++ tailWord_385826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385890 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_385890 : Nat := 118140960795 + 385890 * 2 ^ 59
def prefixEnd_385890 : Nat := 4983230072969 + 3 ^ 40 * 385890 * 2
def baseEnd_385890 : Nat := 132098033175733624866887

theorem tailTrace_385890 : CollatzResearch.WordTrace tailWord_385890 prefixEnd_385890 132098033175733624866887 := by
  unfold tailWord_385890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3518641142998477402540781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9383043047995939740108749 3518641142998477402540781)
  ·
    refine ⟨1319490428624429025952793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3518641142998477402540781 1319490428624429025952793)
    ·
      refine ⟨989617821468321769464595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1319490428624429025952793 989617821468321769464595)
      ·
        refine ⟨1484426732202482654196893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989617821468321769464595 1484426732202482654196893)
        ·
          refine ⟨556660024575930995323835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1484426732202482654196893 556660024575930995323835)
          ·
            refine ⟨834990036863896492985753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556660024575930995323835 834990036863896492985753)
            ·
              refine ⟨626242527647922369739315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834990036863896492985753 626242527647922369739315)
              ·
                refine ⟨939363791471883554608973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626242527647922369739315 939363791471883554608973)
                ·
                  refine ⟨352261421801956332978365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939363791471883554608973 352261421801956332978365)
                  ·
                    refine ⟨132098033175733624866887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352261421801956332978365 132098033175733624866887)
                    ·
                      rfl

theorem cell22_385890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_385890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385890 prefixEnd_385890 := by exact prefixLift 385890
  have htrace : WordTrace (prefixWord ++ tailWord_385890) baseStart_385890 baseEnd_385890 := by
    simpa [prefixWord, tailWord_385890, baseEnd_385890] using wordTrace_append hprefix tailTrace_385890
  have hstable : (prefixWord ++ tailWord_385890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385890).length < 2 ^ (prefixWord ++ tailWord_385890).sum := by decide
  have hdescent : baseEnd_385890 < baseStart_385890 := by decide
  rcases family_descends (prefixWord ++ tailWord_385890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385899 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 5, 4]
def baseStart_385899 : Nat := 118140960795 + 385899 * 2 ^ 59
def prefixEnd_385899 : Nat := 4983230072969 + 3 ^ 40 * 385899 * 2
def baseEnd_385899 : Nat := 132101114059660601391859

theorem tailTrace_385899 : CollatzResearch.WordTrace tailWord_385899 prefixEnd_385899 132101114059660601391859 := by
  unfold tailWord_385899
  simp only [CollatzResearch.WordTrace]
  refine ⟨14074892828961304147240751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383261885974202764827167 14074892828961304147240751)
  ·
    refine ⟨21112339243441956220861127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14074892828961304147240751 21112339243441956220861127)
    ·
      refine ⟨31668508865162934331291691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21112339243441956220861127 31668508865162934331291691)
      ·
        refine ⟨47502763297744401496937537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31668508865162934331291691 47502763297744401496937537)
        ·
          refine ⟨35627072473308301122703153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47502763297744401496937537 35627072473308301122703153)
          ·
            refine ⟨26720304354981225842027365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35627072473308301122703153 26720304354981225842027365)
            ·
              refine ⟨5010057066558979845380131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26720304354981225842027365 5010057066558979845380131)
              ·
                refine ⟨7515085599838469768070197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010057066558979845380131 7515085599838469768070197)
                ·
                  refine ⟨704539274984856540756581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7515085599838469768070197 704539274984856540756581)
                  ·
                    refine ⟨132101114059660601391859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704539274984856540756581 132101114059660601391859)
                    ·
                      rfl

theorem cell22_385899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_385899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385899 prefixEnd_385899 := by exact prefixLift 385899
  have htrace : WordTrace (prefixWord ++ tailWord_385899) baseStart_385899 baseEnd_385899 := by
    simpa [prefixWord, tailWord_385899, baseEnd_385899] using wordTrace_append hprefix tailTrace_385899
  have hstable : (prefixWord ++ tailWord_385899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385899).length < 2 ^ (prefixWord ++ tailWord_385899).sum := by decide
  have hdescent : baseEnd_385899 < baseStart_385899 := by decide
  rcases family_descends (prefixWord ++ tailWord_385899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386096 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_386096 : Nat := 118140960795 + 386096 * 2 ^ 59
def prefixEnd_386096 : Nat := 4983230072969 + 3 ^ 40 * 386096 * 2
def baseEnd_386096 : Nat := 132168551185617754216255

theorem tailTrace_386096 : CollatzResearch.WordTrace tailWord_386096 prefixEnd_386096 132168551185617754216255 := by
  unfold tailWord_386096
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041039004623803396081071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9388052006165071194774761 7041039004623803396081071)
  ·
    refine ⟨10561558506935705094121607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7041039004623803396081071 10561558506935705094121607)
    ·
      refine ⟨15842337760403557641182411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10561558506935705094121607 15842337760403557641182411)
      ·
        refine ⟨23763506640605336461773617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15842337760403557641182411 23763506640605336461773617)
        ·
          refine ⟨17822629980454002346330213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23763506640605336461773617 17822629980454002346330213)
          ·
            refine ⟨3341743121335125439936915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17822629980454002346330213 3341743121335125439936915)
            ·
              refine ⟨5012614682002688159905373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341743121335125439936915 5012614682002688159905373)
              ·
                refine ⟨1879730505751008059964515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5012614682002688159905373 1879730505751008059964515)
                ·
                  refine ⟨2819595758626512089946773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879730505751008059964515 2819595758626512089946773)
                  ·
                    refine ⟨132168551185617754216255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2819595758626512089946773 132168551185617754216255)
                    ·
                      rfl

theorem cell22_386096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_386096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386096 prefixEnd_386096 := by exact prefixLift 386096
  have htrace : WordTrace (prefixWord ++ tailWord_386096) baseStart_386096 baseEnd_386096 := by
    simpa [prefixWord, tailWord_386096, baseEnd_386096] using wordTrace_append hprefix tailTrace_386096
  have hstable : (prefixWord ++ tailWord_386096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386096).length < 2 ^ (prefixWord ++ tailWord_386096).sum := by decide
  have hdescent : baseEnd_386096 < baseStart_386096 := by decide
  rcases family_descends (prefixWord ++ tailWord_386096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386098 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_386098 : Nat := 118140960795 + 386098 * 2 ^ 59
def prefixEnd_386098 : Nat := 4983230072969 + 3 ^ 40 * 386098 * 2
def baseEnd_386098 : Nat := 132169235826490415666249

theorem tailTrace_386098 : CollatzResearch.WordTrace tailWord_386098 prefixEnd_386098 132169235826490415666249 := by
  unfold tailWord_386098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520537738810090283433737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9388100636826907422489965 3520537738810090283433737)
  ·
    refine ⟨2640403304107567712575303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3520537738810090283433737 2640403304107567712575303)
    ·
      refine ⟨3960604956161351568862955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640403304107567712575303 3960604956161351568862955)
      ·
        refine ⟨5940907434242027353294433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960604956161351568862955 5940907434242027353294433)
        ·
          refine ⟨4455680575681520514970825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940907434242027353294433 4455680575681520514970825)
          ·
            refine ⟨3341760431761140386228119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4455680575681520514970825 3341760431761140386228119)
            ·
              refine ⟨5012640647641710579342179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341760431761140386228119 5012640647641710579342179)
              ·
                refine ⟨7518960971462565869013269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012640647641710579342179 7518960971462565869013269)
                ·
                  refine ⟨352451295537307775109997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7518960971462565869013269 352451295537307775109997)
                  ·
                    refine ⟨132169235826490415666249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352451295537307775109997 132169235826490415666249)
                    ·
                      rfl

theorem cell22_386098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_386098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386098 prefixEnd_386098 := by exact prefixLift 386098
  have htrace : WordTrace (prefixWord ++ tailWord_386098) baseStart_386098 baseEnd_386098 := by
    simpa [prefixWord, tailWord_386098, baseEnd_386098] using wordTrace_append hprefix tailTrace_386098
  have hstable : (prefixWord ++ tailWord_386098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386098).length < 2 ^ (prefixWord ++ tailWord_386098).sum := by decide
  have hdescent : baseEnd_386098 < baseStart_386098 := by decide
  rcases family_descends (prefixWord ++ tailWord_386098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386132 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_386132 : Nat := 118140960795 + 386132 * 2 ^ 59
def prefixEnd_386132 : Nat := 4983230072969 + 3 ^ 40 * 386132 * 2
def baseEnd_386132 : Nat := 132180874721325660316145

theorem tailTrace_386132 : CollatzResearch.WordTrace tailWord_386132 prefixEnd_386132 132180874721325660316145 := by
  unfold tailWord_386132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041695518558592470236325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9388927358078123293648433 7041695518558592470236325)
  ·
    refine ⟨1320317909729736088169311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7041695518558592470236325 1320317909729736088169311)
    ·
      refine ⟨1980476864594604132253967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320317909729736088169311 1980476864594604132253967)
      ·
        refine ⟨2970715296891906198380951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980476864594604132253967 2970715296891906198380951)
        ·
          refine ⟨4456072945337859297571427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970715296891906198380951 4456072945337859297571427)
          ·
            refine ⟨6684109418006788946357141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456072945337859297571427 6684109418006788946357141)
            ·
              refine ⟨313317628969068231860491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6684109418006788946357141 313317628969068231860491)
              ·
                refine ⟨469976443453602347790737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313317628969068231860491 469976443453602347790737)
                ·
                  refine ⟨352482332590201760843053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469976443453602347790737 352482332590201760843053)
                  ·
                    refine ⟨132180874721325660316145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352482332590201760843053 132180874721325660316145)
                    ·
                      rfl

theorem cell22_386132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_386132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386132 prefixEnd_386132 := by exact prefixLift 386132
  have htrace : WordTrace (prefixWord ++ tailWord_386132) baseStart_386132 baseEnd_386132 := by
    simpa [prefixWord, tailWord_386132, baseEnd_386132] using wordTrace_append hprefix tailTrace_386132
  have hstable : (prefixWord ++ tailWord_386132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386132).length < 2 ^ (prefixWord ++ tailWord_386132).sum := by decide
  have hdescent : baseEnd_386132 < baseStart_386132 := by decide
  rcases family_descends (prefixWord ++ tailWord_386132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386143 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 5, 3]
def baseStart_386143 : Nat := 118140960795 + 386143 * 2 ^ 59
def prefixEnd_386143 : Nat := 4983230072969 + 3 ^ 40 * 386143 * 2
def baseEnd_386143 : Nat := 132184640246125298291111

theorem tailTrace_386143 : CollatzResearch.WordTrace tailWord_386143 prefixEnd_386143 132184640246125298291111 := by
  unfold tailWord_386143
  simp only [CollatzResearch.WordTrace]
  refine ⟨14083792240077333819123083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9389194826718222546082055 14083792240077333819123083)
  ·
    refine ⟨21125688360116000728684625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14083792240077333819123083 21125688360116000728684625)
    ·
      refine ⟨15844266270087000546513469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21125688360116000728684625 15844266270087000546513469)
      ·
        refine ⟨5941599851282625204942551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15844266270087000546513469 5941599851282625204942551)
        ·
          refine ⟨8912399776923937807413827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5941599851282625204942551 8912399776923937807413827)
          ·
            refine ⟨13368599665385906711120741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912399776923937807413827 13368599665385906711120741)
            ·
              refine ⟨2506612437259857508335139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13368599665385906711120741 2506612437259857508335139)
              ·
                refine ⟨3759918655889786262502709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506612437259857508335139 3759918655889786262502709)
                ·
                  refine ⟨352492373989667462109629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3759918655889786262502709 352492373989667462109629)
                  ·
                    refine ⟨132184640246125298291111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352492373989667462109629 132184640246125298291111)
                    ·
                      rfl

theorem cell22_386143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_386143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386143 prefixEnd_386143 := by exact prefixLift 386143
  have htrace : WordTrace (prefixWord ++ tailWord_386143) baseStart_386143 baseEnd_386143 := by
    simpa [prefixWord, tailWord_386143, baseEnd_386143] using wordTrace_append hprefix tailTrace_386143
  have hstable : (prefixWord ++ tailWord_386143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386143).length < 2 ^ (prefixWord ++ tailWord_386143).sum := by decide
  have hdescent : baseEnd_386143 < baseStart_386143 := by decide
  rcases family_descends (prefixWord ++ tailWord_386143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386171 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_386171 : Nat := 118140960795 + 386171 * 2 ^ 59
def prefixEnd_386171 : Nat := 4983230072969 + 3 ^ 40 * 386171 * 2
def baseEnd_386171 : Nat := 132194225218342558591025

theorem tailTrace_386171 : CollatzResearch.WordTrace tailWord_386171 prefixEnd_386171 132194225218342558591025 := by
  unfold tailWord_386171
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084813483975894601142367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9389875655983929734094911 14084813483975894601142367)
  ·
    refine ⟨21127220225963841901713551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14084813483975894601142367 21127220225963841901713551)
    ·
      refine ⟨31690830338945762852570327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127220225963841901713551 31690830338945762852570327)
      ·
        refine ⟨47536245508418644278855491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31690830338945762852570327 47536245508418644278855491)
        ·
          refine ⟨71304368262627966418283237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47536245508418644278855491 71304368262627966418283237)
          ·
            refine ⟨13369569049242743703428107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71304368262627966418283237 13369569049242743703428107)
            ·
              refine ⟨20054353573864115555142161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13369569049242743703428107 20054353573864115555142161)
              ·
                refine ⟨15040765180398086666356621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20054353573864115555142161 15040765180398086666356621)
                ·
                  refine ⟨5640286942649282499883733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15040765180398086666356621 5640286942649282499883733)
                  ·
                    refine ⟨132194225218342558591025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5640286942649282499883733 132194225218342558591025)
                    ·
                      rfl

theorem cell22_386171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_386171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386171 prefixEnd_386171 := by exact prefixLift 386171
  have htrace : WordTrace (prefixWord ++ tailWord_386171) baseStart_386171 baseEnd_386171 := by
    simpa [prefixWord, tailWord_386171, baseEnd_386171] using wordTrace_append hprefix tailTrace_386171
  have hstable : (prefixWord ++ tailWord_386171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386171).length < 2 ^ (prefixWord ++ tailWord_386171).sum := by decide
  have hdescent : baseEnd_386171 < baseStart_386171 := by decide
  rcases family_descends (prefixWord ++ tailWord_386171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386190 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_386190 : Nat := 118140960795 + 386190 * 2 ^ 59
def prefixEnd_386190 : Nat := 4983230072969 + 3 ^ 40 * 386190 * 2
def baseEnd_386190 : Nat := 44066909768877614121989

theorem tailTrace_386190 : CollatzResearch.WordTrace tailWord_386190 prefixEnd_386190 44066909768877614121989 := by
  unfold tailWord_386190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760688308863382605760503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9390337647271373897389349 1760688308863382605760503)
  ·
    refine ⟨2641032463295073908640755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760688308863382605760503 2641032463295073908640755)
    ·
      refine ⟨3961548694942610862961133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641032463295073908640755 3961548694942610862961133)
      ·
        refine ⟨1485580760603479073610425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3961548694942610862961133 1485580760603479073610425)
        ·
          refine ⟨1114185570452609305207819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485580760603479073610425 1114185570452609305207819)
          ·
            refine ⟨1671278355678913957811729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114185570452609305207819 1671278355678913957811729)
            ·
              refine ⟨1253458766759185468358797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671278355678913957811729 1253458766759185468358797)
              ·
                refine ⟨470047037534694550634549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1253458766759185468358797 470047037534694550634549)
                ·
                  refine ⟨44066909768877614121989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470047037534694550634549 44066909768877614121989)
                  ·
                    rfl

theorem cell22_386190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_386190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386190 prefixEnd_386190 := by exact prefixLift 386190
  have htrace : WordTrace (prefixWord ++ tailWord_386190) baseStart_386190 baseEnd_386190 := by
    simpa [prefixWord, tailWord_386190, baseEnd_386190] using wordTrace_append hprefix tailTrace_386190
  have hstable : (prefixWord ++ tailWord_386190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386190).length < 2 ^ (prefixWord ++ tailWord_386190).sum := by decide
  have hdescent : baseEnd_386190 < baseStart_386190 := by decide
  rcases family_descends (prefixWord ++ tailWord_386190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386248 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_386248 : Nat := 118140960795 + 386248 * 2 ^ 59
def prefixEnd_386248 : Nat := 4983230072969 + 3 ^ 40 * 386248 * 2
def baseEnd_386248 : Nat := 132220583891940024415789

theorem tailTrace_386248 : CollatzResearch.WordTrace tailWord_386248 prefixEnd_386248 132220583891940024415789 := by
  unfold tailWord_386248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043810952348468375847699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9391747936464624501130265 7043810952348468375847699)
  ·
    refine ⟨10565716428522702563771549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7043810952348468375847699 10565716428522702563771549)
    ·
      refine ⟨3962143660696013461414331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10565716428522702563771549 3962143660696013461414331)
      ·
        refine ⟨5943215491044020192121497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962143660696013461414331 5943215491044020192121497)
        ·
          refine ⟨4457411618283015144091123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943215491044020192121497 4457411618283015144091123)
          ·
            refine ⟨6686117427424522716136685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457411618283015144091123 6686117427424522716136685)
            ·
              refine ⟨2507294035284196018551257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6686117427424522716136685 2507294035284196018551257)
              ·
                refine ⟨1880470526463147013913443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507294035284196018551257 1880470526463147013913443)
                ·
                  refine ⟨2820705789694720520870165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880470526463147013913443 2820705789694720520870165)
                  ·
                    refine ⟨132220583891940024415789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2820705789694720520870165 132220583891940024415789)
                    ·
                      rfl

theorem cell22_386248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_386248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386248 prefixEnd_386248 := by exact prefixLift 386248
  have htrace : WordTrace (prefixWord ++ tailWord_386248) baseStart_386248 baseEnd_386248 := by
    simpa [prefixWord, tailWord_386248, baseEnd_386248] using wordTrace_append hprefix tailTrace_386248
  have hstable : (prefixWord ++ tailWord_386248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386248).length < 2 ^ (prefixWord ++ tailWord_386248).sum := by decide
  have hdescent : baseEnd_386248 < baseStart_386248 := by decide
  rcases family_descends (prefixWord ++ tailWord_386248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386250 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_386250 : Nat := 118140960795 + 386250 * 2 ^ 59
def prefixEnd_386250 : Nat := 4983230072969 + 3 ^ 40 * 386250 * 2
def baseEnd_386250 : Nat := 132221268532812685865783

theorem tailTrace_386250 : CollatzResearch.WordTrace tailWord_386250 prefixEnd_386250 132221268532812685865783 := by
  unfold tailWord_386250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521923712672422773317051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9391796567126460728845469 3521923712672422773317051)
  ·
    refine ⟨5282885569008634159975577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521923712672422773317051 5282885569008634159975577)
    ·
      refine ⟨3962164176756475619981683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5282885569008634159975577 3962164176756475619981683)
      ·
        refine ⟨5943246265134713429972525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962164176756475619981683 5943246265134713429972525)
        ·
          refine ⟨2228717349425517536239697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5943246265134713429972525 2228717349425517536239697)
          ·
            refine ⟨1671538012069138152179773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228717349425517536239697 1671538012069138152179773)
            ·
              refine ⟨626826754525926807067415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1671538012069138152179773 626826754525926807067415)
              ·
                refine ⟨940240131788890210601123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626826754525926807067415 940240131788890210601123)
                ·
                  refine ⟨1410360197683335315901685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940240131788890210601123 1410360197683335315901685)
                  ·
                    refine ⟨132221268532812685865783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1410360197683335315901685 132221268532812685865783)
                    ·
                      rfl

theorem cell22_386250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_386250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386250 prefixEnd_386250 := by exact prefixLift 386250
  have htrace : WordTrace (prefixWord ++ tailWord_386250) baseStart_386250 baseEnd_386250 := by
    simpa [prefixWord, tailWord_386250, baseEnd_386250] using wordTrace_append hprefix tailTrace_386250
  have hstable : (prefixWord ++ tailWord_386250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386250).length < 2 ^ (prefixWord ++ tailWord_386250).sum := by decide
  have hdescent : baseEnd_386250 < baseStart_386250 := by decide
  rcases family_descends (prefixWord ++ tailWord_386250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386323 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_386323 : Nat := 118140960795 + 386323 * 2 ^ 59
def prefixEnd_386323 : Nat := 4983230072969 + 3 ^ 40 * 386323 * 2
def baseEnd_386323 : Nat := 132246257924664828790559

theorem tailTrace_386323 : CollatzResearch.WordTrace tailWord_386323 prefixEnd_386323 132246257924664828790559 := by
  unfold tailWord_386323
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090357379425224560675623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9393571586283483040450415 14090357379425224560675623)
  ·
    refine ⟨21135536069137836841013435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14090357379425224560675623 21135536069137836841013435)
    ·
      refine ⟨31703304103706755261520153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21135536069137836841013435 31703304103706755261520153)
      ·
        refine ⟨23777478077780066446140115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31703304103706755261520153 23777478077780066446140115)
        ·
          refine ⟨35666217116670099669210173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23777478077780066446140115 35666217116670099669210173)
          ·
            refine ⟨13374831418751287375953815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35666217116670099669210173 13374831418751287375953815)
            ·
              refine ⟨20062247128126931063930723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13374831418751287375953815 20062247128126931063930723)
              ·
                refine ⟨30093370692190396595896085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20062247128126931063930723 30093370692190396595896085)
                ·
                  refine ⟨1410626751196424840432629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30093370692190396595896085 1410626751196424840432629)
                  ·
                    refine ⟨132246257924664828790559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1410626751196424840432629 132246257924664828790559)
                    ·
                      rfl

theorem cell22_386323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_386323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386323 prefixEnd_386323 := by exact prefixLift 386323
  have htrace : WordTrace (prefixWord ++ tailWord_386323) baseStart_386323 baseEnd_386323 := by
    simpa [prefixWord, tailWord_386323, baseEnd_386323] using wordTrace_append hprefix tailTrace_386323
  have hstable : (prefixWord ++ tailWord_386323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386323).length < 2 ^ (prefixWord ++ tailWord_386323).sum := by decide
  have hdescent : baseEnd_386323 < baseStart_386323 := by decide
  rcases family_descends (prefixWord ++ tailWord_386323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386340 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_386340 : Nat := 118140960795 + 386340 * 2 ^ 59
def prefixEnd_386340 : Nat := 4983230072969 + 3 ^ 40 * 386340 * 2
def baseEnd_386340 : Nat := 132252077372082451115507

theorem tailTrace_386340 : CollatzResearch.WordTrace tailWord_386340 prefixEnd_386340 132252077372082451115507 := by
  unfold tailWord_386340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045488710181818232022237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9393984946909090976029649 7045488710181818232022237)
  ·
    refine ⟨2642058266318181837008339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7045488710181818232022237 2642058266318181837008339)
    ·
      refine ⟨3963087399477272755512509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642058266318181837008339 3963087399477272755512509)
      ·
        refine ⟨1486157774803977283317191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3963087399477272755512509 1486157774803977283317191)
        ·
          refine ⟨2229236662205965924975787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486157774803977283317191 2229236662205965924975787)
          ·
            refine ⟨3343854993308948887463681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229236662205965924975787 3343854993308948887463681)
            ·
              refine ⟨2507891244981711665597761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3343854993308948887463681 2507891244981711665597761)
              ·
                refine ⟨1880918433736283749198321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507891244981711665597761 1880918433736283749198321)
                ·
                  refine ⟨1410688825302212811898741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880918433736283749198321 1410688825302212811898741)
                  ·
                    refine ⟨132252077372082451115507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1410688825302212811898741 132252077372082451115507)
                    ·
                      rfl

theorem cell22_386340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_386340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386340 prefixEnd_386340 := by exact prefixLift 386340
  have htrace : WordTrace (prefixWord ++ tailWord_386340) baseStart_386340 baseEnd_386340 := by
    simpa [prefixWord, tailWord_386340, baseEnd_386340] using wordTrace_append hprefix tailTrace_386340
  have hstable : (prefixWord ++ tailWord_386340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386340).length < 2 ^ (prefixWord ++ tailWord_386340).sum := by decide
  have hdescent : baseEnd_386340 < baseStart_386340 := by decide
  rcases family_descends (prefixWord ++ tailWord_386340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386346 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_386346 : Nat := 118140960795 + 386346 * 2 ^ 59
def prefixEnd_386346 : Nat := 4983230072969 + 3 ^ 40 * 386346 * 2
def baseEnd_386346 : Nat := 132254131294700435465489

theorem tailTrace_386346 : CollatzResearch.WordTrace tailWord_386346 prefixEnd_386346 132254131294700435465489 := by
  unfold tailWord_386346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522799064585474872190723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9394130838894599659175261 3522799064585474872190723)
  ·
    refine ⟨5284198596878212308286085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3522799064585474872190723 5284198596878212308286085)
    ·
      refine ⟨990787236914664807803641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5284198596878212308286085 990787236914664807803641)
      ·
        refine ⟨743090427685998605852731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990787236914664807803641 743090427685998605852731)
        ·
          refine ⟨1114635641528997908779097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743090427685998605852731 1114635641528997908779097)
          ·
            refine ⟨835976731146748431584323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114635641528997908779097 835976731146748431584323)
            ·
              refine ⟨1253965096720122647376485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835976731146748431584323 1253965096720122647376485)
              ·
                refine ⟨235118455635022996383091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1253965096720122647376485 235118455635022996383091)
                ·
                  refine ⟨352677683452534494574637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235118455635022996383091 352677683452534494574637)
                  ·
                    refine ⟨132254131294700435465489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352677683452534494574637 132254131294700435465489)
                    ·
                      rfl

theorem cell22_386346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_386346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386346 prefixEnd_386346 := by exact prefixLift 386346
  have htrace : WordTrace (prefixWord ++ tailWord_386346) baseStart_386346 baseEnd_386346 := by
    simpa [prefixWord, tailWord_386346, baseEnd_386346] using wordTrace_append hprefix tailTrace_386346
  have hstable : (prefixWord ++ tailWord_386346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386346).length < 2 ^ (prefixWord ++ tailWord_386346).sum := by decide
  have hdescent : baseEnd_386346 < baseStart_386346 := by decide
  rcases family_descends (prefixWord ++ tailWord_386346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386355 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 3, 4]
def baseStart_386355 : Nat := 118140960795 + 386355 * 2 ^ 59
def prefixEnd_386355 : Nat := 4983230072969 + 3 ^ 40 * 386355 * 2
def baseEnd_386355 : Nat := 132257212178627411990461

theorem tailTrace_386355 : CollatzResearch.WordTrace tailWord_386355 prefixEnd_386355 132257212178627411990461 := by
  unfold tailWord_386355
  simp only [CollatzResearch.WordTrace]
  refine ⟨14091524515309294025840519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9394349676872862683893679 14091524515309294025840519)
  ·
    refine ⟨21137286772963941038760779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14091524515309294025840519 21137286772963941038760779)
    ·
      refine ⟨31705930159445911558141169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21137286772963941038760779 31705930159445911558141169)
      ·
        refine ⟨23779447619584433668605877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31705930159445911558141169 23779447619584433668605877)
        ·
          refine ⟨2229323214336040656431801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23779447619584433668605877 2229323214336040656431801)
          ·
            refine ⟨1671992410752030492323851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229323214336040656431801 1671992410752030492323851)
            ·
              refine ⟨2507988616128045738485777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671992410752030492323851 2507988616128045738485777)
              ·
                refine ⟨1880991462096034303864333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507988616128045738485777 1880991462096034303864333)
                ·
                  refine ⟨705371798286012863949125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1880991462096034303864333 705371798286012863949125)
                  ·
                    refine ⟨132257212178627411990461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705371798286012863949125 132257212178627411990461)
                    ·
                      rfl

theorem cell22_386355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_386355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386355 prefixEnd_386355 := by exact prefixLift 386355
  have htrace : WordTrace (prefixWord ++ tailWord_386355) baseStart_386355 baseEnd_386355 := by
    simpa [prefixWord, tailWord_386355, baseEnd_386355] using wordTrace_append hprefix tailTrace_386355
  have hstable : (prefixWord ++ tailWord_386355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386355).length < 2 ^ (prefixWord ++ tailWord_386355).sum := by decide
  have hdescent : baseEnd_386355 < baseStart_386355 := by decide
  rcases family_descends (prefixWord ++ tailWord_386355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386385 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_386385 : Nat := 118140960795 + 386385 * 2 ^ 59
def prefixEnd_386385 : Nat := 4983230072969 + 3 ^ 40 * 386385 * 2
def baseEnd_386385 : Nat := 132267481791717333740369

theorem tailTrace_386385 : CollatzResearch.WordTrace tailWord_386385 prefixEnd_386385 132267481791717333740369 := by
  unfold tailWord_386385
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092618705200609149432609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9395079136800406099621739 14092618705200609149432609)
  ·
    refine ⟨10569464028900456862074457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14092618705200609149432609 10569464028900456862074457)
    ·
      refine ⟨7927098021675342646555843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10569464028900456862074457 7927098021675342646555843)
      ·
        refine ⟨11890647032513013969833765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7927098021675342646555843 11890647032513013969833765)
        ·
          refine ⟨2229496318596190119343831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11890647032513013969833765 2229496318596190119343831)
          ·
            refine ⟨3344244477894285179015747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229496318596190119343831 3344244477894285179015747)
            ·
              refine ⟨5016366716841427768523621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344244477894285179015747 5016366716841427768523621)
              ·
                refine ⟨940568759407767706598179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5016366716841427768523621 940568759407767706598179)
                ·
                  refine ⟨1410853139111651559897269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940568759407767706598179 1410853139111651559897269)
                  ·
                    refine ⟨132267481791717333740369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1410853139111651559897269 132267481791717333740369)
                    ·
                      rfl

theorem cell22_386385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_386385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386385 prefixEnd_386385 := by exact prefixLift 386385
  have htrace : WordTrace (prefixWord ++ tailWord_386385) baseStart_386385 baseEnd_386385 := by
    simpa [prefixWord, tailWord_386385, baseEnd_386385] using wordTrace_append hprefix tailTrace_386385
  have hstable : (prefixWord ++ tailWord_386385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386385).length < 2 ^ (prefixWord ++ tailWord_386385).sum := by decide
  have hdescent : baseEnd_386385 < baseStart_386385 := by decide
  rcases family_descends (prefixWord ++ tailWord_386385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386387 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 4]
def baseStart_386387 : Nat := 118140960795 + 386387 * 2 ^ 59
def prefixEnd_386387 : Nat := 4983230072969 + 3 ^ 40 * 386387 * 2
def baseEnd_386387 : Nat := 44089388810863331730121

theorem tailTrace_386387 : CollatzResearch.WordTrace tailWord_386387 prefixEnd_386387 44089388810863331730121 := by
  unfold tailWord_386387
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092691651193363491005415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9395127767462242327336943 14092691651193363491005415)
  ·
    refine ⟨21139037476790045236508123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14092691651193363491005415 21139037476790045236508123)
    ·
      refine ⟨31708556215185067854762185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21139037476790045236508123 31708556215185067854762185)
      ·
        refine ⟨23781417161388800891071639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31708556215185067854762185 23781417161388800891071639)
        ·
          refine ⟨35672125742083201336607459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23781417161388800891071639 35672125742083201336607459)
          ·
            refine ⟨53508188613124802004911189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35672125742083201336607459 53508188613124802004911189)
            ·
              refine ⟨627049085310056273495053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 53508188613124802004911189 627049085310056273495053)
              ·
                refine ⟨235143406991271102560645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 627049085310056273495053 235143406991271102560645)
                ·
                  refine ⟨44089388810863331730121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235143406991271102560645 44089388810863331730121)
                  ·
                    rfl

theorem cell22_386387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 4].length) (baseStart_386387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386387 prefixEnd_386387 := by exact prefixLift 386387
  have htrace : WordTrace (prefixWord ++ tailWord_386387) baseStart_386387 baseEnd_386387 := by
    simpa [prefixWord, tailWord_386387, baseEnd_386387] using wordTrace_append hprefix tailTrace_386387
  have hstable : (prefixWord ++ tailWord_386387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386387).length < 2 ^ (prefixWord ++ tailWord_386387).sum := by decide
  have hdescent : baseEnd_386387 < baseStart_386387 := by decide
  rcases family_descends (prefixWord ++ tailWord_386387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386389 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_386389 : Nat := 118140960795 + 386389 * 2 ^ 59
def prefixEnd_386389 : Nat := 4983230072969 + 3 ^ 40 * 386389 * 2
def baseEnd_386389 : Nat := 132268851073462656640357

theorem tailTrace_386389 : CollatzResearch.WordTrace tailWord_386389 prefixEnd_386389 132268851073462656640357 := by
  unfold tailWord_386389
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092764597186117832578221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9395176398124078555052147 14092764597186117832578221)
  ·
    refine ⟨5284786723944794187216833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14092764597186117832578221 5284786723944794187216833)
    ·
      refine ⟨3963590042958595640412625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5284786723944794187216833 3963590042958595640412625)
      ·
        refine ⟨2972692532218946730309469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3963590042958595640412625 2972692532218946730309469)
        ·
          refine ⟨1114759699582105023866051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2972692532218946730309469 1114759699582105023866051)
          ·
            refine ⟨1672139549373157535799077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114759699582105023866051 1672139549373157535799077)
            ·
              refine ⟨313526165507467037962327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1672139549373157535799077 313526165507467037962327)
              ·
                refine ⟨470289248261200556943491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313526165507467037962327 470289248261200556943491)
                ·
                  refine ⟨705433872391800835415237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470289248261200556943491 705433872391800835415237)
                  ·
                    refine ⟨132268851073462656640357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705433872391800835415237 132268851073462656640357)
                    ·
                      rfl

theorem cell22_386389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_386389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386389 prefixEnd_386389 := by exact prefixLift 386389
  have htrace : WordTrace (prefixWord ++ tailWord_386389) baseStart_386389 baseEnd_386389 := by
    simpa [prefixWord, tailWord_386389, baseEnd_386389] using wordTrace_append hprefix tailTrace_386389
  have hstable : (prefixWord ++ tailWord_386389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386389).length < 2 ^ (prefixWord ++ tailWord_386389).sum := by decide
  have hdescent : baseEnd_386389 < baseStart_386389 := by decide
  rcases family_descends (prefixWord ++ tailWord_386389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386434 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_386434 : Nat := 118140960795 + 386434 * 2 ^ 59
def prefixEnd_386434 : Nat := 4983230072969 + 3 ^ 40 * 386434 * 2
def baseEnd_386434 : Nat := 132284255493097539265219

theorem tailTrace_386434 : CollatzResearch.WordTrace tailWord_386434 prefixEnd_386434 132284255493097539265219 := by
  unfold tailWord_386434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523601470505772629491589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9396270588015393678644237 3523601470505772629491589)
  ·
    refine ⟨660675275719832368029673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3523601470505772629491589 660675275719832368029673)
    ·
      refine ⟨495506456789874276022255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660675275719832368029673 495506456789874276022255)
      ·
        refine ⟨743259685184811414033383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495506456789874276022255 743259685184811414033383)
        ·
          refine ⟨1114889527777217121050075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743259685184811414033383 1114889527777217121050075)
          ·
            refine ⟨1672334291665825681575113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114889527777217121050075 1672334291665825681575113)
            ·
              refine ⟨1254250718749369261181335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672334291665825681575113 1254250718749369261181335)
              ·
                refine ⟨1881376078124053891772003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254250718749369261181335 1881376078124053891772003)
                ·
                  refine ⟨2822064117186080837658005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881376078124053891772003 2822064117186080837658005)
                  ·
                    refine ⟨132284255493097539265219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2822064117186080837658005 132284255493097539265219)
                    ·
                      rfl

theorem cell22_386434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_386434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386434 prefixEnd_386434 := by exact prefixLift 386434
  have htrace : WordTrace (prefixWord ++ tailWord_386434) baseStart_386434 baseEnd_386434 := by
    simpa [prefixWord, tailWord_386434, baseEnd_386434] using wordTrace_append hprefix tailTrace_386434
  have hstable : (prefixWord ++ tailWord_386434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386434).length < 2 ^ (prefixWord ++ tailWord_386434).sum := by decide
  have hdescent : baseEnd_386434 < baseStart_386434 := by decide
  rcases family_descends (prefixWord ++ tailWord_386434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386507 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 1, 4]
def baseStart_386507 : Nat := 118140960795 + 386507 * 2 ^ 59
def prefixEnd_386507 : Nat := 4983230072969 + 3 ^ 40 * 386507 * 2
def baseEnd_386507 : Nat := 132309244884949682189995

theorem tailTrace_386507 : CollatzResearch.WordTrace tailWord_386507 prefixEnd_386507 132309244884949682189995 := by
  unfold tailWord_386507
  simp only [CollatzResearch.WordTrace]
  refine ⟨14097068410758623985373775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9398045607172415990249183 14097068410758623985373775)
  ·
    refine ⟨21145602616137935978060663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14097068410758623985373775 21145602616137935978060663)
    ·
      refine ⟨31718403924206903967090995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21145602616137935978060663 31718403924206903967090995)
      ·
        refine ⟨47577605886310355950636493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31718403924206903967090995 47577605886310355950636493)
        ·
          refine ⟨17841602207366383481488685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47577605886310355950636493 17841602207366383481488685)
          ·
            refine ⟨6690600827762393805558257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17841602207366383481488685 6690600827762393805558257)
            ·
              refine ⟨5017950620821795354168693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690600827762393805558257 5017950620821795354168693)
              ·
                refine ⟨470432870702043314453315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5017950620821795354168693 470432870702043314453315)
                ·
                  refine ⟨705649306053064971679973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470432870702043314453315 705649306053064971679973)
                  ·
                    refine ⟨132309244884949682189995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705649306053064971679973 132309244884949682189995)
                    ·
                      rfl

theorem cell22_386507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 4].length) (baseStart_386507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386507 prefixEnd_386507 := by exact prefixLift 386507
  have htrace : WordTrace (prefixWord ++ tailWord_386507) baseStart_386507 baseEnd_386507 := by
    simpa [prefixWord, tailWord_386507, baseEnd_386507] using wordTrace_append hprefix tailTrace_386507
  have hstable : (prefixWord ++ tailWord_386507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386507).length < 2 ^ (prefixWord ++ tailWord_386507).sum := by decide
  have hdescent : baseEnd_386507 < baseStart_386507 := by decide
  rcases family_descends (prefixWord ++ tailWord_386507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386552 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_386552 : Nat := 118140960795 + 386552 * 2 ^ 59
def prefixEnd_386552 : Nat := 4983230072969 + 3 ^ 40 * 386552 * 2
def baseEnd_386552 : Nat := 132324649304584564814857

theorem tailTrace_386552 : CollatzResearch.WordTrace tailWord_386552 prefixEnd_386552 132324649304584564814857 := by
  unfold tailWord_386552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049354847797798335380955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9399139797063731113841273 7049354847797798335380955)
  ·
    refine ⟨10574032271696697503071433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7049354847797798335380955 10574032271696697503071433)
    ·
      refine ⟨7930524203772523127303575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10574032271696697503071433 7930524203772523127303575)
      ·
        refine ⟨11895786305658784690955363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7930524203772523127303575 11895786305658784690955363)
        ·
          refine ⟨17843679458488177036433045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11895786305658784690955363 17843679458488177036433045)
          ·
            refine ⟨836422474616633298582799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17843679458488177036433045 836422474616633298582799)
            ·
              refine ⟨1254633711924949947874199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836422474616633298582799 1254633711924949947874199)
              ·
                refine ⟨1881950567887424921811299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254633711924949947874199 1881950567887424921811299)
                ·
                  refine ⟨2822925851831137382716949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881950567887424921811299 2822925851831137382716949)
                  ·
                    refine ⟨132324649304584564814857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2822925851831137382716949 132324649304584564814857)
                    ·
                      rfl

theorem cell22_386552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_386552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386552 prefixEnd_386552 := by exact prefixLift 386552
  have htrace : WordTrace (prefixWord ++ tailWord_386552) baseStart_386552 baseEnd_386552 := by
    simpa [prefixWord, tailWord_386552, baseEnd_386552] using wordTrace_append hprefix tailTrace_386552
  have hstable : (prefixWord ++ tailWord_386552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386552).length < 2 ^ (prefixWord ++ tailWord_386552).sum := by decide
  have hdescent : baseEnd_386552 < baseStart_386552 := by decide
  rcases family_descends (prefixWord ++ tailWord_386552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386558 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_386558 : Nat := 118140960795 + 386558 * 2 ^ 59
def prefixEnd_386558 : Nat := 4983230072969 + 3 ^ 40 * 386558 * 2
def baseEnd_386558 : Nat := 132326703227202549164839

theorem tailTrace_386558 : CollatzResearch.WordTrace tailWord_386558 prefixEnd_386558 132326703227202549164839 := by
  unfold tailWord_386558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1762366066696732461935041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9399285689049239796986885 1762366066696732461935041)
  ·
    refine ⟨1321774550022549346451281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1762366066696732461935041 1321774550022549346451281)
    ·
      refine ⟨991330912516912009838461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1321774550022549346451281 991330912516912009838461)
      ·
        refine ⟨371749092193842003689423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 991330912516912009838461 371749092193842003689423)
        ·
          refine ⟨557623638290763005534135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371749092193842003689423 557623638290763005534135)
          ·
            refine ⟨836435457436144508301203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557623638290763005534135 836435457436144508301203)
            ·
              refine ⟨1254653186154216762451805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836435457436144508301203 1254653186154216762451805)
              ·
                refine ⟨470494944807831285919427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254653186154216762451805 470494944807831285919427)
                ·
                  refine ⟨705742417211746928879141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470494944807831285919427 705742417211746928879141)
                  ·
                    refine ⟨132326703227202549164839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705742417211746928879141 132326703227202549164839)
                    ·
                      rfl

theorem cell22_386558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_386558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386558 prefixEnd_386558 := by exact prefixLift 386558
  have htrace : WordTrace (prefixWord ++ tailWord_386558) baseStart_386558 baseEnd_386558 := by
    simpa [prefixWord, tailWord_386558, baseEnd_386558] using wordTrace_append hprefix tailTrace_386558
  have hstable : (prefixWord ++ tailWord_386558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386558).length < 2 ^ (prefixWord ++ tailWord_386558).sum := by decide
  have hdescent : baseEnd_386558 < baseStart_386558 := by decide
  rcases family_descends (prefixWord ++ tailWord_386558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386567 : List Nat := [1, 1, 4, 3, 2, 2, 9]
def baseStart_386567 : Nat := 118140960795 + 386567 * 2 ^ 59
def prefixEnd_386567 : Nat := 4983230072969 + 3 ^ 40 * 386567 * 2
def baseEnd_386567 : Nat := 4901103115227019469993

theorem tailTrace_386567 : CollatzResearch.WordTrace tailWord_386567 prefixEnd_386567 4901103115227019469993 := by
  unfold tailWord_386567
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099256790541254232557955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9399504527027502821705303 14099256790541254232557955)
  ·
    refine ⟨21148885185811881348836933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14099256790541254232557955 21148885185811881348836933)
    ·
      refine ⟨3965415972339727752906925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21148885185811881348836933 3965415972339727752906925)
      ·
        refine ⟨1487030989627397907340097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3965415972339727752906925 1487030989627397907340097)
        ·
          refine ⟨1115273242220548430505073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487030989627397907340097 1115273242220548430505073)
          ·
            refine ⟨836454931665411322878805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115273242220548430505073 836454931665411322878805)
            ·
              refine ⟨4901103115227019469993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 836454931665411322878805 4901103115227019469993)
              ·
                rfl

theorem cell22_386567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 9].length) (baseStart_386567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386567 prefixEnd_386567 := by exact prefixLift 386567
  have htrace : WordTrace (prefixWord ++ tailWord_386567) baseStart_386567 baseEnd_386567 := by
    simpa [prefixWord, tailWord_386567, baseEnd_386567] using wordTrace_append hprefix tailTrace_386567
  have hstable : (prefixWord ++ tailWord_386567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386567).length < 2 ^ (prefixWord ++ tailWord_386567).sum := by decide
  have hdescent : baseEnd_386567 < baseStart_386567 := by decide
  rcases family_descends (prefixWord ++ tailWord_386567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386573 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 6]
def baseStart_386573 : Nat := 118140960795 + 386573 * 2 ^ 59
def prefixEnd_386573 : Nat := 4983230072969 + 3 ^ 40 * 386573 * 2
def baseEnd_386573 : Nat := 44110612677915836679931

theorem tailTrace_386573 : CollatzResearch.WordTrace tailWord_386573 prefixEnd_386573 44110612677915836679931 := by
  unfold tailWord_386573
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099475628519517257276373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9399650419013011504850915 14099475628519517257276373)
  ·
    refine ⟨330456460043426185717415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14099475628519517257276373 330456460043426185717415)
    ·
      refine ⟨495684690065139278576123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330456460043426185717415 495684690065139278576123)
      ·
        refine ⟨743527035097708917864185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495684690065139278576123 743527035097708917864185)
        ·
          refine ⟨557645276323281688398139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743527035097708917864185 557645276323281688398139)
          ·
            refine ⟨836467914484922532597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557645276323281688398139 836467914484922532597209)
            ·
              refine ⟨627350935863691899447907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836467914484922532597209 627350935863691899447907)
              ·
                refine ⟨941026403795537849171861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627350935863691899447907 941026403795537849171861)
                ·
                  refine ⟨44110612677915836679931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 941026403795537849171861 44110612677915836679931)
                  ·
                    rfl

theorem cell22_386573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_386573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386573 prefixEnd_386573 := by exact prefixLift 386573
  have htrace : WordTrace (prefixWord ++ tailWord_386573) baseStart_386573 baseEnd_386573 := by
    simpa [prefixWord, tailWord_386573, baseEnd_386573] using wordTrace_append hprefix tailTrace_386573
  have hstable : (prefixWord ++ tailWord_386573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386573).length < 2 ^ (prefixWord ++ tailWord_386573).sum := by decide
  have hdescent : baseEnd_386573 < baseStart_386573 := by decide
  rcases family_descends (prefixWord ++ tailWord_386573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386657 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 8]
def baseStart_386657 : Nat := 118140960795 + 386657 * 2 ^ 59
def prefixEnd_386657 : Nat := 4983230072969 + 3 ^ 40 * 386657 * 2
def baseEnd_386657 : Nat := 44120197650133096979845

theorem tailTrace_386657 : CollatzResearch.WordTrace tailWord_386657 prefixEnd_386657 44120197650133096979845 := by
  unfold tailWord_386657
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102539360215199603334225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9401692906810133068889483 14102539360215199603334225)
  ·
    refine ⟨10576904520161399702500669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14102539360215199603334225 10576904520161399702500669)
    ·
      refine ⟨3966339195060524888437751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10576904520161399702500669 3966339195060524888437751)
      ·
        refine ⟨5949508792590787332656627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966339195060524888437751 5949508792590787332656627)
        ·
          refine ⟨8924263188886180998984941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949508792590787332656627 8924263188886180998984941)
          ·
            refine ⟨3346598695832317874619353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8924263188886180998984941 3346598695832317874619353)
            ·
              refine ⟨2509949021874238405964515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346598695832317874619353 2509949021874238405964515)
              ·
                refine ⟨3764923532811357608946773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509949021874238405964515 3764923532811357608946773)
                ·
                  refine ⟨44120197650133096979845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3764923532811357608946773 44120197650133096979845)
                  ·
                    rfl

theorem cell22_386657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_386657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386657 prefixEnd_386657 := by exact prefixLift 386657
  have htrace : WordTrace (prefixWord ++ tailWord_386657) baseStart_386657 baseEnd_386657 := by
    simpa [prefixWord, tailWord_386657, baseEnd_386657] using wordTrace_append hprefix tailTrace_386657
  have hstable : (prefixWord ++ tailWord_386657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386657).length < 2 ^ (prefixWord ++ tailWord_386657).sum := by decide
  have hdescent : baseEnd_386657 < baseStart_386657 := by decide
  rcases family_descends (prefixWord ++ tailWord_386657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386659 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 3, 4]
def baseStart_386659 : Nat := 118140960795 + 386659 * 2 ^ 59
def prefixEnd_386659 : Nat := 4983230072969 + 3 ^ 40 * 386659 * 2
def baseEnd_386659 : Nat := 132361277591271952389529

theorem tailTrace_386659 : CollatzResearch.WordTrace tailWord_386659 prefixEnd_386659 132361277591271952389529 := by
  unfold tailWord_386659
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102612306207953944907031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9401741537471969296604687 14102612306207953944907031)
  ·
    refine ⟨21153918459311930917360547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14102612306207953944907031 21153918459311930917360547)
    ·
      refine ⟨31730877688967896376040821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21153918459311930917360547 31730877688967896376040821)
      ·
        refine ⟨2974769783340740285253827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31730877688967896376040821 2974769783340740285253827)
        ·
          refine ⟨4462154675011110427880741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974769783340740285253827 4462154675011110427880741)
          ·
            refine ⟨836654001564583205227639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4462154675011110427880741 836654001564583205227639)
            ·
              refine ⟨1254981002346874807841459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836654001564583205227639 1254981002346874807841459)
              ·
                refine ⟨1882471503520312211762189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254981002346874807841459 1882471503520312211762189)
                ·
                  refine ⟨705926813820117079410821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1882471503520312211762189 705926813820117079410821)
                  ·
                    refine ⟨132361277591271952389529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705926813820117079410821 132361277591271952389529)
                    ·
                      rfl

theorem cell22_386659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_386659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386659 prefixEnd_386659 := by exact prefixLift 386659
  have htrace : WordTrace (prefixWord ++ tailWord_386659) baseStart_386659 baseEnd_386659 := by
    simpa [prefixWord, tailWord_386659, baseEnd_386659] using wordTrace_append hprefix tailTrace_386659
  have hstable : (prefixWord ++ tailWord_386659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386659).length < 2 ^ (prefixWord ++ tailWord_386659).sum := by decide
  have hdescent : baseEnd_386659 < baseStart_386659 := by decide
  rcases family_descends (prefixWord ++ tailWord_386659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386721 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_386721 : Nat := 118140960795 + 386721 * 2 ^ 59
def prefixEnd_386721 : Nat := 4983230072969 + 3 ^ 40 * 386721 * 2
def baseEnd_386721 : Nat := 132382501458324457339339

theorem tailTrace_386721 : CollatzResearch.WordTrace tailWord_386721 prefixEnd_386721 132382501458324457339339 := by
  unfold tailWord_386721
  simp only [CollatzResearch.WordTrace]
  refine ⟨14104873631983338533664017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9403249087988892355776011 14104873631983338533664017)
  ·
    refine ⟨10578655223987503900248013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14104873631983338533664017 10578655223987503900248013)
    ·
      refine ⟨3966995708995313962593005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10578655223987503900248013 3966995708995313962593005)
      ·
        refine ⟨1487623390873242735972377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3966995708995313962593005 1487623390873242735972377)
        ·
          refine ⟨1115717543154932051979283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487623390873242735972377 1115717543154932051979283)
          ·
            refine ⟨1673576314732398077968925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115717543154932051979283 1673576314732398077968925)
            ·
              refine ⟨627591118024649279238347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1673576314732398077968925 627591118024649279238347)
              ·
                refine ⟨941386677036973918857521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627591118024649279238347 941386677036973918857521)
                ·
                  refine ⟨706040007777730439143141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941386677036973918857521 706040007777730439143141)
                  ·
                    refine ⟨132382501458324457339339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706040007777730439143141 132382501458324457339339)
                    ·
                      rfl

theorem cell22_386721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_386721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386721 prefixEnd_386721 := by exact prefixLift 386721
  have htrace : WordTrace (prefixWord ++ tailWord_386721) baseStart_386721 baseEnd_386721 := by
    simpa [prefixWord, tailWord_386721, baseEnd_386721] using wordTrace_append hprefix tailTrace_386721
  have hstable : (prefixWord ++ tailWord_386721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386721).length < 2 ^ (prefixWord ++ tailWord_386721).sum := by decide
  have hdescent : baseEnd_386721 < baseStart_386721 := by decide
  rcases family_descends (prefixWord ++ tailWord_386721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386751 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 3, 3]
def baseStart_386751 : Nat := 118140960795 + 386751 * 2 ^ 59
def prefixEnd_386751 : Nat := 4983230072969 + 3 ^ 40 * 386751 * 2
def baseEnd_386751 : Nat := 132392771071414379089247

theorem tailTrace_386751 : CollatzResearch.WordTrace tailWord_386751 prefixEnd_386751 132392771071414379089247 := by
  unfold tailWord_386751
  simp only [CollatzResearch.WordTrace]
  refine ⟨14105967821874653657256107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9403978547916435771504071 14105967821874653657256107)
  ·
    refine ⟨21158951732811980485884161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14105967821874653657256107 21158951732811980485884161)
    ·
      refine ⟨15869213799608985364413121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21158951732811980485884161 15869213799608985364413121)
      ·
        refine ⟨11901910349706739023309841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15869213799608985364413121 11901910349706739023309841)
        ·
          refine ⟨8926432762280054267482381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11901910349706739023309841 8926432762280054267482381)
          ·
            refine ⟨3347412285855020350305893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8926432762280054267482381 3347412285855020350305893)
            ·
              refine ⟨627639803597816315682355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3347412285855020350305893 627639803597816315682355)
              ·
                refine ⟨941459705396724473523533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627639803597816315682355 941459705396724473523533)
                ·
                  refine ⟨353047389523771677571325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941459705396724473523533 353047389523771677571325)
                  ·
                    refine ⟨132392771071414379089247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353047389523771677571325 132392771071414379089247)
                    ·
                      rfl

theorem cell22_386751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_386751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386751 prefixEnd_386751 := by exact prefixLift 386751
  have htrace : WordTrace (prefixWord ++ tailWord_386751) baseStart_386751 baseEnd_386751 := by
    simpa [prefixWord, tailWord_386751, baseEnd_386751] using wordTrace_append hprefix tailTrace_386751
  have hstable : (prefixWord ++ tailWord_386751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386751).length < 2 ^ (prefixWord ++ tailWord_386751).sum := by decide
  have hdescent : baseEnd_386751 < baseStart_386751 := by decide
  rcases family_descends (prefixWord ++ tailWord_386751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386860 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 4]
def baseStart_386860 : Nat := 118140960795 + 386860 * 2 ^ 59
def prefixEnd_386860 : Nat := 4983230072969 + 3 ^ 40 * 386860 * 2
def baseEnd_386860 : Nat := 44143361332991476037971

theorem tailTrace_386860 : CollatzResearch.WordTrace tailWord_386860 prefixEnd_386860 44143361332991476037971 := by
  unfold tailWord_386860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7054971689239882636487017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9406628918986510181982689 7054971689239882636487017)
  ·
    refine ⟨5291228766929911977365263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7054971689239882636487017 5291228766929911977365263)
    ·
      refine ⟨7936843150394867966047895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5291228766929911977365263 7936843150394867966047895)
      ·
        refine ⟨11905264725592301949071843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7936843150394867966047895 11905264725592301949071843)
        ·
          refine ⟨17857897088388452923607765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905264725592301949071843 17857897088388452923607765)
          ·
            refine ⟨418544463009104365397057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17857897088388452923607765 418544463009104365397057)
            ·
              refine ⟨313908347256828274047793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418544463009104365397057 313908347256828274047793)
              ·
                refine ⟨235431260442621205535845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313908347256828274047793 235431260442621205535845)
                ·
                  refine ⟨44143361332991476037971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235431260442621205535845 44143361332991476037971)
                  ·
                    rfl

theorem cell22_386860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_386860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386860 prefixEnd_386860 := by exact prefixLift 386860
  have htrace : WordTrace (prefixWord ++ tailWord_386860) baseStart_386860 baseEnd_386860 := by
    simpa [prefixWord, tailWord_386860, baseEnd_386860] using wordTrace_append hprefix tailTrace_386860
  have hstable : (prefixWord ++ tailWord_386860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386860).length < 2 ^ (prefixWord ++ tailWord_386860).sum := by decide
  have hdescent : baseEnd_386860 < baseStart_386860 := by decide
  rcases family_descends (prefixWord ++ tailWord_386860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386920 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 1, 3]
def baseStart_386920 : Nat := 118140960795 + 386920 * 2 ^ 59
def prefixEnd_386920 : Nat := 4983230072969 + 3 ^ 40 * 386920 * 2
def baseEnd_386920 : Nat := 132450623225154271613729

theorem tailTrace_386920 : CollatzResearch.WordTrace tailWord_386920 prefixEnd_386920 132450623225154271613729 := by
  unfold tailWord_386920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056065879131197760079107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9408087838841597013438809 7056065879131197760079107)
  ·
    refine ⟨10584098818696796640118661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7056065879131197760079107 10584098818696796640118661)
    ·
      refine ⟨1984518528505649370022249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10584098818696796640118661 1984518528505649370022249)
      ·
        refine ⟨1488388896379237027516687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1984518528505649370022249 1488388896379237027516687)
        ·
          refine ⟨2232583344568855541275031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488388896379237027516687 2232583344568855541275031)
          ·
            refine ⟨3348875016853283311912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232583344568855541275031 3348875016853283311912547)
            ·
              refine ⟨5023312525279924967868821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348875016853283311912547 5023312525279924967868821)
              ·
                refine ⟨235467774622496482868851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5023312525279924967868821 235467774622496482868851)
                ·
                  refine ⟨353201661933744724303277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235467774622496482868851 353201661933744724303277)
                  ·
                    refine ⟨132450623225154271613729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353201661933744724303277 132450623225154271613729)
                    ·
                      rfl

theorem cell22_386920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_386920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386920 prefixEnd_386920 := by exact prefixLift 386920
  have htrace : WordTrace (prefixWord ++ tailWord_386920) baseStart_386920 baseEnd_386920 := by
    simpa [prefixWord, tailWord_386920, baseEnd_386920] using wordTrace_append hprefix tailTrace_386920
  have hstable : (prefixWord ++ tailWord_386920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386920).length < 2 ^ (prefixWord ++ tailWord_386920).sum := by decide
  have hdescent : baseEnd_386920 < baseStart_386920 := by decide
  rcases family_descends (prefixWord ++ tailWord_386920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386954 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_386954 : Nat := 118140960795 + 386954 * 2 ^ 59
def prefixEnd_386954 : Nat := 4983230072969 + 3 ^ 40 * 386954 * 2
def baseEnd_386954 : Nat := 132462262119989516263625

theorem tailTrace_386954 : CollatzResearch.WordTrace tailWord_386954 prefixEnd_386954 132462262119989516263625 := by
  unfold tailWord_386954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528342960034804831723979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9408914560092812884597277 3528342960034804831723979)
  ·
    refine ⟨5292514440052207247585969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3528342960034804831723979 5292514440052207247585969)
    ·
      refine ⟨3969385830039155435689477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5292514440052207247585969 3969385830039155435689477)
      ·
        refine ⟨744259843132341644191777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3969385830039155435689477 744259843132341644191777)
        ·
          refine ⟨558194882349256233143833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744259843132341644191777 558194882349256233143833)
          ·
            refine ⟨418646161761942174857875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558194882349256233143833 418646161761942174857875)
            ·
              refine ⟨627969242642913262286813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418646161761942174857875 627969242642913262286813)
              ·
                refine ⟨235488465991092473357555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 627969242642913262286813 235488465991092473357555)
                ·
                  refine ⟨353232698986638710036333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235488465991092473357555 353232698986638710036333)
                  ·
                    refine ⟨132462262119989516263625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353232698986638710036333 132462262119989516263625)
                    ·
                      rfl

theorem cell22_386954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_386954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386954 prefixEnd_386954 := by exact prefixLift 386954
  have htrace : WordTrace (prefixWord ++ tailWord_386954) baseStart_386954 baseEnd_386954 := by
    simpa [prefixWord, tailWord_386954, baseEnd_386954] using wordTrace_append hprefix tailTrace_386954
  have hstable : (prefixWord ++ tailWord_386954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386954).length < 2 ^ (prefixWord ++ tailWord_386954).sum := by decide
  have hdescent : baseEnd_386954 < baseStart_386954 := by decide
  rcases family_descends (prefixWord ++ tailWord_386954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386984 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 5]
def baseStart_386984 : Nat := 118140960795 + 386984 * 2 ^ 59
def prefixEnd_386984 : Nat := 4983230072969 + 3 ^ 40 * 386984 * 2
def baseEnd_386984 : Nat := 44157510577693146004511

theorem tailTrace_386984 : CollatzResearch.WordTrace tailWord_386984 prefixEnd_386984 44157510577693146004511 := by
  unfold tailWord_386984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7057233015015267225244003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9409644020020356300325337 7057233015015267225244003)
  ·
    refine ⟨10585849522522900837866005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7057233015015267225244003 10585849522522900837866005)
    ·
      refine ⟨496211696368260976774969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10585849522522900837866005 496211696368260976774969)
      ·
        refine ⟨372158772276195732581227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 496211696368260976774969 372158772276195732581227)
        ·
          refine ⟨558238158414293598871841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372158772276195732581227 558238158414293598871841)
          ·
            refine ⟨418678618810720199153881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558238158414293598871841 418678618810720199153881)
            ·
              refine ⟨314008964108040149365411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418678618810720199153881 314008964108040149365411)
              ·
                refine ⟨471013446162060224048117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314008964108040149365411 471013446162060224048117)
                ·
                  refine ⟨44157510577693146004511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 471013446162060224048117 44157510577693146004511)
                  ·
                    rfl

theorem cell22_386984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_386984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386984 prefixEnd_386984 := by exact prefixLift 386984
  have htrace : WordTrace (prefixWord ++ tailWord_386984) baseStart_386984 baseEnd_386984 := by
    simpa [prefixWord, tailWord_386984, baseEnd_386984] using wordTrace_append hprefix tailTrace_386984
  have hstable : (prefixWord ++ tailWord_386984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386984).length < 2 ^ (prefixWord ++ tailWord_386984).sum := by decide
  have hdescent : baseEnd_386984 < baseStart_386984 := by decide
  rcases family_descends (prefixWord ++ tailWord_386984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386991 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 4, 4]
def baseStart_386991 : Nat := 118140960795 + 386991 * 2 ^ 59
def prefixEnd_386991 : Nat := 4983230072969 + 3 ^ 40 * 386991 * 2
def baseEnd_386991 : Nat := 132474927976133753088511

theorem tailTrace_386991 : CollatzResearch.WordTrace tailWord_386991 prefixEnd_386991 132474927976133753088511 := by
  unfold tailWord_386991
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114721341005174645992827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9409814227336783097328551 14114721341005174645992827)
  ·
    refine ⟨21172082011507761968989241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14114721341005174645992827 21172082011507761968989241)
    ·
      refine ⟨15879061508630821476741931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21172082011507761968989241 15879061508630821476741931)
      ·
        refine ⟨23818592262946232215112897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15879061508630821476741931 23818592262946232215112897)
        ·
          refine ⟨17863944197209674161334673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23818592262946232215112897 17863944197209674161334673)
          ·
            refine ⟨13397958147907255621001005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17863944197209674161334673 13397958147907255621001005)
            ·
              refine ⟨5024234305465220857875377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13397958147907255621001005 5024234305465220857875377)
              ·
                refine ⟨3768175729098915643406533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024234305465220857875377 3768175729098915643406533)
                ·
                  refine ⟨706532949206046683138725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3768175729098915643406533 706532949206046683138725)
                  ·
                    refine ⟨132474927976133753088511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706532949206046683138725 132474927976133753088511)
                    ·
                      rfl

theorem cell22_386991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_386991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_386991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_386991 prefixEnd_386991 := by exact prefixLift 386991
  have htrace : WordTrace (prefixWord ++ tailWord_386991) baseStart_386991 baseEnd_386991 := by
    simpa [prefixWord, tailWord_386991, baseEnd_386991] using wordTrace_append hprefix tailTrace_386991
  have hstable : (prefixWord ++ tailWord_386991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386991).length < 2 ^ (prefixWord ++ tailWord_386991).sum := by decide
  have hdescent : baseEnd_386991 < baseStart_386991 := by decide
  rcases family_descends (prefixWord ++ tailWord_386991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387008 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_387008 : Nat := 118140960795 + 387008 * 2 ^ 59
def prefixEnd_387008 : Nat := 4983230072969 + 3 ^ 40 * 387008 * 2
def baseEnd_387008 : Nat := 132480747423551375413459

theorem tailTrace_387008 : CollatzResearch.WordTrace tailWord_387008 prefixEnd_387008 132480747423551375413459 := by
  unfold tailWord_387008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7057670690971793274680839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9410227587962391032907785 7057670690971793274680839)
  ·
    refine ⟨10586506036457689912021259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7057670690971793274680839 10586506036457689912021259)
    ·
      refine ⟨15879759054686534868031889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10586506036457689912021259 15879759054686534868031889)
      ·
        refine ⟨11909819291014901151023917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15879759054686534868031889 11909819291014901151023917)
        ·
          refine ⟨4466182234130587931633969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11909819291014901151023917 4466182234130587931633969)
          ·
            refine ⟨3349636675597940948725477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4466182234130587931633969 3349636675597940948725477)
            ·
              refine ⟨628056876674613927886027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3349636675597940948725477 628056876674613927886027)
              ·
                refine ⟨942085315011920891829041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628056876674613927886027 942085315011920891829041)
                ·
                  refine ⟨706563986258940668871781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942085315011920891829041 706563986258940668871781)
                  ·
                    refine ⟨132480747423551375413459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706563986258940668871781 132480747423551375413459)
                    ·
                      rfl

theorem cell22_387008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_387008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387008 prefixEnd_387008 := by exact prefixLift 387008
  have htrace : WordTrace (prefixWord ++ tailWord_387008) baseStart_387008 baseEnd_387008 := by
    simpa [prefixWord, tailWord_387008, baseEnd_387008] using wordTrace_append hprefix tailTrace_387008
  have hstable : (prefixWord ++ tailWord_387008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387008).length < 2 ^ (prefixWord ++ tailWord_387008).sum := by decide
  have hdescent : baseEnd_387008 < baseStart_387008 := by decide
  rcases family_descends (prefixWord ++ tailWord_387008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387145 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_387145 : Nat := 118140960795 + 387145 * 2 ^ 59
def prefixEnd_387145 : Nat := 4983230072969 + 3 ^ 40 * 387145 * 2
def baseEnd_387145 : Nat := 132527645323328684738039

theorem tailTrace_387145 : CollatzResearch.WordTrace tailWord_387145 prefixEnd_387145 132527645323328684738039 := by
  unfold tailWord_387145
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120338182447258947098889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9413558788298172631399259 14120338182447258947098889)
  ·
    refine ⟨10590253636835444210324167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14120338182447258947098889 10590253636835444210324167)
    ·
      refine ⟨15885380455253166315486251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10590253636835444210324167 15885380455253166315486251)
      ·
        refine ⟨23828070682879749473229377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15885380455253166315486251 23828070682879749473229377)
        ·
          refine ⟨17871053012159812104922033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23828070682879749473229377 17871053012159812104922033)
          ·
            refine ⟨13403289759119859078691525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17871053012159812104922033 13403289759119859078691525)
            ·
              refine ⟨2513116829834973577254661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13403289759119859078691525 2513116829834973577254661)
              ·
                refine ⟨471209405594057545735249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2513116829834973577254661 471209405594057545735249)
                ·
                  refine ⟨353407054195543159301437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471209405594057545735249 353407054195543159301437)
                  ·
                    refine ⟨132527645323328684738039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353407054195543159301437 132527645323328684738039)
                    ·
                      rfl

theorem cell22_387145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_387145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387145 prefixEnd_387145 := by exact prefixLift 387145
  have htrace : WordTrace (prefixWord ++ tailWord_387145) baseStart_387145 baseEnd_387145 := by
    simpa [prefixWord, tailWord_387145, baseEnd_387145] using wordTrace_append hprefix tailTrace_387145
  have hstable : (prefixWord ++ tailWord_387145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387145).length < 2 ^ (prefixWord ++ tailWord_387145).sum := by decide
  have hdescent : baseEnd_387145 < baseStart_387145 := by decide
  rcases family_descends (prefixWord ++ tailWord_387145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387295 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 2, 4]
def baseStart_387295 : Nat := 118140960795 + 387295 * 2 ^ 59
def prefixEnd_387295 : Nat := 4983230072969 + 3 ^ 40 * 387295 * 2
def baseEnd_387295 : Nat := 132578993388778293487579

theorem tailTrace_387295 : CollatzResearch.WordTrace tailWord_387295 prefixEnd_387295 132578993388778293487579 := by
  unfold tailWord_387295
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125809131903834565059339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9417206087935889710039559 14125809131903834565059339)
  ·
    refine ⟨21188713697855751847589009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14125809131903834565059339 21188713697855751847589009)
    ·
      refine ⟨15891535273391813885691757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21188713697855751847589009 15891535273391813885691757)
      ·
        refine ⟨5959325727521930207134409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15891535273391813885691757 5959325727521930207134409)
        ·
          refine ⟨4469494295641447655350807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5959325727521930207134409 4469494295641447655350807)
          ·
            refine ⟨6704241443462171483026211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469494295641447655350807 6704241443462171483026211)
            ·
              refine ⟨10056362165193257224539317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6704241443462171483026211 10056362165193257224539317)
              ·
                refine ⟨942783952986867864800561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10056362165193257224539317 942783952986867864800561)
                ·
                  refine ⟨707087964740150898600421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942783952986867864800561 707087964740150898600421)
                  ·
                    refine ⟨132578993388778293487579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 707087964740150898600421 132578993388778293487579)
                    ·
                      rfl

theorem cell22_387295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_387295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387295 prefixEnd_387295 := by exact prefixLift 387295
  have htrace : WordTrace (prefixWord ++ tailWord_387295) baseStart_387295 baseEnd_387295 := by
    simpa [prefixWord, tailWord_387295, baseEnd_387295] using wordTrace_append hprefix tailTrace_387295
  have hstable : (prefixWord ++ tailWord_387295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387295).length < 2 ^ (prefixWord ++ tailWord_387295).sum := by decide
  have hdescent : baseEnd_387295 < baseStart_387295 := by decide
  rcases family_descends (prefixWord ++ tailWord_387295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387342 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_387342 : Nat := 118140960795 + 387342 * 2 ^ 59
def prefixEnd_387342 : Nat := 4983230072969 + 3 ^ 40 * 387342 * 2
def baseEnd_387342 : Nat := 132595082449285837562435

theorem tailTrace_387342 : CollatzResearch.WordTrace tailWord_387342 prefixEnd_387342 132595082449285837562435 := by
  unfold tailWord_387342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765940420341695199002535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9418348908489041061346853 1765940420341695199002535)
  ·
    refine ⟨2648910630512542798503803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765940420341695199002535 2648910630512542798503803)
    ·
      refine ⟨3973365945768814197755705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648910630512542798503803 3973365945768814197755705)
      ·
        refine ⟨2980024459326610648316779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3973365945768814197755705 2980024459326610648316779)
        ·
          refine ⟨4470036688989915972475169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980024459326610648316779 4470036688989915972475169)
          ·
            refine ⟨3352527516742436979356377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4470036688989915972475169 3352527516742436979356377)
            ·
              refine ⟨2514395637556827734517283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352527516742436979356377 2514395637556827734517283)
              ·
                refine ⟨3771593456335241601775925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514395637556827734517283 3771593456335241601775925)
                ·
                  refine ⟨353586886531428900166493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771593456335241601775925 353586886531428900166493)
                  ·
                    refine ⟨132595082449285837562435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353586886531428900166493 132595082449285837562435)
                    ·
                      rfl

theorem cell22_387342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_387342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387342 prefixEnd_387342 := by exact prefixLift 387342
  have htrace : WordTrace (prefixWord ++ tailWord_387342) baseStart_387342 baseEnd_387342 := by
    simpa [prefixWord, tailWord_387342, baseEnd_387342] using wordTrace_append hprefix tailTrace_387342
  have hstable : (prefixWord ++ tailWord_387342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387342).length < 2 ^ (prefixWord ++ tailWord_387342).sum := by decide
  have hdescent : baseEnd_387342 < baseStart_387342 := by decide
  rcases family_descends (prefixWord ++ tailWord_387342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387367 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 4]
def baseStart_387367 : Nat := 118140960795 + 387367 * 2 ^ 59
def prefixEnd_387367 : Nat := 4983230072969 + 3 ^ 40 * 387367 * 2
def baseEnd_387367 : Nat := 44201213486731368562453

theorem tailTrace_387367 : CollatzResearch.WordTrace tailWord_387367 prefixEnd_387367 44201213486731368562453 := by
  unfold tailWord_387367
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128435187642990861680355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9418956791761993907786903 14128435187642990861680355)
  ·
    refine ⟨21192652781464486292520533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14128435187642990861680355 21192652781464486292520533)
    ·
      refine ⟨248351399782786948740475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 21192652781464486292520533 248351399782786948740475)
      ·
        refine ⟨372527099674180423110713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248351399782786948740475 372527099674180423110713)
        ·
          refine ⟨279395324755635317333035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372527099674180423110713 279395324755635317333035)
          ·
            refine ⟨419092987133452975999553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279395324755635317333035 419092987133452975999553)
            ·
              refine ⟨314319740350089731999665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419092987133452975999553 314319740350089731999665)
              ·
                refine ⟨235739805262567298999749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314319740350089731999665 235739805262567298999749)
                ·
                  refine ⟨44201213486731368562453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235739805262567298999749 44201213486731368562453)
                  ·
                    rfl

theorem cell22_387367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 4].length) (baseStart_387367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387367 prefixEnd_387367 := by exact prefixLift 387367
  have htrace : WordTrace (prefixWord ++ tailWord_387367) baseStart_387367 baseEnd_387367 := by
    simpa [prefixWord, tailWord_387367, baseEnd_387367] using wordTrace_append hprefix tailTrace_387367
  have hstable : (prefixWord ++ tailWord_387367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387367).length < 2 ^ (prefixWord ++ tailWord_387367).sum := by decide
  have hdescent : baseEnd_387367 < baseStart_387367 := by decide
  rcases family_descends (prefixWord ++ tailWord_387367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387400 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_387400 : Nat := 118140960795 + 387400 * 2 ^ 59
def prefixEnd_387400 : Nat := 4983230072969 + 3 ^ 40 * 387400 * 2
def baseEnd_387400 : Nat := 44204979011531006537419

theorem tailTrace_387400 : CollatzResearch.WordTrace tailWord_387400 prefixEnd_387400 44204979011531006537419 := by
  unfold tailWord_387400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064819398261718748815827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9419759197682291665087769 7064819398261718748815827)
  ·
    refine ⟨10597229097392578123223741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064819398261718748815827 10597229097392578123223741)
    ·
      refine ⟨3973960911522216796208903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10597229097392578123223741 3973960911522216796208903)
      ·
        refine ⟨5960941367283325194313355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3973960911522216796208903 5960941367283325194313355)
        ·
          refine ⟨8941412050924987791470033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960941367283325194313355 8941412050924987791470033)
          ·
            refine ⟨6706059038193740843602525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8941412050924987791470033 6706059038193740843602525)
            ·
              refine ⟨2514772139322652816350947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6706059038193740843602525 2514772139322652816350947)
              ·
                refine ⟨3772158208983979224526421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514772139322652816350947 3772158208983979224526421)
                ·
                  refine ⟨44204979011531006537419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3772158208983979224526421 44204979011531006537419)
                  ·
                    rfl

theorem cell22_387400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_387400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387400 prefixEnd_387400 := by exact prefixLift 387400
  have htrace : WordTrace (prefixWord ++ tailWord_387400) baseStart_387400 baseEnd_387400 := by
    simpa [prefixWord, tailWord_387400, baseEnd_387400] using wordTrace_append hprefix tailTrace_387400
  have hstable : (prefixWord ++ tailWord_387400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387400).length < 2 ^ (prefixWord ++ tailWord_387400).sum := by decide
  have hdescent : baseEnd_387400 < baseStart_387400 := by decide
  rcases family_descends (prefixWord ++ tailWord_387400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387434 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_387434 : Nat := 118140960795 + 387434 * 2 ^ 59
def prefixEnd_387434 : Nat := 4983230072969 + 3 ^ 40 * 387434 * 2
def baseEnd_387434 : Nat := 44208858643142754754051

theorem tailTrace_387434 : CollatzResearch.WordTrace tailWord_387434 prefixEnd_387434 44208858643142754754051 := by
  unfold tailWord_387434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532719719600065326092339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9420585918933507536246237 3532719719600065326092339)
  ·
    refine ⟨5299079579400097989138509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3532719719600065326092339 5299079579400097989138509)
    ·
      refine ⟨1987154842275036745926941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5299079579400097989138509 1987154842275036745926941)
      ·
        refine ⟨745183065853138779722603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1987154842275036745926941 745183065853138779722603)
        ·
          refine ⟨1117774598779708169583905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745183065853138779722603 1117774598779708169583905)
          ·
            refine ⟨838330949084781127187929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117774598779708169583905 838330949084781127187929)
            ·
              refine ⟨628748211813585845390947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838330949084781127187929 628748211813585845390947)
              ·
                refine ⟨943122317720378768086421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628748211813585845390947 943122317720378768086421)
                ·
                  refine ⟨44208858643142754754051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 943122317720378768086421 44208858643142754754051)
                  ·
                    rfl

theorem cell22_387434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_387434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387434 prefixEnd_387434 := by exact prefixLift 387434
  have htrace : WordTrace (prefixWord ++ tailWord_387434) baseStart_387434 baseEnd_387434 := by
    simpa [prefixWord, tailWord_387434, baseEnd_387434] using wordTrace_append hprefix tailTrace_387434
  have hstable : (prefixWord ++ tailWord_387434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387434).length < 2 ^ (prefixWord ++ tailWord_387434).sum := by decide
  have hdescent : baseEnd_387434 < baseStart_387434 := by decide
  rcases family_descends (prefixWord ++ tailWord_387434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387552 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_387552 : Nat := 118140960795 + 387552 * 2 ^ 59
def prefixEnd_387552 : Nat := 4983230072969 + 3 ^ 40 * 387552 * 2
def baseEnd_387552 : Nat := 44222323246971763270597

theorem tailTrace_387552 : CollatzResearch.WordTrace tailWord_387552 prefixEnd_387552 44222323246971763270597 := by
  unfold tailWord_387552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067591345986383728582455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9423455127981844971443273 7067591345986383728582455)
  ·
    refine ⟨10601387018979575592873683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7067591345986383728582455 10601387018979575592873683)
    ·
      refine ⟨15902080528469363389310525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10601387018979575592873683 15902080528469363389310525)
      ·
        refine ⟨5963280198176011270991447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15902080528469363389310525 5963280198176011270991447)
        ·
          refine ⟨8944920297264016906487171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5963280198176011270991447 8944920297264016906487171)
          ·
            refine ⟨13417380445896025359730757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944920297264016906487171 13417380445896025359730757)
            ·
              refine ⟨2515758833605504754949517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13417380445896025359730757 2515758833605504754949517)
              ·
                refine ⟨943409562602064283106069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2515758833605504754949517 943409562602064283106069)
                ·
                  refine ⟨44222323246971763270597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 943409562602064283106069 44222323246971763270597)
                  ·
                    rfl

theorem cell22_387552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_387552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387552 prefixEnd_387552 := by exact prefixLift 387552
  have htrace : WordTrace (prefixWord ++ tailWord_387552) baseStart_387552 baseEnd_387552 := by
    simpa [prefixWord, tailWord_387552, baseEnd_387552] using wordTrace_append hprefix tailTrace_387552
  have hstable : (prefixWord ++ tailWord_387552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387552).length < 2 ^ (prefixWord ++ tailWord_387552).sum := by decide
  have hdescent : baseEnd_387552 < baseStart_387552 := by decide
  rcases family_descends (prefixWord ++ tailWord_387552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387588 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_387588 : Nat := 118140960795 + 387588 * 2 ^ 59
def prefixEnd_387588 : Nat := 4983230072969 + 3 ^ 40 * 387588 * 2
def baseEnd_387588 : Nat := 132679293276623195911681

theorem tailTrace_387588 : CollatzResearch.WordTrace tailWord_387588 prefixEnd_387588 132679293276623195911681 := by
  unfold tailWord_387588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068247859921172802737709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9424330479894897070316945 7068247859921172802737709)
  ·
    refine ⟨2650592947470439801026641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7068247859921172802737709 2650592947470439801026641)
    ·
      refine ⟨1987944710602829850769981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2650592947470439801026641 1987944710602829850769981)
      ·
        refine ⟨745479266476061194038743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1987944710602829850769981 745479266476061194038743)
        ·
          refine ⟨1118218899714091791058115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745479266476061194038743 1118218899714091791058115)
          ·
            refine ⟨1677328349571137686587173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118218899714091791058115 1677328349571137686587173)
            ·
              refine ⟨314499065544588316235095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1677328349571137686587173 314499065544588316235095)
              ·
                refine ⟨471748598316882474352643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314499065544588316235095 471748598316882474352643)
                ·
                  refine ⟨707622897475323711528965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471748598316882474352643 707622897475323711528965)
                  ·
                    refine ⟨132679293276623195911681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 707622897475323711528965 132679293276623195911681)
                    ·
                      rfl

theorem cell22_387588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_387588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387588 prefixEnd_387588 := by exact prefixLift 387588
  have htrace : WordTrace (prefixWord ++ tailWord_387588) baseStart_387588 baseEnd_387588 := by
    simpa [prefixWord, tailWord_387588, baseEnd_387588] using wordTrace_append hprefix tailTrace_387588
  have hstable : (prefixWord ++ tailWord_387588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387588).length < 2 ^ (prefixWord ++ tailWord_387588).sum := by decide
  have hdescent : baseEnd_387588 < baseStart_387588 := by decide
  rcases family_descends (prefixWord ++ tailWord_387588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387627 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_387627 : Nat := 118140960795 + 387627 * 2 ^ 59
def prefixEnd_387627 : Nat := 4983230072969 + 3 ^ 40 * 387627 * 2
def baseEnd_387627 : Nat := 132692643773640094186561

theorem tailTrace_387627 : CollatzResearch.WordTrace tailWord_387627 prefixEnd_387627 132692643773640094186561 := by
  unfold tailWord_387627
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137918166701055266145135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9425278777800703510763423 14137918166701055266145135)
  ·
    refine ⟨21206877250051582899217703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14137918166701055266145135 21206877250051582899217703)
    ·
      refine ⟨31810315875077374348826555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21206877250051582899217703 31810315875077374348826555)
      ·
        refine ⟨47715473812616061523239833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31810315875077374348826555 47715473812616061523239833)
        ·
          refine ⟨35786605359462046142429875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47715473812616061523239833 35786605359462046142429875)
          ·
            refine ⟨53679908039193069213644813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35786605359462046142429875 53679908039193069213644813)
            ·
              refine ⟨20129965514697400955116805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53679908039193069213644813 20129965514697400955116805)
              ·
                refine ⟨3774368534005762679084401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20129965514697400955116805 3774368534005762679084401)
                ·
                  refine ⟨2830776400504322009313301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3774368534005762679084401 2830776400504322009313301)
                  ·
                    refine ⟨132692643773640094186561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2830776400504322009313301 132692643773640094186561)
                    ·
                      rfl

theorem cell22_387627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_387627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387627 prefixEnd_387627 := by exact prefixLift 387627
  have htrace : WordTrace (prefixWord ++ tailWord_387627) baseStart_387627 baseEnd_387627 := by
    simpa [prefixWord, tailWord_387627, baseEnd_387627] using wordTrace_append hprefix tailTrace_387627
  have hstable : (prefixWord ++ tailWord_387627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387627).length < 2 ^ (prefixWord ++ tailWord_387627).sum := by decide
  have hdescent : baseEnd_387627 < baseStart_387627 := by decide
  rcases family_descends (prefixWord ++ tailWord_387627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387719 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_387719 : Nat := 118140960795 + 387719 * 2 ^ 59
def prefixEnd_387719 : Nat := 4983230072969 + 3 ^ 40 * 387719 * 2
def baseEnd_387719 : Nat := 132724137253782520886279

theorem tailTrace_387719 : CollatzResearch.WordTrace tailWord_387719 prefixEnd_387719 132724137253782520886279 := by
  unfold tailWord_387719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141273682367754978494211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9427515788245169985662807 14141273682367754978494211)
  ·
    refine ⟨21211910523551632467741317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14141273682367754978494211 21211910523551632467741317)
    ·
      refine ⟨3977233223165931087701497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21211910523551632467741317 3977233223165931087701497)
      ·
        refine ⟨2982924917374448315776123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3977233223165931087701497 2982924917374448315776123)
        ·
          refine ⟨4474387376061672473664185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982924917374448315776123 4474387376061672473664185)
          ·
            refine ⟨3355790532046254355248139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474387376061672473664185 3355790532046254355248139)
            ·
              refine ⟨5033685798069381532872209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355790532046254355248139 5033685798069381532872209)
              ·
                refine ⟨3775264348552036149654157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5033685798069381532872209 3775264348552036149654157)
                ·
                  refine ⟨1415724130707013556120309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3775264348552036149654157 1415724130707013556120309)
                  ·
                    refine ⟨132724137253782520886279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1415724130707013556120309 132724137253782520886279)
                    ·
                      rfl

theorem cell22_387719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_387719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387719 prefixEnd_387719 := by exact prefixLift 387719
  have htrace : WordTrace (prefixWord ++ tailWord_387719) baseStart_387719 baseEnd_387719 := by
    simpa [prefixWord, tailWord_387719, baseEnd_387719] using wordTrace_append hprefix tailTrace_387719
  have hstable : (prefixWord ++ tailWord_387719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387719).length < 2 ^ (prefixWord ++ tailWord_387719).sum := by decide
  have hdescent : baseEnd_387719 < baseStart_387719 := by decide
  rcases family_descends (prefixWord ++ tailWord_387719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387736 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_387736 : Nat := 118140960795 + 387736 * 2 ^ 59
def prefixEnd_387736 : Nat := 4983230072969 + 3 ^ 40 * 387736 * 2
def baseEnd_387736 : Nat := 132729956701200143211227

theorem tailTrace_387736 : CollatzResearch.WordTrace tailWord_387736 prefixEnd_387736 132729956701200143211227 := by
  unfold tailWord_387736
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070946861653083440931531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9427929148870777921242041 7070946861653083440931531)
  ·
    refine ⟨10606420292479625161397297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070946861653083440931531 10606420292479625161397297)
    ·
      refine ⟨7954815219359718871047973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10606420292479625161397297 7954815219359718871047973)
      ·
        refine ⟨1491527853629947288321495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7954815219359718871047973 1491527853629947288321495)
        ·
          refine ⟨2237291780444920932482243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491527853629947288321495 2237291780444920932482243)
          ·
            refine ⟨3355937670667381398723365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237291780444920932482243 3355937670667381398723365)
            ·
              refine ⟨629238313250134012260631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3355937670667381398723365 629238313250134012260631)
              ·
                refine ⟨943857469875201018390947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629238313250134012260631 943857469875201018390947)
                ·
                  refine ⟨1415786204812801527586421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943857469875201018390947 1415786204812801527586421)
                  ·
                    refine ⟨132729956701200143211227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1415786204812801527586421 132729956701200143211227)
                    ·
                      rfl

theorem cell22_387736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_387736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387736 prefixEnd_387736 := by exact prefixLift 387736
  have htrace : WordTrace (prefixWord ++ tailWord_387736) baseStart_387736 baseEnd_387736 := by
    simpa [prefixWord, tailWord_387736, baseEnd_387736] using wordTrace_append hprefix tailTrace_387736
  have hstable : (prefixWord ++ tailWord_387736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387736).length < 2 ^ (prefixWord ++ tailWord_387736).sum := by decide
  have hdescent : baseEnd_387736 < baseStart_387736 := by decide
  rcases family_descends (prefixWord ++ tailWord_387736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387738 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_387738 : Nat := 118140960795 + 387738 * 2 ^ 59
def prefixEnd_387738 : Nat := 4983230072969 + 3 ^ 40 * 387738 * 2
def baseEnd_387738 : Nat := 44243547114024268220407

theorem tailTrace_387738 : CollatzResearch.WordTrace tailWord_387738 prefixEnd_387738 44243547114024268220407 := by
  unfold tailWord_387738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535491667324730305858967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9427977779532614148957245 3535491667324730305858967)
  ·
    refine ⟨5303237500987095458788451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535491667324730305858967 5303237500987095458788451)
    ·
      refine ⟨7954856251480643188182677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5303237500987095458788451 7954856251480643188182677)
      ·
        refine ⟨372883886788155149446063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7954856251480643188182677 372883886788155149446063)
        ·
          refine ⟨559325830182232724169095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372883886788155149446063 559325830182232724169095)
          ·
            refine ⟨838988745273349086253643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559325830182232724169095 838988745273349086253643)
            ·
              refine ⟨1258483117910023629380465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838988745273349086253643 1258483117910023629380465)
              ·
                refine ⟨943862338432517722035349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258483117910023629380465 943862338432517722035349)
                ·
                  refine ⟨44243547114024268220407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 943862338432517722035349 44243547114024268220407)
                  ·
                    rfl

theorem cell22_387738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_387738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387738 prefixEnd_387738 := by exact prefixLift 387738
  have htrace : WordTrace (prefixWord ++ tailWord_387738) baseStart_387738 baseEnd_387738 := by
    simpa [prefixWord, tailWord_387738, baseEnd_387738] using wordTrace_append hprefix tailTrace_387738
  have hstable : (prefixWord ++ tailWord_387738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387738).length < 2 ^ (prefixWord ++ tailWord_387738).sum := by decide
  have hdescent : baseEnd_387738 < baseStart_387738 := by decide
  rcases family_descends (prefixWord ++ tailWord_387738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387811 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 7]
def baseStart_387811 : Nat := 118140960795 + 387811 * 2 ^ 59
def prefixEnd_387811 : Nat := 4983230072969 + 3 ^ 40 * 387811 * 2
def baseEnd_387811 : Nat := 44251876911308315861999

theorem tailTrace_387811 : CollatzResearch.WordTrace tailWord_387811 prefixEnd_387811 44251876911308315861999 := by
  unfold tailWord_387811
  simp only [CollatzResearch.WordTrace]
  refine ⟨14144629198034454690843287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9429752798689636460562191 14144629198034454690843287)
  ·
    refine ⟨21216943797051682036264931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14144629198034454690843287 21216943797051682036264931)
    ·
      refine ⟨31825415695577523054397397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21216943797051682036264931 31825415695577523054397397)
      ·
        refine ⟨745908180365098196587439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31825415695577523054397397 745908180365098196587439)
        ·
          refine ⟨1118862270547647294881159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745908180365098196587439 1118862270547647294881159)
          ·
            refine ⟨1678293405821470942321739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118862270547647294881159 1678293405821470942321739)
            ·
              refine ⟨2517440108732206413482609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678293405821470942321739 2517440108732206413482609)
              ·
                refine ⟨1888080081549154810111957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517440108732206413482609 1888080081549154810111957)
                ·
                  refine ⟨44251876911308315861999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1888080081549154810111957 44251876911308315861999)
                  ·
                    rfl

theorem cell22_387811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 7].length) (baseStart_387811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387811 prefixEnd_387811 := by exact prefixLift 387811
  have htrace : WordTrace (prefixWord ++ tailWord_387811) baseStart_387811 baseEnd_387811 := by
    simpa [prefixWord, tailWord_387811, baseEnd_387811] using wordTrace_append hprefix tailTrace_387811
  have hstable : (prefixWord ++ tailWord_387811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387811).length < 2 ^ (prefixWord ++ tailWord_387811).sum := by decide
  have hdescent : baseEnd_387811 < baseStart_387811 := by decide
  rcases family_descends (prefixWord ++ tailWord_387811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387841 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_387841 : Nat := 118140960795 + 387841 * 2 ^ 59
def prefixEnd_387841 : Nat := 4983230072969 + 3 ^ 40 * 387841 * 2
def baseEnd_387841 : Nat := 132765900347014869335905

theorem tailTrace_387841 : CollatzResearch.WordTrace tailWord_387841 prefixEnd_387841 132765900347014869335905 := by
  unfold tailWord_387841
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145723387925769814435377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9430482258617179876290251 14145723387925769814435377)
  ·
    refine ⟨10609292540944327360826533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14145723387925769814435377 10609292540944327360826533)
    ·
      refine ⟨1989242351427061380154975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10609292540944327360826533 1989242351427061380154975)
      ·
        refine ⟨2983863527140592070232463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989242351427061380154975 2983863527140592070232463)
        ·
          refine ⟨4475795290710888105348695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983863527140592070232463 4475795290710888105348695)
          ·
            refine ⟨6713692936066332158023043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475795290710888105348695 6713692936066332158023043)
            ·
              refine ⟨10070539404099498237034565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713692936066332158023043 10070539404099498237034565)
              ·
                refine ⟨1888226138268655919443981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10070539404099498237034565 1888226138268655919443981)
                ·
                  refine ⟨708084801850745969791493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1888226138268655919443981 708084801850745969791493)
                  ·
                    refine ⟨132765900347014869335905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 708084801850745969791493 132765900347014869335905)
                    ·
                      rfl

theorem cell22_387841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_387841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387841 prefixEnd_387841 := by exact prefixLift 387841
  have htrace : WordTrace (prefixWord ++ tailWord_387841) baseStart_387841 baseEnd_387841 := by
    simpa [prefixWord, tailWord_387841, baseEnd_387841] using wordTrace_append hprefix tailTrace_387841
  have hstable : (prefixWord ++ tailWord_387841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387841).length < 2 ^ (prefixWord ++ tailWord_387841).sum := by decide
  have hdescent : baseEnd_387841 < baseStart_387841 := by decide
  rcases family_descends (prefixWord ++ tailWord_387841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387871 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_387871 : Nat := 118140960795 + 387871 * 2 ^ 59
def prefixEnd_387871 : Nat := 4983230072969 + 3 ^ 40 * 387871 * 2
def baseEnd_387871 : Nat := 132776169960104791085813

theorem tailTrace_387871 : CollatzResearch.WordTrace tailWord_387871 prefixEnd_387871 132776169960104791085813 := by
  unfold tailWord_387871
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146817577817084938027467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9431211718544723292018311 14146817577817084938027467)
  ·
    refine ⟨21220226366725627407041201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14146817577817084938027467 21220226366725627407041201)
    ·
      refine ⟨15915169775044220555280901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21220226366725627407041201 15915169775044220555280901)
      ·
        refine ⟨2984094332820791354115169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15915169775044220555280901 2984094332820791354115169)
        ·
          refine ⟨2238070749615593515586377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984094332820791354115169 2238070749615593515586377)
          ·
            refine ⟨1678553062211695136689783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2238070749615593515586377 1678553062211695136689783)
            ·
              refine ⟨2517829593317542705034675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678553062211695136689783 2517829593317542705034675)
              ·
                refine ⟨3776744389976314057552013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517829593317542705034675 3776744389976314057552013)
                ·
                  refine ⟨1416279146241117771582005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3776744389976314057552013 1416279146241117771582005)
                  ·
                    refine ⟨132776169960104791085813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1416279146241117771582005 132776169960104791085813)
                    ·
                      rfl

theorem cell22_387871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_387871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387871 prefixEnd_387871 := by exact prefixLift 387871
  have htrace : WordTrace (prefixWord ++ tailWord_387871) baseStart_387871 baseEnd_387871 := by
    simpa [prefixWord, tailWord_387871, baseEnd_387871] using wordTrace_append hprefix tailTrace_387871
  have hstable : (prefixWord ++ tailWord_387871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387871).length < 2 ^ (prefixWord ++ tailWord_387871).sum := by decide
  have hdescent : baseEnd_387871 < baseStart_387871 := by decide
  rcases family_descends (prefixWord ++ tailWord_387871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387873 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 4]
def baseStart_387873 : Nat := 118140960795 + 387873 * 2 ^ 59
def prefixEnd_387873 : Nat := 4983230072969 + 3 ^ 40 * 387873 * 2
def baseEnd_387873 : Nat := 44258951533659150845269

theorem tailTrace_387873 : CollatzResearch.WordTrace tailWord_387873 prefixEnd_387873 44258951533659150845269 := by
  unfold tailWord_387873
  simp only [CollatzResearch.WordTrace]
  refine ⟨14146890523809839279600273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9431260349206559519733515 14146890523809839279600273)
  ·
    refine ⟨10610167892857379459700205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14146890523809839279600273 10610167892857379459700205)
    ·
      refine ⟨3978812959821517297387577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10610167892857379459700205 3978812959821517297387577)
      ·
        refine ⟨2984109719866137973040683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3978812959821517297387577 2984109719866137973040683)
        ·
          refine ⟨4476164579799206959561025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984109719866137973040683 4476164579799206959561025)
          ·
            refine ⟨3357123434849405219670769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476164579799206959561025 3357123434849405219670769)
            ·
              refine ⟨2517842576137053914753077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357123434849405219670769 2517842576137053914753077)
              ·
                refine ⟨236047741512848804508101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2517842576137053914753077 236047741512848804508101)
                ·
                  refine ⟨44258951533659150845269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236047741512848804508101 44258951533659150845269)
                  ·
                    rfl

theorem cell22_387873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_387873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_387873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_387873 prefixEnd_387873 := by exact prefixLift 387873
  have htrace : WordTrace (prefixWord ++ tailWord_387873) baseStart_387873 baseEnd_387873 := by
    simpa [prefixWord, tailWord_387873, baseEnd_387873] using wordTrace_append hprefix tailTrace_387873
  have hstable : (prefixWord ++ tailWord_387873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387873).length < 2 ^ (prefixWord ++ tailWord_387873).sum := by decide
  have hdescent : baseEnd_387873 < baseStart_387873 := by decide
  rcases family_descends (prefixWord ++ tailWord_387873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388040 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_388040 : Nat := 118140960795 + 388040 * 2 ^ 59
def prefixEnd_388040 : Nat := 4983230072969 + 3 ^ 40 * 388040 * 2
def baseEnd_388040 : Nat := 132834022113844683610295

theorem tailTrace_388040 : CollatzResearch.WordTrace tailWord_388040 prefixEnd_388040 132834022113844683610295 := by
  unfold tailWord_388040
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076490757102413400464787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9435321009469884533953049 7076490757102413400464787)
  ·
    refine ⟨10614736135653620100697181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076490757102413400464787 10614736135653620100697181)
    ·
      refine ⟨3980526050870107537761443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10614736135653620100697181 3980526050870107537761443)
      ·
        refine ⟨5970789076305161306642165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980526050870107537761443 5970789076305161306642165)
        ·
          refine ⟨559761475903608872497703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5970789076305161306642165 559761475903608872497703)
          ·
            refine ⟨839642213855413308746555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559761475903608872497703 839642213855413308746555)
            ·
              refine ⟨1259463320783119963119833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839642213855413308746555 1259463320783119963119833)
              ·
                refine ⟨944597490587339972339875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259463320783119963119833 944597490587339972339875)
                ·
                  refine ⟨1416896235881009958509813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944597490587339972339875 1416896235881009958509813)
                  ·
                    refine ⟨132834022113844683610295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1416896235881009958509813 132834022113844683610295)
                    ·
                      rfl

theorem cell22_388040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_388040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388040 prefixEnd_388040 := by exact prefixLift 388040
  have htrace : WordTrace (prefixWord ++ tailWord_388040) baseStart_388040 baseEnd_388040 := by
    simpa [prefixWord, tailWord_388040, baseEnd_388040] using wordTrace_append hprefix tailTrace_388040
  have hstable : (prefixWord ++ tailWord_388040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388040).length < 2 ^ (prefixWord ++ tailWord_388040).sum := by decide
  have hdescent : baseEnd_388040 < baseStart_388040 := by decide
  rcases family_descends (prefixWord ++ tailWord_388040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388053 : List Nat := [1, 3, 2, 3, 3, 10]
def baseStart_388053 : Nat := 118140960795 + 388053 * 2 ^ 59
def prefixEnd_388053 : Nat := 4983230072969 + 3 ^ 40 * 388053 * 2
def baseEnd_388053 : Nat := 1639981139253296086855

theorem tailTrace_388053 : CollatzResearch.WordTrace tailWord_388053 prefixEnd_388053 1639981139253296086855 := by
  unfold tailWord_388053
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153455663157730021152813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9435637108771820014101875 14153455663157730021152813)
  ·
    refine ⟨5307545873684148757932305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14153455663157730021152813 5307545873684148757932305)
    ·
      refine ⟨3980659405263111568449229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5307545873684148757932305 3980659405263111568449229)
      ·
        refine ⟨1492747276973666838168461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3980659405263111568449229 1492747276973666838168461)
        ·
          refine ⟨559780228865125064313173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1492747276973666838168461 559780228865125064313173)
          ·
            refine ⟨1639981139253296086855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 559780228865125064313173 1639981139253296086855)
            ·
              rfl

theorem cell22_388053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 10].length) (baseStart_388053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388053 prefixEnd_388053 := by exact prefixLift 388053
  have htrace : WordTrace (prefixWord ++ tailWord_388053) baseStart_388053 baseEnd_388053 := by
    simpa [prefixWord, tailWord_388053, baseEnd_388053] using wordTrace_append hprefix tailTrace_388053
  have hstable : (prefixWord ++ tailWord_388053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388053).length < 2 ^ (prefixWord ++ tailWord_388053).sum := by decide
  have hdescent : baseEnd_388053 < baseStart_388053 := by decide
  rcases family_descends (prefixWord ++ tailWord_388053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388057 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_388057 : Nat := 118140960795 + 388057 * 2 ^ 59
def prefixEnd_388057 : Nat := 4983230072969 + 3 ^ 40 * 388057 * 2
def baseEnd_388057 : Nat := 132839841561262305935243

theorem tailTrace_388057 : CollatzResearch.WordTrace tailWord_388057 prefixEnd_388057 132839841561262305935243 := by
  unfold tailWord_388057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153601555143238704298425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9435734370095492469532283 14153601555143238704298425)
  ·
    refine ⟨10615201166357429028223819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14153601555143238704298425 10615201166357429028223819)
    ·
      refine ⟨15922801749536143542335729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10615201166357429028223819 15922801749536143542335729)
      ·
        refine ⟨11942101312152107656751797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15922801749536143542335729 11942101312152107656751797)
        ·
          refine ⟨1119571998014260092820481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11942101312152107656751797 1119571998014260092820481)
          ·
            refine ⟨839678998510695069615361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119571998014260092820481 839678998510695069615361)
            ·
              refine ⟨629759248883021302211521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839678998510695069615361 629759248883021302211521)
              ·
                refine ⟨472319436662265976658641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629759248883021302211521 472319436662265976658641)
                ·
                  refine ⟨354239577496699482493981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472319436662265976658641 354239577496699482493981)
                  ·
                    refine ⟨132839841561262305935243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354239577496699482493981 132839841561262305935243)
                    ·
                      rfl

theorem cell22_388057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_388057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388057 prefixEnd_388057 := by exact prefixLift 388057
  have htrace : WordTrace (prefixWord ++ tailWord_388057) baseStart_388057 baseEnd_388057 := by
    simpa [prefixWord, tailWord_388057, baseEnd_388057] using wordTrace_append hprefix tailTrace_388057
  have hstable : (prefixWord ++ tailWord_388057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388057).length < 2 ^ (prefixWord ++ tailWord_388057).sum := by decide
  have hdescent : baseEnd_388057 < baseStart_388057 := by decide
  rcases family_descends (prefixWord ++ tailWord_388057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388119 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 1, 3]
def baseStart_388119 : Nat := 118140960795 + 388119 * 2 ^ 59
def prefixEnd_388119 : Nat := 4983230072969 + 3 ^ 40 * 388119 * 2
def baseEnd_388119 : Nat := 132861065428314810885053

theorem tailTrace_388119 : CollatzResearch.WordTrace tailWord_388119 prefixEnd_388119 132861065428314810885053 := by
  unfold tailWord_388119
  simp only [CollatzResearch.WordTrace]
  refine ⟨14155862880918623293055411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9437241920612415528703607 14155862880918623293055411)
  ·
    refine ⟨21233794321377934939583117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14155862880918623293055411 21233794321377934939583117)
    ·
      refine ⟨7962672870516725602343669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21233794321377934939583117 7962672870516725602343669)
      ·
        refine ⟨746500581610943025219719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7962672870516725602343669 746500581610943025219719)
        ·
          refine ⟨1119750872416414537829579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746500581610943025219719 1119750872416414537829579)
          ·
            refine ⟨1679626308624621806744369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119750872416414537829579 1679626308624621806744369)
            ·
              refine ⟨1259719731468466355058277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679626308624621806744369 1259719731468466355058277)
              ·
                refine ⟨236197449650337441573427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1259719731468466355058277 236197449650337441573427)
                ·
                  refine ⟨354296174475506162360141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236197449650337441573427 354296174475506162360141)
                  ·
                    refine ⟨132861065428314810885053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354296174475506162360141 132861065428314810885053)
                    ·
                      rfl

theorem cell22_388119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_388119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388119 prefixEnd_388119 := by exact prefixLift 388119
  have htrace : WordTrace (prefixWord ++ tailWord_388119) baseStart_388119 baseEnd_388119 := by
    simpa [prefixWord, tailWord_388119, baseEnd_388119] using wordTrace_append hprefix tailTrace_388119
  have hstable : (prefixWord ++ tailWord_388119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388119).length < 2 ^ (prefixWord ++ tailWord_388119).sum := by decide
  have hdescent : baseEnd_388119 < baseStart_388119 := by decide
  rcases family_descends (prefixWord ++ tailWord_388119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388130 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_388130 : Nat := 118140960795 + 388130 * 2 ^ 59
def prefixEnd_388130 : Nat := 4983230072969 + 3 ^ 40 * 388130 * 2
def baseEnd_388130 : Nat := 132864830953114448860019

theorem tailTrace_388130 : CollatzResearch.WordTrace tailWord_388130 prefixEnd_388130 132864830953114448860019 := by
  unfold tailWord_388130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539066020969693042926461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9437509389252514781137229 3539066020969693042926461)
  ·
    refine ⟨1327149757863634891097423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3539066020969693042926461 1327149757863634891097423)
    ·
      refine ⟨1990724636795452336646135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327149757863634891097423 1990724636795452336646135)
      ·
        refine ⟨2986086955193178504969203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990724636795452336646135 2986086955193178504969203)
        ·
          refine ⟨4479130432789767757453805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986086955193178504969203 4479130432789767757453805)
          ·
            refine ⟨1679673912296162909045177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4479130432789767757453805 1679673912296162909045177)
            ·
              refine ⟨1259755434222122181783883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679673912296162909045177 1259755434222122181783883)
              ·
                refine ⟨1889633151333183272675825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259755434222122181783883 1889633151333183272675825)
                ·
                  refine ⟨1417224863499887454506869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889633151333183272675825 1417224863499887454506869)
                  ·
                    refine ⟨132864830953114448860019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1417224863499887454506869 132864830953114448860019)
                    ·
                      rfl

theorem cell22_388130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_388130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388130 prefixEnd_388130 := by exact prefixLift 388130
  have htrace : WordTrace (prefixWord ++ tailWord_388130) baseStart_388130 baseEnd_388130 := by
    simpa [prefixWord, tailWord_388130, baseEnd_388130] using wordTrace_append hprefix tailTrace_388130
  have hstable : (prefixWord ++ tailWord_388130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388130).length < 2 ^ (prefixWord ++ tailWord_388130).sum := by decide
  have hdescent : baseEnd_388130 < baseStart_388130 := by decide
  rcases family_descends (prefixWord ++ tailWord_388130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388192 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_388192 : Nat := 118140960795 + 388192 * 2 ^ 59
def prefixEnd_388192 : Nat := 4983230072969 + 3 ^ 40 * 388192 * 2
def baseEnd_388192 : Nat := 132886054820166953809829

theorem tailTrace_388192 : CollatzResearch.WordTrace tailWord_388192 prefixEnd_388192 132886054820166953809829 := by
  unfold tailWord_388192
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079262704827078380231415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9439016939769437840308553 7079262704827078380231415)
  ·
    refine ⟨10618894057240617570347123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7079262704827078380231415 10618894057240617570347123)
    ·
      refine ⟨15928341085860926355520685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10618894057240617570347123 15928341085860926355520685)
      ·
        refine ⟨5973127907197847383320257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15928341085860926355520685 5973127907197847383320257)
        ·
          refine ⟨4479845930398385537490193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5973127907197847383320257 4479845930398385537490193)
          ·
            refine ⟨3359884447798789153117645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4479845930398385537490193 3359884447798789153117645)
            ·
              refine ⟨1259956667924545932419117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3359884447798789153117645 1259956667924545932419117)
              ·
                refine ⟨472483750471704724657169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1259956667924545932419117 472483750471704724657169)
                ·
                  refine ⟨354362812853778543492877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472483750471704724657169 354362812853778543492877)
                  ·
                    refine ⟨132886054820166953809829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354362812853778543492877 132886054820166953809829)
                    ·
                      rfl

theorem cell22_388192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_388192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388192 prefixEnd_388192 := by exact prefixLift 388192
  have htrace : WordTrace (prefixWord ++ tailWord_388192) baseStart_388192 baseEnd_388192 := by
    simpa [prefixWord, tailWord_388192, baseEnd_388192] using wordTrace_append hprefix tailTrace_388192
  have hstable : (prefixWord ++ tailWord_388192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388192).length < 2 ^ (prefixWord ++ tailWord_388192).sum := by decide
  have hdescent : baseEnd_388192 < baseStart_388192 := by decide
  rcases family_descends (prefixWord ++ tailWord_388192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388205 : List Nat := [1, 5, 1, 1, 2, 2, 2, 8]
def baseStart_388205 : Nat := 118140960795 + 388205 * 2 ^ 59
def prefixEnd_388205 : Nat := 4983230072969 + 3 ^ 40 * 388205 * 2
def baseEnd_388205 : Nat := 14765611665093250359421

theorem tailTrace_388205 : CollatzResearch.WordTrace tailWord_388205 prefixEnd_388205 14765611665093250359421 := by
  unfold tailWord_388205
  simp only [CollatzResearch.WordTrace]
  refine ⟨14158999558607059980686069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9439333039071373320457379 14158999558607059980686069)
  ·
    refine ⟨1327406208619411873189319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14158999558607059980686069 1327406208619411873189319)
    ·
      refine ⟨1991109312929117809783979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327406208619411873189319 1991109312929117809783979)
      ·
        refine ⟨2986663969393676714675969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991109312929117809783979 2986663969393676714675969)
        ·
          refine ⟨2239997977045257536006977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2986663969393676714675969 2239997977045257536006977)
          ·
            refine ⟨1679998482783943152005233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239997977045257536006977 1679998482783943152005233)
            ·
              refine ⟨1259998862087957364003925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679998482783943152005233 1259998862087957364003925)
              ·
                refine ⟨14765611665093250359421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1259998862087957364003925 14765611665093250359421)
                ·
                  rfl

theorem cell22_388205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 8].length) (baseStart_388205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388205 prefixEnd_388205 := by exact prefixLift 388205
  have htrace : WordTrace (prefixWord ++ tailWord_388205) baseStart_388205 baseEnd_388205 := by
    simpa [prefixWord, tailWord_388205, baseEnd_388205] using wordTrace_append hprefix tailTrace_388205
  have hstable : (prefixWord ++ tailWord_388205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388205).length < 2 ^ (prefixWord ++ tailWord_388205).sum := by decide
  have hdescent : baseEnd_388205 < baseStart_388205 := by decide
  rcases family_descends (prefixWord ++ tailWord_388205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388254 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_388254 : Nat := 118140960795 + 388254 * 2 ^ 59
def prefixEnd_388254 : Nat := 4983230072969 + 3 ^ 40 * 388254 * 2
def baseEnd_388254 : Nat := 132907278687219458759639

theorem tailTrace_388254 : CollatzResearch.WordTrace tailWord_388254 prefixEnd_388254 132907278687219458759639 := by
  unfold tailWord_388254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770098341928692668652477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9440524490286360899479877 1770098341928692668652477)
  ·
    refine ⟨663786878223259750744679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1770098341928692668652477 663786878223259750744679)
    ·
      refine ⟨995680317334889626117019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663786878223259750744679 995680317334889626117019)
      ·
        refine ⟨1493520476002334439175529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995680317334889626117019 1493520476002334439175529)
        ·
          refine ⟨1120140357001750829381647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493520476002334439175529 1120140357001750829381647)
          ·
            refine ⟨1680210535502626244072471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120140357001750829381647 1680210535502626244072471)
            ·
              refine ⟨2520315803253939366108707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680210535502626244072471 2520315803253939366108707)
              ·
                refine ⟨3780473704880909049163061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520315803253939366108707 3780473704880909049163061)
                ·
                  refine ⟨354419409832585223359037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3780473704880909049163061 354419409832585223359037)
                  ·
                    refine ⟨132907278687219458759639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354419409832585223359037 132907278687219458759639)
                    ·
                      rfl

theorem cell22_388254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_388254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388254 prefixEnd_388254 := by exact prefixLift 388254
  have htrace : WordTrace (prefixWord ++ tailWord_388254) baseStart_388254 baseEnd_388254 := by
    simpa [prefixWord, tailWord_388254, baseEnd_388254] using wordTrace_append hprefix tailTrace_388254
  have hstable : (prefixWord ++ tailWord_388254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388254).length < 2 ^ (prefixWord ++ tailWord_388254).sum := by decide
  have hdescent : baseEnd_388254 < baseStart_388254 := by decide
  rcases family_descends (prefixWord ++ tailWord_388254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388280 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_388280 : Nat := 118140960795 + 388280 * 2 ^ 59
def prefixEnd_388280 : Nat := 4983230072969 + 3 ^ 40 * 388280 * 2
def baseEnd_388280 : Nat := 132916179018564057609559

theorem tailTrace_388280 : CollatzResearch.WordTrace tailWord_388280 prefixEnd_388280 132916179018564057609559 := by
  unfold tailWord_388280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080867516667673894833147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9441156688890231859777529 7080867516667673894833147)
  ·
    refine ⟨10621301275001510842249721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7080867516667673894833147 10621301275001510842249721)
    ·
      refine ⟨7965975956251133131687291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10621301275001510842249721 7965975956251133131687291)
      ·
        refine ⟨11948963934376699697530937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965975956251133131687291 11948963934376699697530937)
        ·
          refine ⟨8961722950782524773148203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11948963934376699697530937 8961722950782524773148203)
          ·
            refine ⟨13442584426173787159722305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961722950782524773148203 13442584426173787159722305)
            ·
              refine ⟨10081938319630340369791729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13442584426173787159722305 10081938319630340369791729)
              ·
                refine ⟨7561453739722755277343797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10081938319630340369791729 7561453739722755277343797)
                ·
                  refine ⟨708886288099008307250981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7561453739722755277343797 708886288099008307250981)
                  ·
                    refine ⟨132916179018564057609559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 708886288099008307250981 132916179018564057609559)
                    ·
                      rfl

theorem cell22_388280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_388280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388280 prefixEnd_388280 := by exact prefixLift 388280
  have htrace : WordTrace (prefixWord ++ tailWord_388280) baseStart_388280 baseEnd_388280 := by
    simpa [prefixWord, tailWord_388280, baseEnd_388280] using wordTrace_append hprefix tailTrace_388280
  have hstable : (prefixWord ++ tailWord_388280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388280).length < 2 ^ (prefixWord ++ tailWord_388280).sum := by decide
  have hdescent : baseEnd_388280 < baseStart_388280 := by decide
  rcases family_descends (prefixWord ++ tailWord_388280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388284 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 5]
def baseStart_388284 : Nat := 118140960795 + 388284 * 2 ^ 59
def prefixEnd_388284 : Nat := 4983230072969 + 3 ^ 40 * 388284 * 2
def baseEnd_388284 : Nat := 44305849433436460169849

theorem tailTrace_388284 : CollatzResearch.WordTrace tailWord_388284 prefixEnd_388284 44305849433436460169849 := by
  unfold tailWord_388284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080940462660428236405953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9441253950213904315207937 7080940462660428236405953)
  ·
    refine ⟨5310705346995321177304465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7080940462660428236405953 5310705346995321177304465)
    ·
      refine ⟨3983029010246490882978349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5310705346995321177304465 3983029010246490882978349)
      ·
        refine ⟨1493635878842434081116881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3983029010246490882978349 1493635878842434081116881)
        ·
          refine ⟨1120226909131825560837661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493635878842434081116881 1120226909131825560837661)
          ·
            refine ⟨420085090924434585314123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1120226909131825560837661 420085090924434585314123)
            ·
              refine ⟨630127636386651877971185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420085090924434585314123 630127636386651877971185)
              ·
                refine ⟨472595727289988908478389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630127636386651877971185 472595727289988908478389)
                ·
                  refine ⟨44305849433436460169849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 472595727289988908478389 44305849433436460169849)
                  ·
                    rfl

theorem cell22_388284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_388284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388284 prefixEnd_388284 := by exact prefixLift 388284
  have htrace : WordTrace (prefixWord ++ tailWord_388284) baseStart_388284 baseEnd_388284 := by
    simpa [prefixWord, tailWord_388284, baseEnd_388284] using wordTrace_append hprefix tailTrace_388284
  have hstable : (prefixWord ++ tailWord_388284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388284).length < 2 ^ (prefixWord ++ tailWord_388284).sum := by decide
  have hdescent : baseEnd_388284 < baseStart_388284 := by decide
  rcases family_descends (prefixWord ++ tailWord_388284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388432 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_388432 : Nat := 118140960795 + 388432 * 2 ^ 59
def prefixEnd_388432 : Nat := 4983230072969 + 3 ^ 40 * 388432 * 2
def baseEnd_388432 : Nat := 132968211724886327809093

theorem tailTrace_388432 : CollatzResearch.WordTrace tailWord_388432 prefixEnd_388432 132968211724886327809093 := by
  unfold tailWord_388432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083639464392338874599775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9444852619189785166133033 7083639464392338874599775)
  ·
    refine ⟨10625459196588508311899663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7083639464392338874599775 10625459196588508311899663)
    ·
      refine ⟨15938188794882762467849495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10625459196588508311899663 15938188794882762467849495)
      ·
        refine ⟨23907283192324143701774243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15938188794882762467849495 23907283192324143701774243)
        ·
          refine ⟨35860924788486215552661365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23907283192324143701774243 35860924788486215552661365)
          ·
            refine ⟨3361961698920582708062003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35860924788486215552661365 3361961698920582708062003)
            ·
              refine ⟨5042942548380874062093005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361961698920582708062003 5042942548380874062093005)
              ·
                refine ⟨1891103455642827773284877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5042942548380874062093005 1891103455642827773284877)
                ·
                  refine ⟨709163795866060414981829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1891103455642827773284877 709163795866060414981829)
                  ·
                    refine ⟨132968211724886327809093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709163795866060414981829 132968211724886327809093)
                    ·
                      rfl

theorem cell22_388432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_388432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388432 prefixEnd_388432 := by exact prefixLift 388432
  have htrace : WordTrace (prefixWord ++ tailWord_388432) baseStart_388432 baseEnd_388432 := by
    simpa [prefixWord, tailWord_388432, baseEnd_388432] using wordTrace_append hprefix tailTrace_388432
  have hstable : (prefixWord ++ tailWord_388432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388432).length < 2 ^ (prefixWord ++ tailWord_388432).sum := by decide
  have hdescent : baseEnd_388432 < baseStart_388432 := by decide
  rcases family_descends (prefixWord ++ tailWord_388432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388464 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 4]
def baseStart_388464 : Nat := 118140960795 + 388464 * 2 ^ 59
def prefixEnd_388464 : Nat := 4983230072969 + 3 ^ 40 * 388464 * 2
def baseEnd_388464 : Nat := 44326388659616303669665

theorem tailTrace_388464 : CollatzResearch.WordTrace tailWord_388464 prefixEnd_388464 44326388659616303669665 := by
  unfold tailWord_388464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084223032334373607182223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9445630709779164809576297 7084223032334373607182223)
  ·
    refine ⟨10626334548501560410773335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7084223032334373607182223 10626334548501560410773335)
    ·
      refine ⟨15939501822752340616160003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10626334548501560410773335 15939501822752340616160003)
      ·
        refine ⟨23909252734128510924240005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15939501822752340616160003 23909252734128510924240005)
        ·
          refine ⟨4482984887649095798295001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23909252734128510924240005 4482984887649095798295001)
          ·
            refine ⟨3362238665736821848721251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4482984887649095798295001 3362238665736821848721251)
            ·
              refine ⟨5043357998605232773081877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362238665736821848721251 5043357998605232773081877)
              ·
                refine ⟨236407406184620286238213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5043357998605232773081877 236407406184620286238213)
                ·
                  refine ⟨44326388659616303669665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236407406184620286238213 44326388659616303669665)
                  ·
                    rfl

theorem cell22_388464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_388464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388464 prefixEnd_388464 := by exact prefixLift 388464
  have htrace : WordTrace (prefixWord ++ tailWord_388464) baseStart_388464 baseEnd_388464 := by
    simpa [prefixWord, tailWord_388464, baseEnd_388464] using wordTrace_append hprefix tailTrace_388464
  have hstable : (prefixWord ++ tailWord_388464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388464).length < 2 ^ (prefixWord ++ tailWord_388464).sum := by decide
  have hdescent : baseEnd_388464 < baseStart_388464 := by decide
  rcases family_descends (prefixWord ++ tailWord_388464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388477 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_388477 : Nat := 118140960795 + 388477 * 2 ^ 59
def prefixEnd_388477 : Nat := 4983230072969 + 3 ^ 40 * 388477 * 2
def baseEnd_388477 : Nat := 132983616144521210433955

theorem tailTrace_388477 : CollatzResearch.WordTrace tailWord_388477 prefixEnd_388477 132983616144521210433955 := by
  unfold tailWord_388477
  simp only [CollatzResearch.WordTrace]
  refine ⟨14168920213621650434587685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9445946809081100289725123 14168920213621650434587685)
  ·
    refine ⟨2656672540054059456485191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14168920213621650434587685 2656672540054059456485191)
    ·
      refine ⟨3985008810081089184727787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656672540054059456485191 3985008810081089184727787)
      ·
        refine ⟨5977513215121633777091681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3985008810081089184727787 5977513215121633777091681)
        ·
          refine ⟨4483134911341225332818761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5977513215121633777091681 4483134911341225332818761)
          ·
            refine ⟨3362351183505918999614071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483134911341225332818761 3362351183505918999614071)
            ·
              refine ⟨5043526775258878499421107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362351183505918999614071 5043526775258878499421107)
              ·
                refine ⟨7565290162888317749131661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043526775258878499421107 7565290162888317749131661)
                ·
                  refine ⟨2836983811083119155924373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7565290162888317749131661 2836983811083119155924373)
                  ·
                    refine ⟨132983616144521210433955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2836983811083119155924373 132983616144521210433955)
                    ·
                      rfl

theorem cell22_388477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_388477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388477 prefixEnd_388477 := by exact prefixLift 388477
  have htrace : WordTrace (prefixWord ++ tailWord_388477) baseStart_388477 baseEnd_388477 := by
    simpa [prefixWord, tailWord_388477, baseEnd_388477] using wordTrace_append hprefix tailTrace_388477
  have hstable : (prefixWord ++ tailWord_388477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388477).length < 2 ^ (prefixWord ++ tailWord_388477).sum := by decide
  have hdescent : baseEnd_388477 < baseStart_388477 := by decide
  rcases family_descends (prefixWord ++ tailWord_388477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388492 : List Nat := [2, 2, 1, 2, 1, 3, 3, 8]
def baseStart_388492 : Nat := 118140960795 + 388492 * 2 ^ 59
def prefixEnd_388492 : Nat := 4983230072969 + 3 ^ 40 * 388492 * 2
def baseEnd_388492 : Nat := 14776527883451796812101

theorem tailTrace_388492 : CollatzResearch.WordTrace tailWord_388492 prefixEnd_388492 14776527883451796812101 := by
  unfold tailWord_388492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084733654283653998191865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9446311539044871997589153 7084733654283653998191865)
  ·
    refine ⟨5313550240712740498643899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7084733654283653998191865 5313550240712740498643899)
    ·
      refine ⟨7970325361069110747965849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5313550240712740498643899 7970325361069110747965849)
      ·
        refine ⟨5977744020801833060974387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7970325361069110747965849 5977744020801833060974387)
        ·
          refine ⟨8966616031202749591461581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977744020801833060974387 8966616031202749591461581)
          ·
            refine ⟨3362481011701031096798093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8966616031202749591461581 3362481011701031096798093)
            ·
              refine ⟨1260930379387886661299285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3362481011701031096798093 1260930379387886661299285)
              ·
                refine ⟨14776527883451796812101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1260930379387886661299285 14776527883451796812101)
                ·
                  rfl

theorem cell22_388492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_388492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388492 prefixEnd_388492 := by exact prefixLift 388492
  have htrace : WordTrace (prefixWord ++ tailWord_388492) baseStart_388492 baseEnd_388492 := by
    simpa [prefixWord, tailWord_388492, baseEnd_388492] using wordTrace_append hprefix tailTrace_388492
  have hstable : (prefixWord ++ tailWord_388492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388492).length < 2 ^ (prefixWord ++ tailWord_388492).sum := by decide
  have hdescent : baseEnd_388492 < baseStart_388492 := by decide
  rcases family_descends (prefixWord ++ tailWord_388492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388509 : List Nat := [1, 4, 2, 1, 3, 3, 8]
def baseStart_388509 : Nat := 118140960795 + 388509 * 2 ^ 59
def prefixEnd_388509 : Nat := 4983230072969 + 3 ^ 40 * 388509 * 2
def baseEnd_388509 : Nat := 4925724829573473838291

theorem tailTrace_388509 : CollatzResearch.WordTrace tailWord_388509 prefixEnd_388509 4925724829573473838291 := by
  unfold tailWord_388509
  simp only [CollatzResearch.WordTrace]
  refine ⟨14170087349505719899752581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9446724899670479933168387 14170087349505719899752581)
  ·
    refine ⟨2656891378032322481203609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14170087349505719899752581 2656891378032322481203609)
    ·
      refine ⟨1992668533524241860902707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2656891378032322481203609 1992668533524241860902707)
      ·
        refine ⟨2989002800286362791354061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992668533524241860902707 2989002800286362791354061)
        ·
          refine ⟨1120876050107386046757773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2989002800286362791354061 1120876050107386046757773)
          ·
            refine ⟨420328518790269767534165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1120876050107386046757773 420328518790269767534165)
            ·
              refine ⟨4925724829573473838291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 420328518790269767534165 4925724829573473838291)
              ·
                rfl

theorem cell22_388509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 8].length) (baseStart_388509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388509 prefixEnd_388509 := by exact prefixLift 388509
  have htrace : WordTrace (prefixWord ++ tailWord_388509) baseStart_388509 baseEnd_388509 := by
    simpa [prefixWord, tailWord_388509, baseEnd_388509] using wordTrace_append hprefix tailTrace_388509
  have hstable : (prefixWord ++ tailWord_388509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388509).length < 2 ^ (prefixWord ++ tailWord_388509).sum := by decide
  have hdescent : baseEnd_388509 < baseStart_388509 := by decide
  rcases family_descends (prefixWord ++ tailWord_388509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388584 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_388584 : Nat := 118140960795 + 388584 * 2 ^ 59
def prefixEnd_388584 : Nat := 4983230072969 + 3 ^ 40 * 388584 * 2
def baseEnd_388584 : Nat := 133020244431208598008627

theorem tailTrace_388584 : CollatzResearch.WordTrace tailWord_388584 prefixEnd_388584 133020244431208598008627 := by
  unfold tailWord_388584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086411412117003854366403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9448548549489338472488537 7086411412117003854366403)
  ·
    refine ⟨10629617118175505781549605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7086411412117003854366403 10629617118175505781549605)
    ·
      refine ⟨1993053209657907334040551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10629617118175505781549605 1993053209657907334040551)
      ·
        refine ⟨2989579814486861001060827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993053209657907334040551 2989579814486861001060827)
        ·
          refine ⟨4484369721730291501591241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989579814486861001060827 4484369721730291501591241)
          ·
            refine ⟨3363277291297718626193431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4484369721730291501591241 3363277291297718626193431)
            ·
              refine ⟨5044915936946577939290147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3363277291297718626193431 5044915936946577939290147)
              ·
                refine ⟨7567373905419866908935221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044915936946577939290147 7567373905419866908935221)
                ·
                  refine ⟨709441303633112522712677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7567373905419866908935221 709441303633112522712677)
                  ·
                    refine ⟨133020244431208598008627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709441303633112522712677 133020244431208598008627)
                    ·
                      rfl

theorem cell22_388584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_388584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388584 prefixEnd_388584 := by exact prefixLift 388584
  have htrace : WordTrace (prefixWord ++ tailWord_388584) baseStart_388584 baseEnd_388584 := by
    simpa [prefixWord, tailWord_388584, baseEnd_388584] using wordTrace_append hprefix tailTrace_388584
  have hstable : (prefixWord ++ tailWord_388584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388584).length < 2 ^ (prefixWord ++ tailWord_388584).sum := by decide
  have hdescent : baseEnd_388584 < baseStart_388584 := by decide
  rcases family_descends (prefixWord ++ tailWord_388584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388586 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_388586 : Nat := 118140960795 + 388586 * 2 ^ 59
def prefixEnd_388586 : Nat := 4983230072969 + 3 ^ 40 * 388586 * 2
def baseEnd_388586 : Nat := 133020929072081259458621

theorem tailTrace_388586 : CollatzResearch.WordTrace tailWord_388586 prefixEnd_388586 133020929072081259458621 := by
  unfold tailWord_388586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543223942556690512576403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9448597180151174700203741 3543223942556690512576403)
  ·
    refine ⟨5314835913835035768864605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543223942556690512576403 5314835913835035768864605)
    ·
      refine ⟨1993063467688138413324227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5314835913835035768864605 1993063467688138413324227)
      ·
        refine ⟨2989595201532207619986341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993063467688138413324227 2989595201532207619986341)
        ·
          refine ⟨560549100287288928747439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2989595201532207619986341 560549100287288928747439)
          ·
            refine ⟨840823650430933393121159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560549100287288928747439 840823650430933393121159)
            ·
              refine ⟨1261235475646400089681739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840823650430933393121159 1261235475646400089681739)
              ·
                refine ⟨1891853213469600134522609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261235475646400089681739 1891853213469600134522609)
                ·
                  refine ⟨1418889910102200100891957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1891853213469600134522609 1418889910102200100891957)
                  ·
                    refine ⟨133020929072081259458621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1418889910102200100891957 133020929072081259458621)
                    ·
                      rfl

theorem cell22_388586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_388586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388586 prefixEnd_388586 := by exact prefixLift 388586
  have htrace : WordTrace (prefixWord ++ tailWord_388586) baseStart_388586 baseEnd_388586 := by
    simpa [prefixWord, tailWord_388586, baseEnd_388586] using wordTrace_append hprefix tailTrace_388586
  have hstable : (prefixWord ++ tailWord_388586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388586).length < 2 ^ (prefixWord ++ tailWord_388586).sum := by decide
  have hdescent : baseEnd_388586 < baseStart_388586 := by decide
  rcases family_descends (prefixWord ++ tailWord_388586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388616 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 4]
def baseStart_388616 : Nat := 118140960795 + 388616 * 2 ^ 59
def prefixEnd_388616 : Nat := 4983230072969 + 3 ^ 40 * 388616 * 2
def baseEnd_388616 : Nat := 44343732895057060402843

theorem tailTrace_388616 : CollatzResearch.WordTrace tailWord_388616 prefixEnd_388616 44343732895057060402843 := by
  unfold tailWord_388616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086994980059038586948851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9449326640078718115931801 7086994980059038586948851)
  ·
    refine ⟨10630492470088557880423277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7086994980059038586948851 10630492470088557880423277)
    ·
      refine ⟨3986434676283209205158729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10630492470088557880423277 3986434676283209205158729)
      ·
        refine ⟨2989826007212406903869047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3986434676283209205158729 2989826007212406903869047)
        ·
          refine ⟨4484739010818610355803571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989826007212406903869047 4484739010818610355803571)
          ·
            refine ⟨6727108516227915533705357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484739010818610355803571 6727108516227915533705357)
            ·
              refine ⟨2522665693585468325139509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6727108516227915533705357 2522665693585468325139509)
              ·
                refine ⟨236499908773637655481829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2522665693585468325139509 236499908773637655481829)
                ·
                  refine ⟨44343732895057060402843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236499908773637655481829 44343732895057060402843)
                  ·
                    rfl

theorem cell22_388616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_388616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388616 prefixEnd_388616 := by exact prefixLift 388616
  have htrace : WordTrace (prefixWord ++ tailWord_388616) baseStart_388616 baseEnd_388616 := by
    simpa [prefixWord, tailWord_388616, baseEnd_388616] using wordTrace_append hprefix tailTrace_388616
  have hstable : (prefixWord ++ tailWord_388616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388616).length < 2 ^ (prefixWord ++ tailWord_388616).sum := by decide
  have hdescent : baseEnd_388616 < baseStart_388616 := by decide
  rcases family_descends (prefixWord ++ tailWord_388616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388618 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_388618 : Nat := 118140960795 + 388618 * 2 ^ 59
def prefixEnd_388618 : Nat := 4983230072969 + 3 ^ 40 * 388618 * 2
def baseEnd_388618 : Nat := 133031883326043842658523

theorem tailTrace_388618 : CollatzResearch.WordTrace tailWord_388618 prefixEnd_388618 133031883326043842658523 := by
  unfold tailWord_388618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543515726527707878867627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9449375270740554343647005 3543515726527707878867627)
  ·
    refine ⟨5315273589791561818301441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543515726527707878867627 5315273589791561818301441)
    ·
      refine ⟨3986455192343671363726081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5315273589791561818301441 3986455192343671363726081)
      ·
        refine ⟨2989841394257753522794561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3986455192343671363726081 2989841394257753522794561)
        ·
          refine ⟨2242381045693315142095921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2989841394257753522794561 2242381045693315142095921)
          ·
            refine ⟨1681785784269986356571941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242381045693315142095921 1681785784269986356571941)
            ·
              refine ⟨315334834550622441857239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1681785784269986356571941 315334834550622441857239)
              ·
                refine ⟨473002251825933662785859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315334834550622441857239 473002251825933662785859)
                ·
                  refine ⟨709503377738900494178789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473002251825933662785859 709503377738900494178789)
                  ·
                    refine ⟨133031883326043842658523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709503377738900494178789 133031883326043842658523)
                    ·
                      rfl

theorem cell22_388618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_388618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388618 prefixEnd_388618 := by exact prefixLift 388618
  have htrace : WordTrace (prefixWord ++ tailWord_388618) baseStart_388618 baseEnd_388618 := by
    simpa [prefixWord, tailWord_388618, baseEnd_388618] using wordTrace_append hprefix tailTrace_388618
  have hstable : (prefixWord ++ tailWord_388618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388618).length < 2 ^ (prefixWord ++ tailWord_388618).sum := by decide
  have hdescent : baseEnd_388618 < baseStart_388618 := by decide
  rcases family_descends (prefixWord ++ tailWord_388618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388661 : List Nat := [1, 3, 3, 1, 1, 3, 4, 6]
def baseStart_388661 : Nat := 118140960795 + 388661 * 2 ^ 59
def prefixEnd_388661 : Nat := 4983230072969 + 3 ^ 40 * 388661 * 2
def baseEnd_388661 : Nat := 14782955900534007092599

theorem tailTrace_388661 : CollatzResearch.WordTrace tailWord_388661 prefixEnd_388661 14782955900534007092599 := by
  unfold tailWord_388661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175631244955049859285837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9450420829970033239523891 14175631244955049859285837)
  ·
    refine ⟨5315861716858143697232189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14175631244955049859285837 5315861716858143697232189)
    ·
      refine ⟨1993448143821803886462071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5315861716858143697232189 1993448143821803886462071)
      ·
        refine ⟨2990172215732705829693107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993448143821803886462071 2990172215732705829693107)
        ·
          refine ⟨4485258323599058744539661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2990172215732705829693107 4485258323599058744539661)
          ·
            refine ⟨1681971871349647029202373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4485258323599058744539661 1681971871349647029202373)
            ·
              refine ⟨315369725878058817975445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1681971871349647029202373 315369725878058817975445)
              ·
                refine ⟨14782955900534007092599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 315369725878058817975445 14782955900534007092599)
                ·
                  rfl

theorem cell22_388661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 6].length) (baseStart_388661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388661 prefixEnd_388661 := by exact prefixLift 388661
  have htrace : WordTrace (prefixWord ++ tailWord_388661) baseStart_388661 baseEnd_388661 := by
    simpa [prefixWord, tailWord_388661, baseEnd_388661] using wordTrace_append hprefix tailTrace_388661
  have hstable : (prefixWord ++ tailWord_388661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388661).length < 2 ^ (prefixWord ++ tailWord_388661).sum := by decide
  have hdescent : baseEnd_388661 < baseStart_388661 := by decide
  rcases family_descends (prefixWord ++ tailWord_388661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388689 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 7]
def baseStart_388689 : Nat := 118140960795 + 388689 * 2 ^ 59
def prefixEnd_388689 : Nat := 4983230072969 + 3 ^ 40 * 388689 * 2
def baseEnd_388689 : Nat := 44352062692341108044435

theorem tailTrace_388689 : CollatzResearch.WordTrace tailWord_388689 prefixEnd_388689 44352062692341108044435 := by
  unfold tailWord_388689
  simp only [CollatzResearch.WordTrace]
  refine ⟨14176652488853610641305121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9451101659235740427536747 14176652488853610641305121)
  ·
    refine ⟨10632489366640207980978841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14176652488853610641305121 10632489366640207980978841)
    ·
      refine ⟨7974367024980155985734131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10632489366640207980978841 7974367024980155985734131)
      ·
        refine ⟨11961550537470233978601197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7974367024980155985734131 11961550537470233978601197)
        ·
          refine ⟨4485581451551337741975449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11961550537470233978601197 4485581451551337741975449)
          ·
            refine ⟨3364186088663503306481587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4485581451551337741975449 3364186088663503306481587)
            ·
              refine ⟨5046279132995254959722381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3364186088663503306481587 5046279132995254959722381)
              ·
                refine ⟨1892354674873220609895893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5046279132995254959722381 1892354674873220609895893)
                ·
                  refine ⟨44352062692341108044435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1892354674873220609895893 44352062692341108044435)
                  ·
                    rfl

theorem cell22_388689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_388689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388689 prefixEnd_388689 := by exact prefixLift 388689
  have htrace : WordTrace (prefixWord ++ tailWord_388689) baseStart_388689 baseEnd_388689 := by
    simpa [prefixWord, tailWord_388689, baseEnd_388689] using wordTrace_append hprefix tailTrace_388689
  have hstable : (prefixWord ++ tailWord_388689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388689).length < 2 ^ (prefixWord ++ tailWord_388689).sum := by decide
  have hdescent : baseEnd_388689 < baseStart_388689 := by decide
  rcases family_descends (prefixWord ++ tailWord_388689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388704 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_388704 : Nat := 118140960795 + 388704 * 2 ^ 59
def prefixEnd_388704 : Nat := 4983230072969 + 3 ^ 40 * 388704 * 2
def baseEnd_388704 : Nat := 133061322883568285008259

theorem tailTrace_388704 : CollatzResearch.WordTrace tailWord_388704 prefixEnd_388704 133061322883568285008259 := by
  unfold tailWord_388704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088599791899634101550583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9451466389199512135400777 7088599791899634101550583)
  ·
    refine ⟨10632899687849451152325875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7088599791899634101550583 10632899687849451152325875)
    ·
      refine ⟨15949349531774176728488813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10632899687849451152325875 15949349531774176728488813)
      ·
        refine ⟨5981006074415316273183305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15949349531774176728488813 5981006074415316273183305)
        ·
          refine ⟨4485754555811487204887479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5981006074415316273183305 4485754555811487204887479)
          ·
            refine ⟨6728631833717230807331219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485754555811487204887479 6728631833717230807331219)
            ·
              refine ⟨10092947750575846210996829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728631833717230807331219 10092947750575846210996829)
              ·
                refine ⟨3784855406465942329123811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10092947750575846210996829 3784855406465942329123811)
                ·
                  refine ⟨5677283109698913493685717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784855406465942329123811 5677283109698913493685717)
                  ·
                    refine ⟨133061322883568285008259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5677283109698913493685717 133061322883568285008259)
                    ·
                      rfl

theorem cell22_388704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_388704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388704 prefixEnd_388704 := by exact prefixLift 388704
  have htrace : WordTrace (prefixWord ++ tailWord_388704) baseStart_388704 baseEnd_388704 := by
    simpa [prefixWord, tailWord_388704, baseEnd_388704] using wordTrace_append hprefix tailTrace_388704
  have hstable : (prefixWord ++ tailWord_388704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388704).length < 2 ^ (prefixWord ++ tailWord_388704).sum := by decide
  have hdescent : baseEnd_388704 < baseStart_388704 := by decide
  rcases family_descends (prefixWord ++ tailWord_388704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388796 : List Nat := [2, 2, 2, 3, 1, 3, 9]
def baseStart_388796 : Nat := 118140960795 + 388796 * 2 ^ 59
def prefixEnd_388796 : Nat := 4983230072969 + 3 ^ 40 * 388796 * 2
def baseEnd_388796 : Nat := 4929363569026322655851

theorem tailTrace_388796 : CollatzResearch.WordTrace tailWord_388796 prefixEnd_388796 4929363569026322655851 := by
  unfold tailWord_388796
  simp only [CollatzResearch.WordTrace]
  refine ⟨7090277549732983957725121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9453703399643978610300161 7090277549732983957725121)
  ·
    refine ⟨5317708162299737968293841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7090277549732983957725121 5317708162299737968293841)
    ·
      refine ⟨3988281121724803476220381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5317708162299737968293841 3988281121724803476220381)
      ·
        refine ⟨1495605420646801303582643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3988281121724803476220381 1495605420646801303582643)
        ·
          refine ⟨2243408130970201955373965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495605420646801303582643 2243408130970201955373965)
          ·
            refine ⟨841278049113825733265237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2243408130970201955373965 841278049113825733265237)
            ·
              refine ⟨4929363569026322655851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 841278049113825733265237 4929363569026322655851)
              ·
                rfl

theorem cell22_388796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 9].length) (baseStart_388796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388796 prefixEnd_388796 := by exact prefixLift 388796
  have htrace : WordTrace (prefixWord ++ tailWord_388796) baseStart_388796 baseEnd_388796 := by
    simpa [prefixWord, tailWord_388796, baseEnd_388796] using wordTrace_append hprefix tailTrace_388796
  have hstable : (prefixWord ++ tailWord_388796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388796).length < 2 ^ (prefixWord ++ tailWord_388796).sum := by decide
  have hdescent : baseEnd_388796 < baseStart_388796 := by decide
  rcases family_descends (prefixWord ++ tailWord_388796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388856 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_388856 : Nat := 118140960795 + 388856 * 2 ^ 59
def prefixEnd_388856 : Nat := 4983230072969 + 3 ^ 40 * 388856 * 2
def baseEnd_388856 : Nat := 133113355589890555207793

theorem tailTrace_388856 : CollatzResearch.WordTrace tailWord_388856 prefixEnd_388856 133113355589890555207793 := by
  unfold tailWord_388856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091371739624299081317211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9455162319499065441756281 7091371739624299081317211)
  ·
    refine ⟨10637057609436448621975817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7091371739624299081317211 10637057609436448621975817)
    ·
      refine ⟨7977793207077336466481863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10637057609436448621975817 7977793207077336466481863)
      ·
        refine ⟨11966689810616004699722795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977793207077336466481863 11966689810616004699722795)
        ·
          refine ⟨17950034715924007049584193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966689810616004699722795 17950034715924007049584193)
          ·
            refine ⟨13462526036943005287188145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17950034715924007049584193 13462526036943005287188145)
            ·
              refine ⟨10096894527707253965391109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13462526036943005287188145 10096894527707253965391109)
              ·
                refine ⟨1893167723945110118510833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10096894527707253965391109 1893167723945110118510833)
                ·
                  refine ⟨1419875792958832588883125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1893167723945110118510833 1419875792958832588883125)
                  ·
                    refine ⟨133113355589890555207793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1419875792958832588883125 133113355589890555207793)
                    ·
                      rfl

theorem cell22_388856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_388856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388856 prefixEnd_388856 := by exact prefixLift 388856
  have htrace : WordTrace (prefixWord ++ tailWord_388856) baseStart_388856 baseEnd_388856 := by
    simpa [prefixWord, tailWord_388856, baseEnd_388856] using wordTrace_append hprefix tailTrace_388856
  have hstable : (prefixWord ++ tailWord_388856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388856).length < 2 ^ (prefixWord ++ tailWord_388856).sum := by decide
  have hdescent : baseEnd_388856 < baseStart_388856 := by decide
  rcases family_descends (prefixWord ++ tailWord_388856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388920 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 4]
def baseStart_388920 : Nat := 118140960795 + 388920 * 2 ^ 59
def prefixEnd_388920 : Nat := 4983230072969 + 3 ^ 40 * 388920 * 2
def baseEnd_388920 : Nat := 44378421365938573869199

theorem tailTrace_388920 : CollatzResearch.WordTrace tailWord_388920 prefixEnd_388920 44378421365938573869199 := by
  unfold tailWord_388920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092538875508368546482107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9456718500677824728642809 7092538875508368546482107)
  ·
    refine ⟨10638808313262552819723161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7092538875508368546482107 10638808313262552819723161)
    ·
      refine ⟨7979106234946914614792371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10638808313262552819723161 7979106234946914614792371)
      ·
        refine ⟨11968659352420371922188557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979106234946914614792371 11968659352420371922188557)
        ·
          refine ⟨4488247257157639470820709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11968659352420371922188557 4488247257157639470820709)
          ·
            refine ⟨841546360717057400778883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4488247257157639470820709 841546360717057400778883)
            ·
              refine ⟨1262319541075586101168325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841546360717057400778883 1262319541075586101168325)
              ·
                refine ⟨236684913951672393969061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1262319541075586101168325 236684913951672393969061)
                ·
                  refine ⟨44378421365938573869199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236684913951672393969061 44378421365938573869199)
                  ·
                    rfl

theorem cell22_388920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_388920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388920 prefixEnd_388920 := by exact prefixLift 388920
  have htrace : WordTrace (prefixWord ++ tailWord_388920) baseStart_388920 baseEnd_388920 := by
    simpa [prefixWord, tailWord_388920, baseEnd_388920] using wordTrace_append hprefix tailTrace_388920
  have hstable : (prefixWord ++ tailWord_388920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388920).length < 2 ^ (prefixWord ++ tailWord_388920).sum := by decide
  have hdescent : baseEnd_388920 < baseStart_388920 := by decide
  rcases family_descends (prefixWord ++ tailWord_388920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388935 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 2, 3]
def baseStart_388935 : Nat := 118140960795 + 388935 * 2 ^ 59
def prefixEnd_388935 : Nat := 4983230072969 + 3 ^ 40 * 388935 * 2
def baseEnd_388935 : Nat := 133140398904360682482551

theorem tailTrace_388935 : CollatzResearch.WordTrace tailWord_388935 prefixEnd_388935 133140398904360682482551 := by
  unfold tailWord_388935
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185624845962394654760259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9457083230641596436506839 14185624845962394654760259)
  ·
    refine ⟨21278437268943591982140389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14185624845962394654760259 21278437268943591982140389)
    ·
      refine ⟨3989706987926923496651323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21278437268943591982140389 3989706987926923496651323)
      ·
        refine ⟨5984560481890385244976985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989706987926923496651323 5984560481890385244976985)
        ·
          refine ⟨4488420361417788933732739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5984560481890385244976985 4488420361417788933732739)
          ·
            refine ⟨6732630542126683400599109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4488420361417788933732739 6732630542126683400599109)
            ·
              refine ⟨1262368226648753137612333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6732630542126683400599109 1262368226648753137612333)
              ·
                refine ⟨473388084993282426604625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1262368226648753137612333 473388084993282426604625)
                ·
                  refine ⟨355041063744961819953469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473388084993282426604625 355041063744961819953469)
                  ·
                    refine ⟨133140398904360682482551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355041063744961819953469 133140398904360682482551)
                    ·
                      rfl

theorem cell22_388935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_388935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388935 prefixEnd_388935 := by exact prefixLift 388935
  have htrace : WordTrace (prefixWord ++ tailWord_388935) baseStart_388935 baseEnd_388935 := by
    simpa [prefixWord, tailWord_388935, baseEnd_388935] using wordTrace_append hprefix tailTrace_388935
  have hstable : (prefixWord ++ tailWord_388935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388935).length < 2 ^ (prefixWord ++ tailWord_388935).sum := by decide
  have hdescent : baseEnd_388935 < baseStart_388935 := by decide
  rcases family_descends (prefixWord ++ tailWord_388935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388956 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_388956 : Nat := 118140960795 + 388956 * 2 ^ 59
def prefixEnd_388956 : Nat := 4983230072969 + 3 ^ 40 * 388956 * 2
def baseEnd_388956 : Nat := 133147587633523627707487

theorem tailTrace_388956 : CollatzResearch.WordTrace tailWord_388956 prefixEnd_388956 133147587633523627707487 := by
  unfold tailWord_388956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093195389443157620637361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9457593852590876827516481 7093195389443157620637361)
  ·
    refine ⟨5319896542082368215478021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7093195389443157620637361 5319896542082368215478021)
    ·
      refine ⟨997480601640444040402129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5319896542082368215478021 997480601640444040402129)
      ·
        refine ⟨748110451230333030301597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 997480601640444040402129 748110451230333030301597)
        ·
          refine ⟨280541419211374886363099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 748110451230333030301597 280541419211374886363099)
          ·
            refine ⟨420812128817062329544649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280541419211374886363099 420812128817062329544649)
            ·
              refine ⟨315609096612796747158487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420812128817062329544649 315609096612796747158487)
              ·
                refine ⟨473413644919195120737731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315609096612796747158487 473413644919195120737731)
                ·
                  refine ⟨710120467378792681106597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473413644919195120737731 710120467378792681106597)
                  ·
                    refine ⟨133147587633523627707487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710120467378792681106597 133147587633523627707487)
                    ·
                      rfl

theorem cell22_388956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_388956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_388956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_388956 prefixEnd_388956 := by exact prefixLift 388956
  have htrace : WordTrace (prefixWord ++ tailWord_388956) baseStart_388956 baseEnd_388956 := by
    simpa [prefixWord, tailWord_388956, baseEnd_388956] using wordTrace_append hprefix tailTrace_388956
  have hstable : (prefixWord ++ tailWord_388956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388956).length < 2 ^ (prefixWord ++ tailWord_388956).sum := by decide
  have hdescent : baseEnd_388956 < baseStart_388956 := by decide
  rcases family_descends (prefixWord ++ tailWord_388956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389010 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_389010 : Nat := 118140960795 + 389010 * 2 ^ 59
def prefixEnd_389010 : Nat := 4983230072969 + 3 ^ 40 * 389010 * 2
def baseEnd_389010 : Nat := 44388690979028495619107

theorem tailTrace_389010 : CollatzResearch.WordTrace tailWord_389010 prefixEnd_389010 44388690979028495619107 := by
  unfold tailWord_389010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547090080172670615935121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9458906880460454975826989 3547090080172670615935121)
  ·
    refine ⟨2660317560129502961951341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3547090080172670615935121 2660317560129502961951341)
    ·
      refine ⟨997619085048563610731753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2660317560129502961951341 997619085048563610731753)
      ·
        refine ⟨748214313786422708048815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 997619085048563610731753 748214313786422708048815)
        ·
          refine ⟨1122321470679634062073223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748214313786422708048815 1122321470679634062073223)
          ·
            refine ⟨1683482206019451093109835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122321470679634062073223 1683482206019451093109835)
            ·
              refine ⟨2525223309029176639664753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683482206019451093109835 2525223309029176639664753)
              ·
                refine ⟨1893917481771882479748565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525223309029176639664753 1893917481771882479748565)
                ·
                  refine ⟨44388690979028495619107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1893917481771882479748565 44388690979028495619107)
                  ·
                    rfl

theorem cell22_389010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_389010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389010 prefixEnd_389010 := by exact prefixLift 389010
  have htrace : WordTrace (prefixWord ++ tailWord_389010) baseStart_389010 baseEnd_389010 := by
    simpa [prefixWord, tailWord_389010, baseEnd_389010] using wordTrace_append hprefix tailTrace_389010
  have hstable : (prefixWord ++ tailWord_389010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389010).length < 2 ^ (prefixWord ++ tailWord_389010).sum := by decide
  have hdescent : baseEnd_389010 < baseStart_389010 := by decide
  rcases family_descends (prefixWord ++ tailWord_389010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389031 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 1, 3]
def baseStart_389031 : Nat := 118140960795 + 389031 * 2 ^ 59
def prefixEnd_389031 : Nat := 4983230072969 + 3 ^ 40 * 389031 * 2
def baseEnd_389031 : Nat := 133173261666248432082257

theorem tailTrace_389031 : CollatzResearch.WordTrace tailWord_389031 prefixEnd_389031 133173261666248432082257 := by
  unfold tailWord_389031
  simp only [CollatzResearch.WordTrace]
  refine ⟨14189126253614603050254947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9459417502409735366836631 14189126253614603050254947)
  ·
    refine ⟨21283689380421904575382421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14189126253614603050254947 21283689380421904575382421)
    ·
      refine ⟨997672939707276776971051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21283689380421904575382421 997672939707276776971051)
      ·
        refine ⟨1496509409560915165456577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997672939707276776971051 1496509409560915165456577)
        ·
          refine ⟨1122382057170686374092433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496509409560915165456577 1122382057170686374092433)
          ·
            refine ⟨841786542878014780569325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1122382057170686374092433 841786542878014780569325)
            ·
              refine ⟨315669953579255542713497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 841786542878014780569325 315669953579255542713497)
              ·
                refine ⟨236752465184441657035123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315669953579255542713497 236752465184441657035123)
                ·
                  refine ⟨355128697776662485552685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236752465184441657035123 355128697776662485552685)
                  ·
                    refine ⟨133173261666248432082257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355128697776662485552685 133173261666248432082257)
                    ·
                      rfl

theorem cell22_389031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_389031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389031 prefixEnd_389031 := by exact prefixLift 389031
  have htrace : WordTrace (prefixWord ++ tailWord_389031) baseStart_389031 baseEnd_389031 := by
    simpa [prefixWord, tailWord_389031, baseEnd_389031] using wordTrace_append hprefix tailTrace_389031
  have hstable : (prefixWord ++ tailWord_389031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389031).length < 2 ^ (prefixWord ++ tailWord_389031).sum := by decide
  have hdescent : baseEnd_389031 < baseStart_389031 := by decide
  rcases family_descends (prefixWord ++ tailWord_389031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389044 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_389044 : Nat := 118140960795 + 389044 * 2 ^ 59
def prefixEnd_389044 : Nat := 4983230072969 + 3 ^ 40 * 389044 * 2
def baseEnd_389044 : Nat := 44392570610640243835739

theorem tailTrace_389044 : CollatzResearch.WordTrace tailWord_389044 prefixEnd_389044 44392570610640243835739 := by
  unfold tailWord_389044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7094800201283753135239093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9459733601711670846985457 7094800201283753135239093)
  ·
    refine ⟨665137518870351856428665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7094800201283753135239093 665137518870351856428665)
    ·
      refine ⟨498853139152763892321499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 665137518870351856428665 498853139152763892321499)
      ·
        refine ⟨748279708729145838482249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498853139152763892321499 748279708729145838482249)
        ·
          refine ⟨561209781546859378861687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748279708729145838482249 561209781546859378861687)
          ·
            refine ⟨841814672320289068292531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561209781546859378861687 841814672320289068292531)
            ·
              refine ⟨1262722008480433602438797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841814672320289068292531 1262722008480433602438797)
              ·
                refine ⟨473520753180162600914549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1262722008480433602438797 473520753180162600914549)
                ·
                  refine ⟨44392570610640243835739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 473520753180162600914549 44392570610640243835739)
                  ·
                    rfl

theorem cell22_389044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_389044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389044 prefixEnd_389044 := by exact prefixLift 389044
  have htrace : WordTrace (prefixWord ++ tailWord_389044) baseStart_389044 baseEnd_389044 := by
    simpa [prefixWord, tailWord_389044, baseEnd_389044] using wordTrace_append hprefix tailTrace_389044
  have hstable : (prefixWord ++ tailWord_389044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389044).length < 2 ^ (prefixWord ++ tailWord_389044).sum := by decide
  have hdescent : baseEnd_389044 < baseStart_389044 := by decide
  rcases family_descends (prefixWord ++ tailWord_389044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389070 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_389070 : Nat := 118140960795 + 389070 * 2 ^ 59
def prefixEnd_389070 : Nat := 4983230072969 + 3 ^ 40 * 389070 * 2
def baseEnd_389070 : Nat := 133186612163265330357137

theorem tailTrace_389070 : CollatzResearch.WordTrace tailWord_389070 prefixEnd_389070 133186612163265330357137 := by
  unfold tailWord_389070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773818587559164088865583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9460365800315541807283109 1773818587559164088865583)
  ·
    refine ⟨2660727881338746133298375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1773818587559164088865583 2660727881338746133298375)
    ·
      refine ⟨3991091822008119199947563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2660727881338746133298375 3991091822008119199947563)
      ·
        refine ⟨5986637733012178799921345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991091822008119199947563 5986637733012178799921345)
        ·
          refine ⟨4489978299759134099941009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5986637733012178799921345 4489978299759134099941009)
          ·
            refine ⟨3367483724819350574955757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4489978299759134099941009 3367483724819350574955757)
            ·
              refine ⟨1262806396807256465608409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3367483724819350574955757 1262806396807256465608409)
              ·
                refine ⟨947104797605442349206307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262806396807256465608409 947104797605442349206307)
                ·
                  refine ⟨1420657196408163523809461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947104797605442349206307 1420657196408163523809461)
                  ·
                    refine ⟨133186612163265330357137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1420657196408163523809461 133186612163265330357137)
                    ·
                      rfl

theorem cell22_389070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_389070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389070 prefixEnd_389070 := by exact prefixLift 389070
  have htrace : WordTrace (prefixWord ++ tailWord_389070) baseStart_389070 baseEnd_389070 := by
    simpa [prefixWord, tailWord_389070, baseEnd_389070] using wordTrace_append hprefix tailTrace_389070
  have hstable : (prefixWord ++ tailWord_389070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389070).length < 2 ^ (prefixWord ++ tailWord_389070).sum := by decide
  have hdescent : baseEnd_389070 < baseStart_389070 := by decide
  rcases family_descends (prefixWord ++ tailWord_389070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389087 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 2, 3]
def baseStart_389087 : Nat := 118140960795 + 389087 * 2 ^ 59
def prefixEnd_389087 : Nat := 4983230072969 + 3 ^ 40 * 389087 * 2
def baseEnd_389087 : Nat := 133192431610682952682085

theorem tailTrace_389087 : CollatzResearch.WordTrace tailWord_389087 prefixEnd_389087 133192431610682952682085 := by
  unfold tailWord_389087
  simp only [CollatzResearch.WordTrace]
  refine ⟨14191168741411724614293515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9460779160941149742862343 14191168741411724614293515)
  ·
    refine ⟨21286753112117586921440273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14191168741411724614293515 21286753112117586921440273)
    ·
      refine ⟨15965064834088190191080205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21286753112117586921440273 15965064834088190191080205)
      ·
        refine ⟨5986899312783071321655077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15965064834088190191080205 5986899312783071321655077)
        ·
          refine ⟨1122543621146825872810327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5986899312783071321655077 1122543621146825872810327)
          ·
            refine ⟨1683815431720238809215491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122543621146825872810327 1683815431720238809215491)
            ·
              refine ⟨2525723147580358213823237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683815431720238809215491 2525723147580358213823237)
              ·
                refine ⟨473573090171317165091857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2525723147580358213823237 473573090171317165091857)
                ·
                  refine ⟨355179817628487873818893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473573090171317165091857 355179817628487873818893)
                  ·
                    refine ⟨133192431610682952682085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355179817628487873818893 133192431610682952682085)
                    ·
                      rfl

theorem cell22_389087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_389087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389087 prefixEnd_389087 := by exact prefixLift 389087
  have htrace : WordTrace (prefixWord ++ tailWord_389087) baseStart_389087 baseEnd_389087 := by
    simpa [prefixWord, tailWord_389087, baseEnd_389087] using wordTrace_append hprefix tailTrace_389087
  have hstable : (prefixWord ++ tailWord_389087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389087).length < 2 ^ (prefixWord ++ tailWord_389087).sum := by decide
  have hdescent : baseEnd_389087 < baseStart_389087 := by decide
  rcases family_descends (prefixWord ++ tailWord_389087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389115 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 5, 3]
def baseStart_389115 : Nat := 118140960795 + 389115 * 2 ^ 59
def prefixEnd_389115 : Nat := 4983230072969 + 3 ^ 40 * 389115 * 2
def baseEnd_389115 : Nat := 133202016582900212981999

theorem tailTrace_389115 : CollatzResearch.WordTrace tailWord_389115 prefixEnd_389115 133202016582900212981999 := by
  unfold tailWord_389115
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192189985310285396312799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9461459990206856930875199 14192189985310285396312799)
  ·
    refine ⟨21288284977965428094469199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14192189985310285396312799 21288284977965428094469199)
    ·
      refine ⟨31932427466948142141703799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21288284977965428094469199 31932427466948142141703799)
      ·
        refine ⟨47898641200422213212555699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31932427466948142141703799 47898641200422213212555699)
        ·
          refine ⟨71847961800633319818833549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47898641200422213212555699 71847961800633319818833549)
          ·
            refine ⟨26942985675237494932062581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71847961800633319818833549 26942985675237494932062581)
            ·
              refine ⟨2525904907053515149880867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26942985675237494932062581 2525904907053515149880867)
              ·
                refine ⟨3788857360580272724821301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525904907053515149880867 3788857360580272724821301)
                ·
                  refine ⟨355205377554400567951997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3788857360580272724821301 355205377554400567951997)
                  ·
                    refine ⟨133202016582900212981999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355205377554400567951997 133202016582900212981999)
                    ·
                      rfl

theorem cell22_389115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 3].length) (baseStart_389115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389115 prefixEnd_389115 := by exact prefixLift 389115
  have htrace : WordTrace (prefixWord ++ tailWord_389115) baseStart_389115 baseEnd_389115 := by
    simpa [prefixWord, tailWord_389115, baseEnd_389115] using wordTrace_append hprefix tailTrace_389115
  have hstable : (prefixWord ++ tailWord_389115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389115).length < 2 ^ (prefixWord ++ tailWord_389115).sum := by decide
  have hdescent : baseEnd_389115 < baseStart_389115 := by decide
  rcases family_descends (prefixWord ++ tailWord_389115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389149 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_389149 : Nat := 118140960795 + 389149 * 2 ^ 59
def prefixEnd_389149 : Nat := 4983230072969 + 3 ^ 40 * 389149 * 2
def baseEnd_389149 : Nat := 133213655477735457631895

theorem tailTrace_389149 : CollatzResearch.WordTrace tailWord_389149 prefixEnd_389149 133213655477735457631895 := by
  unfold tailWord_389149
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193430067187109203050501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9462286711458072802033667 14193430067187109203050501)
  ·
    refine ⟨2661268137597582975571969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14193430067187109203050501 2661268137597582975571969)
    ·
      refine ⟨1995951103198187231678977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2661268137597582975571969 1995951103198187231678977)
      ·
        refine ⟨1496963327398640423759233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995951103198187231678977 1496963327398640423759233)
        ·
          refine ⟨1122722495548980317819425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496963327398640423759233 1122722495548980317819425)
          ·
            refine ⟨842041871661735238364569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1122722495548980317819425 842041871661735238364569)
            ·
              refine ⟨631531403746301428773427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842041871661735238364569 631531403746301428773427)
              ·
                refine ⟨947297105619452143160141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631531403746301428773427 947297105619452143160141)
                ·
                  refine ⟨355236414607294553685053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947297105619452143160141 355236414607294553685053)
                  ·
                    refine ⟨133213655477735457631895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355236414607294553685053 133213655477735457631895)
                    ·
                      rfl

theorem cell22_389149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_389149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389149 prefixEnd_389149 := by exact prefixLift 389149
  have htrace : WordTrace (prefixWord ++ tailWord_389149) baseStart_389149 baseEnd_389149 := by
    simpa [prefixWord, tailWord_389149, baseEnd_389149] using wordTrace_append hprefix tailTrace_389149
  have hstable : (prefixWord ++ tailWord_389149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389149).length < 2 ^ (prefixWord ++ tailWord_389149).sum := by decide
  have hdescent : baseEnd_389149 < baseStart_389149 := by decide
  rcases family_descends (prefixWord ++ tailWord_389149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389175 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 3, 4]
def baseStart_389175 : Nat := 118140960795 + 389175 * 2 ^ 59
def prefixEnd_389175 : Nat := 4983230072969 + 3 ^ 40 * 389175 * 2
def baseEnd_389175 : Nat := 133222555809080056481815

theorem tailTrace_389175 : CollatzResearch.WordTrace tailWord_389175 prefixEnd_389175 133222555809080056481815 := by
  unfold tailWord_389175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194378365092915643496979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9462918910061943762331319 14194378365092915643496979)
  ·
    refine ⟨21291567547639373465245469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14194378365092915643496979 21291567547639373465245469)
    ·
      refine ⟨7984337830364765049467051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21291567547639373465245469 7984337830364765049467051)
      ·
        refine ⟨11976506745547147574200577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7984337830364765049467051 11976506745547147574200577)
        ·
          refine ⟨8982380059160360680650433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11976506745547147574200577 8982380059160360680650433)
          ·
            refine ⟨6736785044370270510487825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8982380059160360680650433 6736785044370270510487825)
            ·
              refine ⟨5052588783277702882865869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6736785044370270510487825 5052588783277702882865869)
              ·
                refine ⟨1894720793729138581074701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5052588783277702882865869 1894720793729138581074701)
                ·
                  refine ⟨710520297648426967903013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1894720793729138581074701 710520297648426967903013)
                  ·
                    refine ⟨133222555809080056481815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710520297648426967903013 133222555809080056481815)
                    ·
                      rfl

theorem cell22_389175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_389175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389175 prefixEnd_389175 := by exact prefixLift 389175
  have htrace : WordTrace (prefixWord ++ tailWord_389175) baseStart_389175 baseEnd_389175 := by
    simpa [prefixWord, tailWord_389175, baseEnd_389175] using wordTrace_append hprefix tailTrace_389175
  have hstable : (prefixWord ++ tailWord_389175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389175).length < 2 ^ (prefixWord ++ tailWord_389175).sum := by decide
  have hdescent : baseEnd_389175 < baseStart_389175 := by decide
  rcases family_descends (prefixWord ++ tailWord_389175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389207 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 4]
def baseStart_389207 : Nat := 118140960795 + 389207 * 2 ^ 59
def prefixEnd_389207 : Nat := 4983230072969 + 3 ^ 40 * 389207 * 2
def baseEnd_389207 : Nat := 44411170021014213227239

theorem tailTrace_389207 : CollatzResearch.WordTrace tailWord_389207 prefixEnd_389207 44411170021014213227239 := by
  unfold tailWord_389207
  simp only [CollatzResearch.WordTrace]
  refine ⟨14195545500976985108661875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9463697000651323405774583 14195545500976985108661875)
  ·
    refine ⟨21293318251465477662992813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14195545500976985108661875 21293318251465477662992813)
    ·
      refine ⟨7984994344299554123622305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21293318251465477662992813 7984994344299554123622305)
      ·
        refine ⟨5988745758224665592716729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7984994344299554123622305 5988745758224665592716729)
        ·
          refine ⟨4491559318668499194537547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5988745758224665592716729 4491559318668499194537547)
          ·
            refine ⟨6737338978002748791806321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491559318668499194537547 6737338978002748791806321)
            ·
              refine ⟨5053004233502061593854741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6737338978002748791806321 5053004233502061593854741)
              ·
                refine ⟨236859573445409137211941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5053004233502061593854741 236859573445409137211941)
                ·
                  refine ⟨44411170021014213227239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236859573445409137211941 44411170021014213227239)
                  ·
                    rfl

theorem cell22_389207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 4].length) (baseStart_389207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389207 prefixEnd_389207 := by exact prefixLift 389207
  have htrace : WordTrace (prefixWord ++ tailWord_389207) baseStart_389207 baseEnd_389207 := by
    simpa [prefixWord, tailWord_389207, baseEnd_389207] using wordTrace_append hprefix tailTrace_389207
  have hstable : (prefixWord ++ tailWord_389207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389207).length < 2 ^ (prefixWord ++ tailWord_389207).sum := by decide
  have hdescent : baseEnd_389207 < baseStart_389207 := by decide
  rcases family_descends (prefixWord ++ tailWord_389207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389220 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_389220 : Nat := 118140960795 + 389220 * 2 ^ 59
def prefixEnd_389220 : Nat := 4983230072969 + 3 ^ 40 * 389220 * 2
def baseEnd_389220 : Nat := 133237960228714939106677

theorem tailTrace_389220 : CollatzResearch.WordTrace tailWord_389220 prefixEnd_389220 133237960228714939106677 := by
  unfold tailWord_389220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098009824964944164442557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9464013099953258885923409 7098009824964944164442557)
  ·
    refine ⟨2661753684361854061665959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7098009824964944164442557 2661753684361854061665959)
    ·
      refine ⟨3992630526542781092498939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661753684361854061665959 3992630526542781092498939)
      ·
        refine ⟨5988945789814171638748409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3992630526542781092498939 5988945789814171638748409)
        ·
          refine ⟨4491709342360628729061307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5988945789814171638748409 4491709342360628729061307)
          ·
            refine ⟨6737564013540943093591961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491709342360628729061307 6737564013540943093591961)
            ·
              refine ⟨5053173010155707320193971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6737564013540943093591961 5053173010155707320193971)
              ·
                refine ⟨7579759515233560980290957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053173010155707320193971 7579759515233560980290957)
                ·
                  refine ⟨2842409818212585367609109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7579759515233560980290957 2842409818212585367609109)
                  ·
                    refine ⟨133237960228714939106677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2842409818212585367609109 133237960228714939106677)
                    ·
                      rfl

theorem cell22_389220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_389220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389220 prefixEnd_389220 := by exact prefixLift 389220
  have htrace : WordTrace (prefixWord ++ tailWord_389220) baseStart_389220 baseEnd_389220 := by
    simpa [prefixWord, tailWord_389220, baseEnd_389220] using wordTrace_append hprefix tailTrace_389220
  have hstable : (prefixWord ++ tailWord_389220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389220).length < 2 ^ (prefixWord ++ tailWord_389220).sum := by decide
  have hdescent : baseEnd_389220 < baseStart_389220 := by decide
  rcases family_descends (prefixWord ++ tailWord_389220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389226 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_389226 : Nat := 118140960795 + 389226 * 2 ^ 59
def prefixEnd_389226 : Nat := 4983230072969 + 3 ^ 40 * 389226 * 2
def baseEnd_389226 : Nat := 133240014151332923456659

theorem tailTrace_389226 : CollatzResearch.WordTrace tailWord_389226 prefixEnd_389226 133240014151332923456659 := by
  unfold tailWord_389226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549059621977037838400883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9464158991938767569069021 3549059621977037838400883)
  ·
    refine ⟨5323589432965556757601325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3549059621977037838400883 5323589432965556757601325)
    ·
      refine ⟨1996346037362083784100497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5323589432965556757601325 1996346037362083784100497)
      ·
        refine ⟨1497259528021562838075373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1996346037362083784100497 1497259528021562838075373)
        ·
          refine ⟨561472323008086064278265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1497259528021562838075373 561472323008086064278265)
          ·
            refine ⟨421104242256064548208699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561472323008086064278265 421104242256064548208699)
            ·
              refine ⟨631656363384096822313049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421104242256064548208699 631656363384096822313049)
              ·
                refine ⟨473742272538072616734787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631656363384096822313049 473742272538072616734787)
                ·
                  refine ⟨710613408807108925102181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473742272538072616734787 710613408807108925102181)
                  ·
                    refine ⟨133240014151332923456659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710613408807108925102181 133240014151332923456659)
                    ·
                      rfl

theorem cell22_389226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_389226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389226 prefixEnd_389226 := by exact prefixLift 389226
  have htrace : WordTrace (prefixWord ++ tailWord_389226) baseStart_389226 baseEnd_389226 := by
    simpa [prefixWord, tailWord_389226, baseEnd_389226] using wordTrace_append hprefix tailTrace_389226
  have hstable : (prefixWord ++ tailWord_389226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389226).length < 2 ^ (prefixWord ++ tailWord_389226).sum := by decide
  have hdescent : baseEnd_389226 < baseStart_389226 := by decide
  rcases family_descends (prefixWord ++ tailWord_389226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389256 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_389256 : Nat := 118140960795 + 389256 * 2 ^ 59
def prefixEnd_389256 : Nat := 4983230072969 + 3 ^ 40 * 389256 * 2
def baseEnd_389256 : Nat := 133250283764422845206567

theorem tailTrace_389256 : CollatzResearch.WordTrace tailWord_389256 prefixEnd_389256 133250283764422845206567 := by
  unfold tailWord_389256
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098666338899733238597811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9464888451866310984797081 7098666338899733238597811)
  ·
    refine ⟨10647999508349599857896717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7098666338899733238597811 10647999508349599857896717)
    ·
      refine ⟨3992999815631099946711269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10647999508349599857896717 3992999815631099946711269)
      ·
        refine ⟨748687465430831240008363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3992999815631099946711269 748687465430831240008363)
        ·
          refine ⟨1123031198146246860012545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748687465430831240008363 1123031198146246860012545)
          ·
            refine ⟨842273398609685145009409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123031198146246860012545 842273398609685145009409)
            ·
              refine ⟨631705048957263858757057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842273398609685145009409 631705048957263858757057)
              ·
                refine ⟨473778786717947894067793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631705048957263858757057 473778786717947894067793)
                ·
                  refine ⟨355334090038460920550845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473778786717947894067793 355334090038460920550845)
                  ·
                    refine ⟨133250283764422845206567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355334090038460920550845 133250283764422845206567)
                    ·
                      rfl

theorem cell22_389256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_389256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389256 prefixEnd_389256 := by exact prefixLift 389256
  have htrace : WordTrace (prefixWord ++ tailWord_389256) baseStart_389256 baseEnd_389256 := by
    simpa [prefixWord, tailWord_389256, baseEnd_389256] using wordTrace_append hprefix tailTrace_389256
  have hstable : (prefixWord ++ tailWord_389256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389256).length < 2 ^ (prefixWord ++ tailWord_389256).sum := by decide
  have hdescent : baseEnd_389256 < baseStart_389256 := by decide
  rcases family_descends (prefixWord ++ tailWord_389256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389267 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 3, 3]
def baseStart_389267 : Nat := 118140960795 + 389267 * 2 ^ 59
def prefixEnd_389267 : Nat := 4983230072969 + 3 ^ 40 * 389267 * 2
def baseEnd_389267 : Nat := 133254049289222483181533

theorem tailTrace_389267 : CollatzResearch.WordTrace tailWord_389267 prefixEnd_389267 133254049289222483181533 := by
  unfold tailWord_389267
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197733880759615355846055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9465155920506410237230703 14197733880759615355846055)
  ·
    refine ⟨21296600821139423033769083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14197733880759615355846055 21296600821139423033769083)
    ·
      refine ⟨31944901231709134550653625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21296600821139423033769083 31944901231709134550653625)
      ·
        refine ⟨23958675923781850912990219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31944901231709134550653625 23958675923781850912990219)
        ·
          refine ⟨35938013885672776369485329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23958675923781850912990219 35938013885672776369485329)
          ·
            refine ⟨26953510414254582277113997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35938013885672776369485329 26953510414254582277113997)
            ·
              refine ⟨10107566405345468353917749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26953510414254582277113997 10107566405345468353917749)
              ·
                refine ⟨947584350501137658179789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10107566405345468353917749 947584350501137658179789)
                ·
                  refine ⟨355344131437926621817421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 947584350501137658179789 355344131437926621817421)
                  ·
                    refine ⟨133254049289222483181533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355344131437926621817421 133254049289222483181533)
                    ·
                      rfl

theorem cell22_389267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 3].length) (baseStart_389267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389267 prefixEnd_389267 := by exact prefixLift 389267
  have htrace : WordTrace (prefixWord ++ tailWord_389267) baseStart_389267 baseEnd_389267 := by
    simpa [prefixWord, tailWord_389267, baseEnd_389267] using wordTrace_append hprefix tailTrace_389267
  have hstable : (prefixWord ++ tailWord_389267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389267).length < 2 ^ (prefixWord ++ tailWord_389267).sum := by decide
  have hdescent : baseEnd_389267 < baseStart_389267 := by decide
  rcases family_descends (prefixWord ++ tailWord_389267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389295 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_389295 : Nat := 118140960795 + 389295 * 2 ^ 59
def prefixEnd_389295 : Nat := 4983230072969 + 3 ^ 40 * 389295 * 2
def baseEnd_389295 : Nat := 133263634261439743481447

theorem tailTrace_389295 : CollatzResearch.WordTrace tailWord_389295 prefixEnd_389295 133263634261439743481447 := by
  unfold tailWord_389295
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198755124658176137865339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9465836749772117425243559 14198755124658176137865339)
  ·
    refine ⟨21298132686987264206798009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14198755124658176137865339 21298132686987264206798009)
    ·
      refine ⟨15973599515240448155098507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21298132686987264206798009 15973599515240448155098507)
      ·
        refine ⟨23960399272860672232647761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15973599515240448155098507 23960399272860672232647761)
        ·
          refine ⟨17970299454645504174485821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23960399272860672232647761 17970299454645504174485821)
          ·
            refine ⟨6738862295492064065432183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17970299454645504174485821 6738862295492064065432183)
            ·
              refine ⟨10108293443238096098148275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738862295492064065432183 10108293443238096098148275)
              ·
                refine ⟨15162440164857144147222413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10108293443238096098148275 15162440164857144147222413)
                ·
                  refine ⟨5685915061821429055208405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15162440164857144147222413 5685915061821429055208405)
                  ·
                    refine ⟨133263634261439743481447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5685915061821429055208405 133263634261439743481447)
                    ·
                      rfl

theorem cell22_389295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_389295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389295 prefixEnd_389295 := by exact prefixLift 389295
  have htrace : WordTrace (prefixWord ++ tailWord_389295) baseStart_389295 baseEnd_389295 := by
    simpa [prefixWord, tailWord_389295, baseEnd_389295] using wordTrace_append hprefix tailTrace_389295
  have hstable : (prefixWord ++ tailWord_389295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389295).length < 2 ^ (prefixWord ++ tailWord_389295).sum := by decide
  have hdescent : baseEnd_389295 < baseStart_389295 := by decide
  rcases family_descends (prefixWord ++ tailWord_389295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389312 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_389312 : Nat := 118140960795 + 389312 * 2 ^ 59
def prefixEnd_389312 : Nat := 4983230072969 + 3 ^ 40 * 389312 * 2
def baseEnd_389312 : Nat := 133269453708857365806395

theorem tailTrace_389312 : CollatzResearch.WordTrace tailWord_389312 prefixEnd_389312 133269453708857365806395 := by
  unfold tailWord_389312
  simp only [CollatzResearch.WordTrace]
  refine ⟨7099687582798294020617095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9466250110397725360822793 7099687582798294020617095)
  ·
    refine ⟨10649531374197441030925643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7099687582798294020617095 10649531374197441030925643)
    ·
      refine ⟨15974297061296161546388465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10649531374197441030925643 15974297061296161546388465)
      ·
        refine ⟨11980722795972121159791349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15974297061296161546388465 11980722795972121159791349)
        ·
          refine ⟨1123192762122386358730439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11980722795972121159791349 1123192762122386358730439)
          ·
            refine ⟨1684789143183579538095659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123192762122386358730439 1684789143183579538095659)
            ·
              refine ⟨2527183714775369307143489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684789143183579538095659 2527183714775369307143489)
              ·
                refine ⟨1895387786081526980357617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527183714775369307143489 1895387786081526980357617)
                ·
                  refine ⟨1421540839561145235268213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1895387786081526980357617 1421540839561145235268213)
                  ·
                    refine ⟨133269453708857365806395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1421540839561145235268213 133269453708857365806395)
                    ·
                      rfl

theorem cell22_389312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_389312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389312 prefixEnd_389312 := by exact prefixLift 389312
  have htrace : WordTrace (prefixWord ++ tailWord_389312) baseStart_389312 baseEnd_389312 := by
    simpa [prefixWord, tailWord_389312, baseEnd_389312] using wordTrace_append hprefix tailTrace_389312
  have hstable : (prefixWord ++ tailWord_389312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389312).length < 2 ^ (prefixWord ++ tailWord_389312).sum := by decide
  have hdescent : baseEnd_389312 < baseStart_389312 := by decide
  rcases family_descends (prefixWord ++ tailWord_389312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389344 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_389344 : Nat := 118140960795 + 389344 * 2 ^ 59
def prefixEnd_389344 : Nat := 4983230072969 + 3 ^ 40 * 389344 * 2
def baseEnd_389344 : Nat := 133280407962819949006297

theorem tailTrace_389344 : CollatzResearch.WordTrace tailWord_389344 prefixEnd_389344 133280407962819949006297 := by
  unfold tailWord_389344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100271150740328753199543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9467028200987105004266057 7100271150740328753199543)
  ·
    refine ⟨10650406726110493129799315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7100271150740328753199543 10650406726110493129799315)
    ·
      refine ⟨15975610089165739694698973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10650406726110493129799315 15975610089165739694698973)
      ·
        refine ⟨5990853783437152385512115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15975610089165739694698973 5990853783437152385512115)
        ·
          refine ⟨8986280675155728578268173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990853783437152385512115 8986280675155728578268173)
          ·
            refine ⟨3369855253183398216850565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8986280675155728578268173 3369855253183398216850565)
            ·
              refine ⟨631847859971887165659481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3369855253183398216850565 631847859971887165659481)
              ·
                refine ⟨473885894978915374244611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631847859971887165659481 473885894978915374244611)
                ·
                  refine ⟨710828842468373061366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473885894978915374244611 710828842468373061366917)
                  ·
                    refine ⟨133280407962819949006297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710828842468373061366917 133280407962819949006297)
                    ·
                      rfl

theorem cell22_389344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_389344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389344 prefixEnd_389344 := by exact prefixLift 389344
  have htrace : WordTrace (prefixWord ++ tailWord_389344) baseStart_389344 baseEnd_389344 := by
    simpa [prefixWord, tailWord_389344, baseEnd_389344] using wordTrace_append hprefix tailTrace_389344
  have hstable : (prefixWord ++ tailWord_389344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389344).length < 2 ^ (prefixWord ++ tailWord_389344).sum := by decide
  have hdescent : baseEnd_389344 < baseStart_389344 := by decide
  rcases family_descends (prefixWord ++ tailWord_389344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389387 : List Nat := [1, 1, 1, 1, 5, 2, 4, 7]
def baseStart_389387 : Nat := 118140960795 + 389387 * 2 ^ 59
def prefixEnd_389387 : Nat := 4983230072969 + 3 ^ 40 * 389387 * 2
def baseEnd_389387 : Nat := 14810569749064685575685

theorem tailTrace_389387 : CollatzResearch.WordTrace tailWord_389387 prefixEnd_389387 14810569749064685575685 := by
  unfold tailWord_389387
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202110640324875850214415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9468073760216583900142943 14202110640324875850214415)
  ·
    refine ⟨21303165960487313775321623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14202110640324875850214415 21303165960487313775321623)
    ·
      refine ⟨31954748940730970662982435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21303165960487313775321623 31954748940730970662982435)
      ·
        refine ⟨47932123411096455994473653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31954748940730970662982435 47932123411096455994473653)
        ·
          refine ⟨4493636569790292749481905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47932123411096455994473653 4493636569790292749481905)
          ·
            refine ⟨3370227427342719562111429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4493636569790292749481905 3370227427342719562111429)
            ·
              refine ⟨631917642626759917895893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3370227427342719562111429 631917642626759917895893)
              ·
                refine ⟨14810569749064685575685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 631917642626759917895893 14810569749064685575685)
                ·
                  rfl

theorem cell22_389387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 7].length) (baseStart_389387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389387 prefixEnd_389387 := by exact prefixLift 389387
  have htrace : WordTrace (prefixWord ++ tailWord_389387) baseStart_389387 baseEnd_389387 := by
    simpa [prefixWord, tailWord_389387, baseEnd_389387] using wordTrace_append hprefix tailTrace_389387
  have hstable : (prefixWord ++ tailWord_389387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389387).length < 2 ^ (prefixWord ++ tailWord_389387).sum := by decide
  have hdescent : baseEnd_389387 < baseStart_389387 := by decide
  rcases family_descends (prefixWord ++ tailWord_389387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389421 : List Nat := [1, 5, 3, 1, 3, 9]
def baseStart_389421 : Nat := 118140960795 + 389421 * 2 ^ 59
def prefixEnd_389421 : Nat := 4983230072969 + 3 ^ 40 * 389421 * 2
def baseEnd_389421 : Nat := 1645762551066881664581

theorem tailTrace_389421 : CollatzResearch.WordTrace tailWord_389421 prefixEnd_389421 1645762551066881664581 := by
  unfold tailWord_389421
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203350722201699656952117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9468900481467799771301411 14203350722201699656952117)
  ·
    refine ⟨1331564130206409342839261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14203350722201699656952117 1331564130206409342839261)
    ·
      refine ⟨499336548827403503564723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1331564130206409342839261 499336548827403503564723)
      ·
        refine ⟨749004823241105255347085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499336548827403503564723 749004823241105255347085)
        ·
          refine ⟨280876808715414470755157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 749004823241105255347085 280876808715414470755157)
          ·
            refine ⟨1645762551066881664581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 280876808715414470755157 1645762551066881664581)
            ·
              rfl

theorem cell22_389421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 9].length) (baseStart_389421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389421 prefixEnd_389421 := by exact prefixLift 389421
  have htrace : WordTrace (prefixWord ++ tailWord_389421) baseStart_389421 baseEnd_389421 := by
    simpa [prefixWord, tailWord_389421, baseEnd_389421] using wordTrace_append hprefix tailTrace_389421
  have hstable : (prefixWord ++ tailWord_389421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389421).length < 2 ^ (prefixWord ++ tailWord_389421).sum := by decide
  have hdescent : baseEnd_389421 < baseStart_389421 := by decide
  rcases family_descends (prefixWord ++ tailWord_389421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389432 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_389432 : Nat := 118140960795 + 389432 * 2 ^ 59
def prefixEnd_389432 : Nat := 4983230072969 + 3 ^ 40 * 389432 * 2
def baseEnd_389432 : Nat := 44436844053739017602009

theorem tailTrace_389432 : CollatzResearch.WordTrace tailWord_389432 prefixEnd_389432 44436844053739017602009 := by
  unfold tailWord_389432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101875962580924267801275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9469167950107899023735033 7101875962580924267801275)
  ·
    refine ⟨10652813943871386401701913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7101875962580924267801275 10652813943871386401701913)
    ·
      refine ⟨7989610457903539801276435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10652813943871386401701913 7989610457903539801276435)
      ·
        refine ⟨11984415686855309701914653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989610457903539801276435 11984415686855309701914653)
        ·
          refine ⟨4494155882570741138217995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11984415686855309701914653 4494155882570741138217995)
          ·
            refine ⟨6741233823856111707326993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494155882570741138217995 6741233823856111707326993)
            ·
              refine ⟨5055925367892083780495245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6741233823856111707326993 5055925367892083780495245)
              ·
                refine ⟨1895972012959531417685717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5055925367892083780495245 1895972012959531417685717)
                ·
                  refine ⟨44436844053739017602009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1895972012959531417685717 44436844053739017602009)
                  ·
                    rfl

theorem cell22_389432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_389432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389432 prefixEnd_389432 := by exact prefixLift 389432
  have htrace : WordTrace (prefixWord ++ tailWord_389432) baseStart_389432 baseEnd_389432 := by
    simpa [prefixWord, tailWord_389432, baseEnd_389432] using wordTrace_append hprefix tailTrace_389432
  have hstable : (prefixWord ++ tailWord_389432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389432).length < 2 ^ (prefixWord ++ tailWord_389432).sum := by decide
  have hdescent : baseEnd_389432 < baseStart_389432 := by decide
  rcases family_descends (prefixWord ++ tailWord_389432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389528 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 4]
def baseStart_389528 : Nat := 118140960795 + 389528 * 2 ^ 59
def prefixEnd_389528 : Nat := 4983230072969 + 3 ^ 40 * 389528 * 2
def baseEnd_389528 : Nat := 44447798307701600801911

theorem tailTrace_389528 : CollatzResearch.WordTrace tailWord_389528 prefixEnd_389528 44447798307701600801911 := by
  unfold tailWord_389528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103626666407028465548619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9471502221876037954064825 7103626666407028465548619)
  ·
    refine ⟨10655439999610542698322929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7103626666407028465548619 10655439999610542698322929)
    ·
      refine ⟨7991579999707907023742197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10655439999610542698322929 7991579999707907023742197)
      ·
        refine ⟨749210624972616283475831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7991579999707907023742197 749210624972616283475831)
        ·
          refine ⟨1123815937458924425213747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749210624972616283475831 1123815937458924425213747)
          ·
            refine ⟨1685723906188386637820621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123815937458924425213747 1685723906188386637820621)
            ·
              refine ⟨632146464820644989182733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1685723906188386637820621 632146464820644989182733)
              ·
                refine ⟨237054924307741870943525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632146464820644989182733 237054924307741870943525)
                ·
                  refine ⟨44447798307701600801911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237054924307741870943525 44447798307701600801911)
                  ·
                    rfl

theorem cell22_389528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_389528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389528 prefixEnd_389528 := by exact prefixLift 389528
  have htrace : WordTrace (prefixWord ++ tailWord_389528) baseStart_389528 baseEnd_389528 := by
    simpa [prefixWord, tailWord_389528, baseEnd_389528] using wordTrace_append hprefix tailTrace_389528
  have hstable : (prefixWord ++ tailWord_389528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389528).length < 2 ^ (prefixWord ++ tailWord_389528).sum := by decide
  have hdescent : baseEnd_389528 < baseStart_389528 := by decide
  rcases family_descends (prefixWord ++ tailWord_389528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389539 : List Nat := [1, 1, 1, 4, 1, 6, 8]
def baseStart_389539 : Nat := 118140960795 + 389539 * 2 ^ 59
def prefixEnd_389539 : Nat := 4983230072969 + 3 ^ 40 * 389539 * 2
def baseEnd_389539 : Nat := 4938783720292757051137

theorem tailTrace_389539 : CollatzResearch.WordTrace tailWord_389539 prefixEnd_389539 4938783720292757051137 := by
  unfold tailWord_389539
  simp only [CollatzResearch.WordTrace]
  refine ⟨14207654535774205809747671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9471769690516137206498447 14207654535774205809747671)
  ·
    refine ⟨21311481803661308714621507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14207654535774205809747671 21311481803661308714621507)
    ·
      refine ⟨31967222705491963071932261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21311481803661308714621507 31967222705491963071932261)
      ·
        refine ⟨5993854257279743075987299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31967222705491963071932261 5993854257279743075987299)
        ·
          refine ⟨8990781385919614613980949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993854257279743075987299 8990781385919614613980949)
          ·
            refine ⟨421442877464981935030357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8990781385919614613980949 421442877464981935030357)
            ·
              refine ⟨4938783720292757051137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 421442877464981935030357 4938783720292757051137)
              ·
                rfl

theorem cell22_389539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 8].length) (baseStart_389539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389539 prefixEnd_389539 := by exact prefixLift 389539
  have htrace : WordTrace (prefixWord ++ tailWord_389539) baseStart_389539 baseEnd_389539 := by
    simpa [prefixWord, tailWord_389539, baseEnd_389539] using wordTrace_append hprefix tailTrace_389539
  have hstable : (prefixWord ++ tailWord_389539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389539).length < 2 ^ (prefixWord ++ tailWord_389539).sum := by decide
  have hdescent : baseEnd_389539 < baseStart_389539 := by decide
  rcases family_descends (prefixWord ++ tailWord_389539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389601 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 5]
def baseStart_389601 : Nat := 118140960795 + 389601 * 2 ^ 59
def prefixEnd_389601 : Nat := 4983230072969 + 3 ^ 40 * 389601 * 2
def baseEnd_389601 : Nat := 44456128104985648443503

theorem tailTrace_389601 : CollatzResearch.WordTrace tailWord_389601 prefixEnd_389601 44456128104985648443503 := by
  unfold tailWord_389601
  simp only [CollatzResearch.WordTrace]
  refine ⟨14209915861549590398504657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9473277241033060265669771 14209915861549590398504657)
  ·
    refine ⟨10657436896162192798878493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14209915861549590398504657 10657436896162192798878493)
    ·
      refine ⟨3996538836060822299579435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10657436896162192798878493 3996538836060822299579435)
      ·
        refine ⟨5994808254091233449369153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996538836060822299579435 5994808254091233449369153)
        ·
          refine ⟨4496106190568425087026865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5994808254091233449369153 4496106190568425087026865)
          ·
            refine ⟨3372079642926318815270149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4496106190568425087026865 3372079642926318815270149)
            ·
              refine ⟨632264933048684777863153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3372079642926318815270149 632264933048684777863153)
              ·
                refine ⟨474198699786513583397365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632264933048684777863153 474198699786513583397365)
                ·
                  refine ⟨44456128104985648443503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 474198699786513583397365 44456128104985648443503)
                  ·
                    rfl

theorem cell22_389601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_389601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389601 prefixEnd_389601 := by exact prefixLift 389601
  have htrace : WordTrace (prefixWord ++ tailWord_389601) baseStart_389601 baseEnd_389601 := by
    simpa [prefixWord, tailWord_389601, baseEnd_389601] using wordTrace_append hprefix tailTrace_389601
  have hstable : (prefixWord ++ tailWord_389601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389601).length < 2 ^ (prefixWord ++ tailWord_389601).sum := by decide
  have hdescent : baseEnd_389601 < baseStart_389601 := by decide
  rcases family_descends (prefixWord ++ tailWord_389601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389631 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 1, 4]
def baseStart_389631 : Nat := 118140960795 + 389631 * 2 ^ 59
def prefixEnd_389631 : Nat := 4983230072969 + 3 ^ 40 * 389631 * 2
def baseEnd_389631 : Nat := 133378653928046867080417

theorem tailTrace_389631 : CollatzResearch.WordTrace tailWord_389631 prefixEnd_389631 133378653928046867080417 := by
  unfold tailWord_389631
  simp only [CollatzResearch.WordTrace]
  refine ⟨14211010051440905522096747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9474006700960603681397831 14211010051440905522096747)
  ·
    refine ⟨21316515077161358283145121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14211010051440905522096747 21316515077161358283145121)
    ·
      refine ⟨15987386307871018712358841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21316515077161358283145121 15987386307871018712358841)
      ·
        refine ⟨11990539730903264034269131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15987386307871018712358841 11990539730903264034269131)
        ·
          refine ⟨17985809596354896051403697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11990539730903264034269131 17985809596354896051403697)
          ·
            refine ⟨13489357197266172038552773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17985809596354896051403697 13489357197266172038552773)
            ·
              refine ⟨2529254474487407257228645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13489357197266172038552773 2529254474487407257228645)
              ·
                refine ⟨474235213966388860730371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2529254474487407257228645 474235213966388860730371)
                ·
                  refine ⟨711352820949583291095557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474235213966388860730371 711352820949583291095557)
                  ·
                    refine ⟨133378653928046867080417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 711352820949583291095557 133378653928046867080417)
                    ·
                      rfl

theorem cell22_389631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_389631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389631 prefixEnd_389631 := by exact prefixLift 389631
  have htrace : WordTrace (prefixWord ++ tailWord_389631) baseStart_389631 baseEnd_389631 := by
    simpa [prefixWord, tailWord_389631, baseEnd_389631] using wordTrace_append hprefix tailTrace_389631
  have hstable : (prefixWord ++ tailWord_389631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389631).length < 2 ^ (prefixWord ++ tailWord_389631).sum := by decide
  have hdescent : baseEnd_389631 < baseStart_389631 := by decide
  rcases family_descends (prefixWord ++ tailWord_389631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389770 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_389770 : Nat := 118140960795 + 389770 * 2 ^ 59
def prefixEnd_389770 : Nat := 4983230072969 + 3 ^ 40 * 389770 * 2
def baseEnd_389770 : Nat := 44475412156232279284997

theorem tailTrace_389770 : CollatzResearch.WordTrace tailWord_389770 prefixEnd_389770 44475412156232279284997 := by
  unfold tailWord_389770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3554019949484333065351691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9477386531958221507604509 3554019949484333065351691)
  ·
    refine ⟨5331029924226499598027537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3554019949484333065351691 5331029924226499598027537)
    ·
      refine ⟨3998272443169874698520653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5331029924226499598027537 3998272443169874698520653)
      ·
        refine ⟨1499352166188703011945245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3998272443169874698520653 1499352166188703011945245)
        ·
          refine ⟨562257062320763629479467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1499352166188703011945245 562257062320763629479467)
          ·
            refine ⟨843385593481145444219201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562257062320763629479467 843385593481145444219201)
            ·
              refine ⟨632539195110859083164401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843385593481145444219201 632539195110859083164401)
              ·
                refine ⟨474404396333144312373301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632539195110859083164401 474404396333144312373301)
                ·
                  refine ⟨44475412156232279284997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 474404396333144312373301 44475412156232279284997)
                  ·
                    rfl

theorem cell22_389770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_389770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389770 prefixEnd_389770 := by exact prefixLift 389770
  have htrace : WordTrace (prefixWord ++ tailWord_389770) baseStart_389770 baseEnd_389770 := by
    simpa [prefixWord, tailWord_389770, baseEnd_389770] using wordTrace_append hprefix tailTrace_389770
  have hstable : (prefixWord ++ tailWord_389770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389770).length < 2 ^ (prefixWord ++ tailWord_389770).sum := by decide
  have hdescent : baseEnd_389770 < baseStart_389770 := by decide
  rcases family_descends (prefixWord ++ tailWord_389770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389847 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 2, 3]
def baseStart_389847 : Nat := 118140960795 + 389847 * 2 ^ 59
def prefixEnd_389847 : Nat := 4983230072969 + 3 ^ 40 * 389847 * 2
def baseEnd_389847 : Nat := 133452595142294303679755

theorem tailTrace_389847 : CollatzResearch.WordTrace tailWord_389847 prefixEnd_389847 133452595142294303679755 := by
  unfold tailWord_389847
  simp only [CollatzResearch.WordTrace]
  refine ⟨14218888218658374411959795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9479258812438916274639863 14218888218658374411959795)
  ·
    refine ⟨21328332327987561617939693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14218888218658374411959795 21328332327987561617939693)
    ·
      refine ⟨7998124622995335606727385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21328332327987561617939693 7998124622995335606727385)
      ·
        refine ⟨5998593467246501705045539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7998124622995335606727385 5998593467246501705045539)
        ·
          refine ⟨8997890200869752557568309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5998593467246501705045539 8997890200869752557568309)
          ·
            refine ⟨843552206331539302272029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8997890200869752557568309 843552206331539302272029)
            ·
              refine ⟨316332077374327238352011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843552206331539302272029 316332077374327238352011)
              ·
                refine ⟨474498116061490857528017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316332077374327238352011 474498116061490857528017)
                ·
                  refine ⟨355873587046118143146013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474498116061490857528017 355873587046118143146013)
                  ·
                    refine ⟨133452595142294303679755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355873587046118143146013 133452595142294303679755)
                    ·
                      rfl

theorem cell22_389847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_389847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389847 prefixEnd_389847 := by exact prefixLift 389847
  have htrace : WordTrace (prefixWord ++ tailWord_389847) baseStart_389847 baseEnd_389847 := by
    simpa [prefixWord, tailWord_389847, baseEnd_389847] using wordTrace_append hprefix tailTrace_389847
  have hstable : (prefixWord ++ tailWord_389847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389847).length < 2 ^ (prefixWord ++ tailWord_389847).sum := by decide
  have hdescent : baseEnd_389847 < baseStart_389847 := by decide
  rcases family_descends (prefixWord ++ tailWord_389847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389860 : List Nat := [2, 3, 1, 1, 1, 6, 2, 6]
def baseStart_389860 : Nat := 118140960795 + 389860 * 2 ^ 59
def prefixEnd_389860 : Nat := 4983230072969 + 3 ^ 40 * 389860 * 2
def baseEnd_389860 : Nat := 14828560589774067011635

theorem tailTrace_389860 : CollatzResearch.WordTrace tailWord_389860 prefixEnd_389860 14828560589774067011635 := by
  unfold tailWord_389860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109681183805638816091517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9479574911740851754788689 7109681183805638816091517)
  ·
    refine ⟨2666130443927114556034319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7109681183805638816091517 2666130443927114556034319)
    ·
      refine ⟨3999195665890671834051479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2666130443927114556034319 3999195665890671834051479)
      ·
        refine ⟨5998793498836007751077219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3999195665890671834051479 5998793498836007751077219)
        ·
          refine ⟨8998190248254011626615829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5998793498836007751077219 8998190248254011626615829)
          ·
            refine ⟨421790167886906794997617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8998190248254011626615829 421790167886906794997617)
            ·
              refine ⟨316342625915180096248213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421790167886906794997617 316342625915180096248213)
              ·
                refine ⟨14828560589774067011635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316342625915180096248213 14828560589774067011635)
                ·
                  rfl

theorem cell22_389860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 6].length) (baseStart_389860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389860 prefixEnd_389860 := by exact prefixLift 389860
  have htrace : WordTrace (prefixWord ++ tailWord_389860) baseStart_389860 baseEnd_389860 := by
    simpa [prefixWord, tailWord_389860, baseEnd_389860] using wordTrace_append hprefix tailTrace_389860
  have hstable : (prefixWord ++ tailWord_389860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389860).length < 2 ^ (prefixWord ++ tailWord_389860).sum := by decide
  have hdescent : baseEnd_389860 < baseStart_389860 := by decide
  rcases family_descends (prefixWord ++ tailWord_389860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389905 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 5]
def baseStart_389905 : Nat := 118140960795 + 389905 * 2 ^ 59
def prefixEnd_389905 : Nat := 4983230072969 + 3 ^ 40 * 389905 * 2
def baseEnd_389905 : Nat := 44490816575867161909859

theorem tailTrace_389905 : CollatzResearch.WordTrace tailWord_389905 prefixEnd_389905 44490816575867161909859 := by
  unfold tailWord_389905
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221003652448250317571169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9480669101632166878380779 14221003652448250317571169)
  ·
    refine ⟨10665752739336187738178377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14221003652448250317571169 10665752739336187738178377)
    ·
      refine ⟨7999314554502140803633783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10665752739336187738178377 7999314554502140803633783)
      ·
        refine ⟨11998971831753211205450675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7999314554502140803633783 11998971831753211205450675)
        ·
          refine ⟨17998457747629816808176013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11998971831753211205450675 17998457747629816808176013)
          ·
            refine ⟨6749421655361181303066005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17998457747629816808176013 6749421655361181303066005)
            ·
              refine ⟨316379140095055373581219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6749421655361181303066005 316379140095055373581219)
              ·
                refine ⟨474568710142583060371829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316379140095055373581219 474568710142583060371829)
                ·
                  refine ⟨44490816575867161909859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 474568710142583060371829 44490816575867161909859)
                  ·
                    rfl

theorem cell22_389905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_389905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389905 prefixEnd_389905 := by exact prefixLift 389905
  have htrace : WordTrace (prefixWord ++ tailWord_389905) baseStart_389905 baseEnd_389905 := by
    simpa [prefixWord, tailWord_389905, baseEnd_389905] using wordTrace_append hprefix tailTrace_389905
  have hstable : (prefixWord ++ tailWord_389905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389905).length < 2 ^ (prefixWord ++ tailWord_389905).sum := by decide
  have hdescent : baseEnd_389905 < baseStart_389905 := by decide
  rcases family_descends (prefixWord ++ tailWord_389905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389948 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_389948 : Nat := 118140960795 + 389948 * 2 ^ 59
def prefixEnd_389948 : Nat := 4983230072969 + 3 ^ 40 * 389948 * 2
def baseEnd_389948 : Nat := 133487169506363706904445

theorem tailTrace_389948 : CollatzResearch.WordTrace tailWord_389948 prefixEnd_389948 133487169506363706904445 := by
  unfold tailWord_389948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111285995646234330693249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9481714660861645774257665 7111285995646234330693249)
  ·
    refine ⟨5333464496734675748019937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7111285995646234330693249 5333464496734675748019937)
    ·
      refine ⟨4000098372551006811014953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5333464496734675748019937 4000098372551006811014953)
      ·
        refine ⟨3000073779413255108261215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4000098372551006811014953 3000073779413255108261215)
        ·
          refine ⟨4500110669119882662391823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000073779413255108261215 4500110669119882662391823)
          ·
            refine ⟨6750166003679823993587735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500110669119882662391823 6750166003679823993587735)
            ·
              refine ⟨10125249005519735990381603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750166003679823993587735 10125249005519735990381603)
              ·
                refine ⟨15187873508279603985572405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10125249005519735990381603 15187873508279603985572405)
                ·
                  refine ⟨1423863141401212873647413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15187873508279603985572405 1423863141401212873647413)
                  ·
                    refine ⟨133487169506363706904445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1423863141401212873647413 133487169506363706904445)
                    ·
                      rfl

theorem cell22_389948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_389948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389948 prefixEnd_389948 := by exact prefixLift 389948
  have htrace : WordTrace (prefixWord ++ tailWord_389948) baseStart_389948 baseEnd_389948 := by
    simpa [prefixWord, tailWord_389948, baseEnd_389948] using wordTrace_append hprefix tailTrace_389948
  have hstable : (prefixWord ++ tailWord_389948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389948).length < 2 ^ (prefixWord ++ tailWord_389948).sum := by decide
  have hdescent : baseEnd_389948 < baseStart_389948 := by decide
  rcases family_descends (prefixWord ++ tailWord_389948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389986 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_389986 : Nat := 118140960795 + 389986 * 2 ^ 59
def prefixEnd_389986 : Nat := 4983230072969 + 3 ^ 40 * 389986 * 2
def baseEnd_389986 : Nat := 133500177682944274454329

theorem tailTrace_389986 : CollatzResearch.WordTrace tailWord_389986 prefixEnd_389986 133500177682944274454329 := by
  unfold tailWord_389986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555989491288700287817453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9482638643436534100846541 3555989491288700287817453)
  ·
    refine ⟨1333496059233262607931545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3555989491288700287817453 1333496059233262607931545)
    ·
      refine ⟨1000122044424946955948659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1333496059233262607931545 1000122044424946955948659)
      ·
        refine ⟨1500183066637420433922989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000122044424946955948659 1500183066637420433922989)
        ·
          refine ⟨562568649989032662721121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1500183066637420433922989 562568649989032662721121)
          ·
            refine ⟨421926487491774497040841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562568649989032662721121 421926487491774497040841)
            ·
              refine ⟨316444865618830872780631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421926487491774497040841 316444865618830872780631)
              ·
                refine ⟨474667298428246309170947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316444865618830872780631 474667298428246309170947)
                ·
                  refine ⟨712000947642369463756421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474667298428246309170947 712000947642369463756421)
                  ·
                    refine ⟨133500177682944274454329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712000947642369463756421 133500177682944274454329)
                    ·
                      rfl

theorem cell22_389986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_389986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_389986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_389986 prefixEnd_389986 := by exact prefixLift 389986
  have htrace : WordTrace (prefixWord ++ tailWord_389986) baseStart_389986 baseEnd_389986 := by
    simpa [prefixWord, tailWord_389986, baseEnd_389986] using wordTrace_append hprefix tailTrace_389986
  have hstable : (prefixWord ++ tailWord_389986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389986).length < 2 ^ (prefixWord ++ tailWord_389986).sum := by decide
  have hdescent : baseEnd_389986 < baseStart_389986 := by decide
  rcases family_descends (prefixWord ++ tailWord_389986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390008 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_390008 : Nat := 118140960795 + 390008 * 2 ^ 59
def prefixEnd_390008 : Nat := 4983230072969 + 3 ^ 40 * 390008 * 2
def baseEnd_390008 : Nat := 133507708732543550404261

theorem tailTrace_390008 : CollatzResearch.WordTrace tailWord_390008 prefixEnd_390008 133507708732543550404261 := by
  unfold tailWord_390008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7112380185537549454285339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9483173580716732605713785 7112380185537549454285339)
  ·
    refine ⟨10668570278306324181428009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7112380185537549454285339 10668570278306324181428009)
    ·
      refine ⟨8001427708729743136071007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10668570278306324181428009 8001427708729743136071007)
      ·
        refine ⟨12002141563094614704106511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001427708729743136071007 12002141563094614704106511)
        ·
          refine ⟨18003212344641922056159767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12002141563094614704106511 18003212344641922056159767)
          ·
            refine ⟨27004818516962883084239651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18003212344641922056159767 27004818516962883084239651)
            ·
              refine ⟨40507227775444324626359477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27004818516962883084239651 40507227775444324626359477)
              ·
                refine ⟨3797552603947905433721201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40507227775444324626359477 3797552603947905433721201)
                ·
                  refine ⟨2848164452960929075290901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797552603947905433721201 2848164452960929075290901)
                  ·
                    refine ⟨133507708732543550404261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2848164452960929075290901 133507708732543550404261)
                    ·
                      rfl

theorem cell22_390008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_390008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390008 prefixEnd_390008 := by exact prefixLift 390008
  have htrace : WordTrace (prefixWord ++ tailWord_390008) baseStart_390008 baseEnd_390008 := by
    simpa [prefixWord, tailWord_390008, baseEnd_390008] using wordTrace_append hprefix tailTrace_390008
  have hstable : (prefixWord ++ tailWord_390008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390008).length < 2 ^ (prefixWord ++ tailWord_390008).sum := by decide
  have hdescent : baseEnd_390008 < baseStart_390008 := by decide
  rcases family_descends (prefixWord ++ tailWord_390008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390087 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 1, 4]
def baseStart_390087 : Nat := 118140960795 + 390087 * 2 ^ 59
def prefixEnd_390087 : Nat := 4983230072969 + 3 ^ 40 * 390087 * 2
def baseEnd_390087 : Nat := 133534752047013677679019

theorem tailTrace_390087 : CollatzResearch.WordTrace tailWord_390087 prefixEnd_390087 133534752047013677679019 := by
  unfold tailWord_390087
  simp only [CollatzResearch.WordTrace]
  refine ⟨14227641737788895400696515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9485094491859263600464343 14227641737788895400696515)
  ·
    refine ⟨21341462606683343101044773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14227641737788895400696515 21341462606683343101044773)
    ·
      refine ⟨4001524238753126831445895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21341462606683343101044773 4001524238753126831445895)
      ·
        refine ⟨6002286358129690247168843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001524238753126831445895 6002286358129690247168843)
        ·
          refine ⟨9003429537194535370753265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002286358129690247168843 9003429537194535370753265)
          ·
            refine ⟨6752572152895901528064949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9003429537194535370753265 6752572152895901528064949)
            ·
              refine ⟨633053639333990768256089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6752572152895901528064949 633053639333990768256089)
              ·
                refine ⟨474790229500493076192067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633053639333990768256089 474790229500493076192067)
                ·
                  refine ⟨712185344250739614288101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474790229500493076192067 712185344250739614288101)
                  ·
                    refine ⟨133534752047013677679019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712185344250739614288101 133534752047013677679019)
                    ·
                      rfl

theorem cell22_390087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_390087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390087 prefixEnd_390087 := by exact prefixLift 390087
  have htrace : WordTrace (prefixWord ++ tailWord_390087) baseStart_390087 baseEnd_390087 := by
    simpa [prefixWord, tailWord_390087, baseEnd_390087] using wordTrace_append hprefix tailTrace_390087
  have hstable : (prefixWord ++ tailWord_390087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390087).length < 2 ^ (prefixWord ++ tailWord_390087).sum := by decide
  have hdescent : baseEnd_390087 < baseStart_390087 := by decide
  rcases family_descends (prefixWord ++ tailWord_390087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390104 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 1, 4]
def baseStart_390104 : Nat := 118140960795 + 390104 * 2 ^ 59
def prefixEnd_390104 : Nat := 4983230072969 + 3 ^ 40 * 390104 * 2
def baseEnd_390104 : Nat := 133540571494431300003967

theorem tailTrace_390104 : CollatzResearch.WordTrace tailWord_390104 prefixEnd_390104 133540571494431300003967 := by
  unfold tailWord_390104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114130889363653652032683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9485507852484871536043577 7114130889363653652032683)
  ·
    refine ⟨10671196334045480478049025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7114130889363653652032683 10671196334045480478049025)
    ·
      refine ⟨8003397250534110358536769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10671196334045480478049025 8003397250534110358536769)
      ·
        refine ⟨6002547937900582768902577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8003397250534110358536769 6002547937900582768902577)
        ·
          refine ⟨4501910953425437076676933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002547937900582768902577 4501910953425437076676933)
          ·
            refine ⟨844108303767269451876925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4501910953425437076676933 844108303767269451876925)
            ·
              refine ⟨316540613912726044453847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 844108303767269451876925 316540613912726044453847)
              ·
                refine ⟨474810920869089066680771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316540613912726044453847 474810920869089066680771)
                ·
                  refine ⟨712216381303633600021157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474810920869089066680771 712216381303633600021157)
                  ·
                    refine ⟨133540571494431300003967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712216381303633600021157 133540571494431300003967)
                    ·
                      rfl

theorem cell22_390104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_390104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390104 prefixEnd_390104 := by exact prefixLift 390104
  have htrace : WordTrace (prefixWord ++ tailWord_390104) baseStart_390104 baseEnd_390104 := by
    simpa [prefixWord, tailWord_390104, baseEnd_390104] using wordTrace_append hprefix tailTrace_390104
  have hstable : (prefixWord ++ tailWord_390104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390104).length < 2 ^ (prefixWord ++ tailWord_390104).sum := by decide
  have hdescent : baseEnd_390104 < baseStart_390104 := by decide
  rcases family_descends (prefixWord ++ tailWord_390104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390119 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 4]
def baseStart_390119 : Nat := 118140960795 + 390119 * 2 ^ 59
def prefixEnd_390119 : Nat := 4983230072969 + 3 ^ 40 * 390119 * 2
def baseEnd_390119 : Nat := 44515235433658753626307

theorem tailTrace_390119 : CollatzResearch.WordTrace tailWord_390119 prefixEnd_390119 44515235433658753626307 := by
  unfold tailWord_390119
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228808873672964865861411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9485872582448643243907607 14228808873672964865861411)
  ·
    refine ⟨21343213310509447298792117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14228808873672964865861411 21343213310509447298792117)
    ·
      refine ⟨2000926247860260684261761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21343213310509447298792117 2000926247860260684261761)
      ·
        refine ⟨1500694685895195513196321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2000926247860260684261761 1500694685895195513196321)
        ·
          refine ⟨1125521014421396634897241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1500694685895195513196321 1125521014421396634897241)
          ·
            refine ⟨844140760816047476172931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125521014421396634897241 844140760816047476172931)
            ·
              refine ⟨1266211141224071214259397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844140760816047476172931 1266211141224071214259397)
              ·
                refine ⟨237414588979513352673637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1266211141224071214259397 237414588979513352673637)
                ·
                  refine ⟨44515235433658753626307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237414588979513352673637 44515235433658753626307)
                  ·
                    rfl

theorem cell22_390119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 4].length) (baseStart_390119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390119 prefixEnd_390119 := by exact prefixLift 390119
  have htrace : WordTrace (prefixWord ++ tailWord_390119) baseStart_390119 baseEnd_390119 := by
    simpa [prefixWord, tailWord_390119, baseEnd_390119] using wordTrace_append hprefix tailTrace_390119
  have hstable : (prefixWord ++ tailWord_390119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390119).length < 2 ^ (prefixWord ++ tailWord_390119).sum := by decide
  have hdescent : baseEnd_390119 < baseStart_390119 := by decide
  rcases family_descends (prefixWord ++ tailWord_390119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390134 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_390134 : Nat := 118140960795 + 390134 * 2 ^ 59
def prefixEnd_390134 : Nat := 4983230072969 + 3 ^ 40 * 390134 * 2
def baseEnd_390134 : Nat := 133550841107521221753875

theorem tailTrace_390134 : CollatzResearch.WordTrace tailWord_390134 prefixEnd_390134 133550841107521221753875 := by
  unfold tailWord_390134
  simp only [CollatzResearch.WordTrace]
  refine ⟨889334748038663901728591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9486237312412414951771637 889334748038663901728591)
  ·
    refine ⟨1334002122057995852592887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889334748038663901728591 1334002122057995852592887)
    ·
      refine ⟨2001003183086993778889331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334002122057995852592887 2001003183086993778889331)
      ·
        refine ⟨3001504774630490668333997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001003183086993778889331 3001504774630490668333997)
        ·
          refine ⟨1125564290486434000625249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3001504774630490668333997 1125564290486434000625249)
          ·
            refine ⟨844173217864825500468937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125564290486434000625249 844173217864825500468937)
            ·
              refine ⟨633129913398619125351703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844173217864825500468937 633129913398619125351703)
              ·
                refine ⟨949694870097928688027555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633129913398619125351703 949694870097928688027555)
                ·
                  refine ⟨1424542305146893032041333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949694870097928688027555 1424542305146893032041333)
                  ·
                    refine ⟨133550841107521221753875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1424542305146893032041333 133550841107521221753875)
                    ·
                      rfl

theorem cell22_390134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_390134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390134 prefixEnd_390134 := by exact prefixLift 390134
  have htrace : WordTrace (prefixWord ++ tailWord_390134) baseStart_390134 baseEnd_390134 := by
    simpa [prefixWord, tailWord_390134, baseEnd_390134] using wordTrace_append hprefix tailTrace_390134
  have hstable : (prefixWord ++ tailWord_390134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390134).length < 2 ^ (prefixWord ++ tailWord_390134).sum := by decide
  have hdescent : baseEnd_390134 < baseStart_390134 := by decide
  rcases family_descends (prefixWord ++ tailWord_390134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390179 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 3, 3]
def baseStart_390179 : Nat := 118140960795 + 390179 * 2 ^ 59
def prefixEnd_390179 : Nat := 4983230072969 + 3 ^ 40 * 390179 * 2
def baseEnd_390179 : Nat := 133566245527156104378737

theorem tailTrace_390179 : CollatzResearch.WordTrace tailWord_390179 prefixEnd_390179 133566245527156104378737 := by
  unfold tailWord_390179
  simp only [CollatzResearch.WordTrace]
  refine ⟨14230997253455595113045591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9487331502303730075363727 14230997253455595113045591)
  ·
    refine ⟨21346495880183392669568387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14230997253455595113045591 21346495880183392669568387)
    ·
      refine ⟨32019743820275089004352581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21346495880183392669568387 32019743820275089004352581)
      ·
        refine ⟨6003701966301579188316109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32019743820275089004352581 6003701966301579188316109)
        ·
          refine ⟨2251388237363092195618541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6003701966301579188316109 2251388237363092195618541)
          ·
            refine ⟨844270589011159573356953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2251388237363092195618541 844270589011159573356953)
            ·
              refine ⟨633202941758369680017715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844270589011159573356953 633202941758369680017715)
              ·
                refine ⟨949804412637554520026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633202941758369680017715 949804412637554520026573)
                ·
                  refine ⟨356176654739082945009965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949804412637554520026573 356176654739082945009965)
                  ·
                    refine ⟨133566245527156104378737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356176654739082945009965 133566245527156104378737)
                    ·
                      rfl

theorem cell22_390179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 3].length) (baseStart_390179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390179 prefixEnd_390179 := by exact prefixLift 390179
  have htrace : WordTrace (prefixWord ++ tailWord_390179) baseStart_390179 baseEnd_390179 := by
    simpa [prefixWord, tailWord_390179, baseEnd_390179] using wordTrace_append hprefix tailTrace_390179
  have hstable : (prefixWord ++ tailWord_390179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390179).length < 2 ^ (prefixWord ++ tailWord_390179).sum := by decide
  have hdescent : baseEnd_390179 < baseStart_390179 := by decide
  rcases family_descends (prefixWord ++ tailWord_390179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390196 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_390196 : Nat := 118140960795 + 390196 * 2 ^ 59
def prefixEnd_390196 : Nat := 4983230072969 + 3 ^ 40 * 390196 * 2
def baseEnd_390196 : Nat := 133572064974573726703685

theorem tailTrace_390196 : CollatzResearch.WordTrace tailWord_390196 prefixEnd_390196 133572064974573726703685 := by
  unfold tailWord_390196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115808647197003508207221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9487744862929338010942961 7115808647197003508207221)
  ·
    refine ⟨667107060674719078894427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7115808647197003508207221 667107060674719078894427)
    ·
      refine ⟨1000660591012078618341641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667107060674719078894427 1000660591012078618341641)
      ·
        refine ⟨750495443259058963756231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1000660591012078618341641 750495443259058963756231)
        ·
          refine ⟨1125743164888588445634347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750495443259058963756231 1125743164888588445634347)
          ·
            refine ⟨1688614747332882668451521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125743164888588445634347 1688614747332882668451521)
            ·
              refine ⟨1266461060499662001338641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1688614747332882668451521 1266461060499662001338641)
              ·
                refine ⟨949845795374746501003981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266461060499662001338641 949845795374746501003981)
                ·
                  refine ⟨356192173265529937876493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949845795374746501003981 356192173265529937876493)
                  ·
                    refine ⟨133572064974573726703685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356192173265529937876493 133572064974573726703685)
                    ·
                      rfl

theorem cell22_390196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_390196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390196 prefixEnd_390196 := by exact prefixLift 390196
  have htrace : WordTrace (prefixWord ++ tailWord_390196) baseStart_390196 baseEnd_390196 := by
    simpa [prefixWord, tailWord_390196, baseEnd_390196] using wordTrace_append hprefix tailTrace_390196
  have hstable : (prefixWord ++ tailWord_390196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390196).length < 2 ^ (prefixWord ++ tailWord_390196).sum := by decide
  have hdescent : baseEnd_390196 < baseStart_390196 := by decide
  rcases family_descends (prefixWord ++ tailWord_390196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390230 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_390230 : Nat := 118140960795 + 390230 * 2 ^ 59
def prefixEnd_390230 : Nat := 4983230072969 + 3 ^ 40 * 390230 * 2
def baseEnd_390230 : Nat := 133583703869408971353581

theorem tailTrace_390230 : CollatzResearch.WordTrace tailWord_390230 prefixEnd_390230 133583703869408971353581 := by
  unfold tailWord_390230
  simp only [CollatzResearch.WordTrace]
  refine ⟨889553586016926926447009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9488571584180553882101429 889553586016926926447009)
  ·
    refine ⟨667165189512695194835257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 889553586016926926447009 667165189512695194835257)
    ·
      refine ⟨500373892134521396126443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 667165189512695194835257 500373892134521396126443)
      ·
        refine ⟨750560838201782094189665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500373892134521396126443 750560838201782094189665)
        ·
          refine ⟨562920628651336570642249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750560838201782094189665 562920628651336570642249)
          ·
            refine ⟨422190471488502427981687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562920628651336570642249 422190471488502427981687)
            ·
              refine ⟨633285707232753641972531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422190471488502427981687 633285707232753641972531)
              ·
                refine ⟨949928560849130462958797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633285707232753641972531 949928560849130462958797)
                ·
                  refine ⟨356223210318423923609549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949928560849130462958797 356223210318423923609549)
                  ·
                    refine ⟨133583703869408971353581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356223210318423923609549 133583703869408971353581)
                    ·
                      rfl

theorem cell22_390230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_390230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390230 prefixEnd_390230 := by exact prefixLift 390230
  have htrace : WordTrace (prefixWord ++ tailWord_390230) baseStart_390230 baseEnd_390230 := by
    simpa [prefixWord, tailWord_390230, baseEnd_390230] using wordTrace_append hprefix tailTrace_390230
  have hstable : (prefixWord ++ tailWord_390230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390230).length < 2 ^ (prefixWord ++ tailWord_390230).sum := by decide
  have hdescent : baseEnd_390230 < baseStart_390230 := by decide
  rcases family_descends (prefixWord ++ tailWord_390230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390252 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_390252 : Nat := 118140960795 + 390252 * 2 ^ 59
def prefixEnd_390252 : Nat := 4983230072969 + 3 ^ 40 * 390252 * 2
def baseEnd_390252 : Nat := 133591234919008247303513

theorem tailTrace_390252 : CollatzResearch.WordTrace tailWord_390252 prefixEnd_390252 133591234919008247303513 := by
  unfold tailWord_390252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116829891095564290226505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9489106521460752386968673 7116829891095564290226505)
  ·
    refine ⟨5337622418321673217669879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7116829891095564290226505 5337622418321673217669879)
    ·
      refine ⟨8006433627482509826504819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5337622418321673217669879 8006433627482509826504819)
      ·
        refine ⟨12009650441223764739757229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8006433627482509826504819 12009650441223764739757229)
        ·
          refine ⟨4503618915458911777408961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12009650441223764739757229 4503618915458911777408961)
          ·
            refine ⟨3377714186594183833056721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503618915458911777408961 3377714186594183833056721)
            ·
              refine ⟨2533285639945637874792541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377714186594183833056721 2533285639945637874792541)
              ·
                refine ⟨949982114979614203047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533285639945637874792541 949982114979614203047203)
                ·
                  refine ⟨1424973172469421304570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949982114979614203047203 1424973172469421304570805)
                  ·
                    refine ⟨133591234919008247303513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1424973172469421304570805 133591234919008247303513)
                    ·
                      rfl

theorem cell22_390252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_390252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390252 prefixEnd_390252 := by exact prefixLift 390252
  have htrace : WordTrace (prefixWord ++ tailWord_390252) baseStart_390252 baseEnd_390252 := by
    simpa [prefixWord, tailWord_390252, baseEnd_390252] using wordTrace_append hprefix tailTrace_390252
  have hstable : (prefixWord ++ tailWord_390252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390252).length < 2 ^ (prefixWord ++ tailWord_390252).sum := by decide
  have hdescent : baseEnd_390252 < baseStart_390252 := by decide
  rcases family_descends (prefixWord ++ tailWord_390252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390286 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_390286 : Nat := 118140960795 + 390286 * 2 ^ 59
def prefixEnd_390286 : Nat := 4983230072969 + 3 ^ 40 * 390286 * 2
def baseEnd_390286 : Nat := 133602873813843491953409

theorem tailTrace_390286 : CollatzResearch.WordTrace tailWord_390286 prefixEnd_390286 133602873813843491953409 := by
  unfold tailWord_390286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779362483008494048398839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9489933242711968258127141 1779362483008494048398839)
  ·
    refine ⟨2669043724512741072598259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779362483008494048398839 2669043724512741072598259)
    ·
      refine ⟨4003565586769111608897389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669043724512741072598259 4003565586769111608897389)
      ·
        refine ⟨1501337095038416853336521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4003565586769111608897389 1501337095038416853336521)
        ·
          refine ⟨1126002821278812640002391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1501337095038416853336521 1126002821278812640002391)
          ·
            refine ⟨1689004231918218960003587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126002821278812640002391 1689004231918218960003587)
            ·
              refine ⟨2533506347877328440005381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689004231918218960003587 2533506347877328440005381)
              ·
                refine ⟨475032440226999082501009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2533506347877328440005381 475032440226999082501009)
                ·
                  refine ⟨356274330170249311875757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 475032440226999082501009 356274330170249311875757)
                  ·
                    refine ⟨133602873813843491953409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356274330170249311875757 133602873813843491953409)
                    ·
                      rfl

theorem cell22_390286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_390286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390286 prefixEnd_390286 := by exact prefixLift 390286
  have htrace : WordTrace (prefixWord ++ tailWord_390286) baseStart_390286 baseEnd_390286 := by
    simpa [prefixWord, tailWord_390286, baseEnd_390286] using wordTrace_append hprefix tailTrace_390286
  have hstable : (prefixWord ++ tailWord_390286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390286).length < 2 ^ (prefixWord ++ tailWord_390286).sum := by decide
  have hdescent : baseEnd_390286 < baseStart_390286 := by decide
  rcases family_descends (prefixWord ++ tailWord_390286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390327 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 7]
def baseStart_390327 : Nat := 118140960795 + 390327 * 2 ^ 59
def prefixEnd_390327 : Nat := 4983230072969 + 3 ^ 40 * 390327 * 2
def baseEnd_390327 : Nat := 44538969650577683892761

theorem tailTrace_390327 : CollatzResearch.WordTrace tailWord_390327 prefixEnd_390327 44538969650577683892761 := by
  unfold tailWord_390327
  simp only [CollatzResearch.WordTrace]
  refine ⟨14236395256919416389433235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9490930171279610926288823 14236395256919416389433235)
  ·
    refine ⟨21354592885379124584149853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14236395256919416389433235 21354592885379124584149853)
    ·
      refine ⟨8007972332017171719056195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21354592885379124584149853 8007972332017171719056195)
      ·
        refine ⟨12011958498025757578584293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007972332017171719056195 12011958498025757578584293)
        ·
          refine ⟨2252242218379829545984555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12011958498025757578584293 2252242218379829545984555)
          ·
            refine ⟨3378363327569744318976833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252242218379829545984555 3378363327569744318976833)
            ·
              refine ⟨2533772495677308239232625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378363327569744318976833 2533772495677308239232625)
              ·
                refine ⟨1900329371757981179424469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533772495677308239232625 1900329371757981179424469)
                ·
                  refine ⟨44538969650577683892761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1900329371757981179424469 44538969650577683892761)
                  ·
                    rfl

theorem cell22_390327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_390327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390327 prefixEnd_390327 := by exact prefixLift 390327
  have htrace : WordTrace (prefixWord ++ tailWord_390327) baseStart_390327 baseEnd_390327 := by
    simpa [prefixWord, tailWord_390327, baseEnd_390327] using wordTrace_append hprefix tailTrace_390327
  have hstable : (prefixWord ++ tailWord_390327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390327).length < 2 ^ (prefixWord ++ tailWord_390327).sum := by decide
  have hdescent : baseEnd_390327 < baseStart_390327 := by decide
  rcases family_descends (prefixWord ++ tailWord_390327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390344 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_390344 : Nat := 118140960795 + 390344 * 2 ^ 59
def prefixEnd_390344 : Nat := 4983230072969 + 3 ^ 40 * 390344 * 2
def baseEnd_390344 : Nat := 44540909466383558001077

theorem tailTrace_390344 : CollatzResearch.WordTrace tailWord_390344 prefixEnd_390344 44540909466383558001077 := by
  unfold tailWord_390344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118507648928914146401043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9491343531905218861868057 7118507648928914146401043)
  ·
    refine ⟨10677761473393371219601565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7118507648928914146401043 10677761473393371219601565)
    ·
      refine ⟨4004160552522514207350587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10677761473393371219601565 4004160552522514207350587)
      ·
        refine ⟨6006240828783771311025881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004160552522514207350587 6006240828783771311025881)
        ·
          refine ⟨4504680621587828483269411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6006240828783771311025881 4504680621587828483269411)
          ·
            refine ⟨6757020932381742724904117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504680621587828483269411 6757020932381742724904117)
            ·
              refine ⟨633470712410788380459761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6757020932381742724904117 633470712410788380459761)
              ·
                refine ⟨475103034308091285344821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633470712410788380459761 475103034308091285344821)
                ·
                  refine ⟨44540909466383558001077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 475103034308091285344821 44540909466383558001077)
                  ·
                    rfl

theorem cell22_390344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_390344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390344 prefixEnd_390344 := by exact prefixLift 390344
  have htrace : WordTrace (prefixWord ++ tailWord_390344) baseStart_390344 baseEnd_390344 := by
    simpa [prefixWord, tailWord_390344, baseEnd_390344] using wordTrace_append hprefix tailTrace_390344
  have hstable : (prefixWord ++ tailWord_390344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390344).length < 2 ^ (prefixWord ++ tailWord_390344).sum := by decide
  have hdescent : baseEnd_390344 < baseStart_390344 := by decide
  rcases family_descends (prefixWord ++ tailWord_390344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390436 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_390436 : Nat := 118140960795 + 390436 * 2 ^ 59
def prefixEnd_390436 : Nat := 4983230072969 + 3 ^ 40 * 390436 * 2
def baseEnd_390436 : Nat := 133654221879293100702949

theorem tailTrace_390436 : CollatzResearch.WordTrace tailWord_390436 prefixEnd_390436 133654221879293100702949 := by
  unfold tailWord_390436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120185406762264002575581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9493580542349685336767441 7120185406762264002575581)
  ·
    refine ⟨2670069527535849000965843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7120185406762264002575581 2670069527535849000965843)
    ·
      refine ⟨4005104291303773501448765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670069527535849000965843 4005104291303773501448765)
      ·
        refine ⟨1501914109238915063043287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4005104291303773501448765 1501914109238915063043287)
        ·
          refine ⟨2252871163858372594564931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501914109238915063043287 2252871163858372594564931)
          ·
            refine ⟨3379306745787558891847397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252871163858372594564931 3379306745787558891847397)
            ·
              refine ⟨633620014835167292221387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3379306745787558891847397 633620014835167292221387)
              ·
                refine ⟨950430022252750938332081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633620014835167292221387 950430022252750938332081)
                ·
                  refine ⟨712822516689563203749061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 950430022252750938332081 712822516689563203749061)
                  ·
                    refine ⟨133654221879293100702949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712822516689563203749061 133654221879293100702949)
                    ·
                      rfl

theorem cell22_390436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_390436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390436 prefixEnd_390436 := by exact prefixLift 390436
  have htrace : WordTrace (prefixWord ++ tailWord_390436) baseStart_390436 baseEnd_390436 := by
    simpa [prefixWord, tailWord_390436, baseEnd_390436] using wordTrace_append hprefix tailTrace_390436
  have hstable : (prefixWord ++ tailWord_390436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390436).length < 2 ^ (prefixWord ++ tailWord_390436).sum := by decide
  have hdescent : baseEnd_390436 < baseStart_390436 := by decide
  rcases family_descends (prefixWord ++ tailWord_390436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390457 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 4]
def baseStart_390457 : Nat := 118140960795 + 390457 * 2 ^ 59
def prefixEnd_390457 : Nat := 4983230072969 + 3 ^ 40 * 390457 * 2
def baseEnd_390457 : Nat := 44553803536152015309295

theorem tailTrace_390457 : CollatzResearch.WordTrace tailWord_390457 prefixEnd_390457 44553803536152015309295 := by
  unfold tailWord_390457
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241136746448448591665625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9494091164298965727777083 14241136746448448591665625)
  ·
    refine ⟨10680852559836336443749219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14241136746448448591665625 10680852559836336443749219)
    ·
      refine ⟨16021278839754504665623829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10680852559836336443749219 16021278839754504665623829)
      ·
        refine ⟨750997445613492406201117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16021278839754504665623829 750997445613492406201117)
        ·
          refine ⟨281624042105059652325419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750997445613492406201117 281624042105059652325419)
          ·
            refine ⟨422436063157589478488129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281624042105059652325419 422436063157589478488129)
            ·
              refine ⟨316827047368192108866097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422436063157589478488129 316827047368192108866097)
              ·
                refine ⟨237620285526144081649573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316827047368192108866097 237620285526144081649573)
                ·
                  refine ⟨44553803536152015309295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237620285526144081649573 44553803536152015309295)
                  ·
                    rfl

theorem cell22_390457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_390457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390457 prefixEnd_390457 := by exact prefixLift 390457
  have htrace : WordTrace (prefixWord ++ tailWord_390457) baseStart_390457 baseEnd_390457 := by
    simpa [prefixWord, tailWord_390457, baseEnd_390457] using wordTrace_append hprefix tailTrace_390457
  have hstable : (prefixWord ++ tailWord_390457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390457).length < 2 ^ (prefixWord ++ tailWord_390457).sum := by decide
  have hdescent : baseEnd_390457 < baseStart_390457 := by decide
  rcases family_descends (prefixWord ++ tailWord_390457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390468 : List Nat := [2, 3, 4, 1, 1, 3, 1, 7]
def baseStart_390468 : Nat := 118140960795 + 390468 * 2 ^ 59
def prefixEnd_390468 : Nat := 4983230072969 + 3 ^ 40 * 390468 * 2
def baseEnd_390468 : Nat := 14851686237028409322539

theorem tailTrace_390468 : CollatzResearch.WordTrace tailWord_390468 prefixEnd_390468 14851686237028409322539 := by
  unfold tailWord_390468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120768974704298735158029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9494358632939064980210705 7120768974704298735158029)
  ·
    refine ⟨2670288365514112025684261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7120768974704298735158029 2670288365514112025684261)
    ·
      refine ⟨500679068533896004815799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2670288365514112025684261 500679068533896004815799)
      ·
        refine ⟨751018602800844007223699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500679068533896004815799 751018602800844007223699)
        ·
          refine ⟨1126527904201266010835549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751018602800844007223699 1126527904201266010835549)
          ·
            refine ⟨422447964075474754063331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1126527904201266010835549 422447964075474754063331)
            ·
              refine ⟨633671946113212131094997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422447964075474754063331 633671946113212131094997)
              ·
                refine ⟨14851686237028409322539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 633671946113212131094997 14851686237028409322539)
                ·
                  rfl

theorem cell22_390468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 7].length) (baseStart_390468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390468 prefixEnd_390468 := by exact prefixLift 390468
  have htrace : WordTrace (prefixWord ++ tailWord_390468) baseStart_390468 baseEnd_390468 := by
    simpa [prefixWord, tailWord_390468, baseEnd_390468] using wordTrace_append hprefix tailTrace_390468
  have hstable : (prefixWord ++ tailWord_390468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390468).length < 2 ^ (prefixWord ++ tailWord_390468).sum := by decide
  have hdescent : baseEnd_390468 < baseStart_390468 := by decide
  rcases family_descends (prefixWord ++ tailWord_390468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390500 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_390500 : Nat := 118140960795 + 390500 * 2 ^ 59
def prefixEnd_390500 : Nat := 4983230072969 + 3 ^ 40 * 390500 * 2
def baseEnd_390500 : Nat := 133676130387218267102753

theorem tailTrace_390500 : CollatzResearch.WordTrace tailWord_390500 prefixEnd_390500 133676130387218267102753 := by
  unfold tailWord_390500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121352542646333467740477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9495136723528444623653969 7121352542646333467740477)
  ·
    refine ⟨2670507203492375050402679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7121352542646333467740477 2670507203492375050402679)
    ·
      refine ⟨4005760805238562575604019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670507203492375050402679 4005760805238562575604019)
      ·
        refine ⟨6008641207857843863406029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005760805238562575604019 6008641207857843863406029)
        ·
          refine ⟨2253240452946691448777261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6008641207857843863406029 2253240452946691448777261)
          ·
            refine ⟨844965169855009293291473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2253240452946691448777261 844965169855009293291473)
            ·
              refine ⟨633723877391256969968605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844965169855009293291473 633723877391256969968605)
              ·
                refine ⟨237646454021721363738227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633723877391256969968605 237646454021721363738227)
                ·
                  refine ⟨356469681032582045607341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237646454021721363738227 356469681032582045607341)
                  ·
                    refine ⟨133676130387218267102753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356469681032582045607341 133676130387218267102753)
                    ·
                      rfl

theorem cell22_390500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_390500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390500 prefixEnd_390500 := by exact prefixLift 390500
  have htrace : WordTrace (prefixWord ++ tailWord_390500) baseStart_390500 baseEnd_390500 := by
    simpa [prefixWord, tailWord_390500, baseEnd_390500] using wordTrace_append hprefix tailTrace_390500
  have hstable : (prefixWord ++ tailWord_390500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390500).length < 2 ^ (prefixWord ++ tailWord_390500).sum := by decide
  have hdescent : baseEnd_390500 < baseStart_390500 := by decide
  rcases family_descends (prefixWord ++ tailWord_390500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390594 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_390594 : Nat := 118140960795 + 390594 * 2 ^ 59
def prefixEnd_390594 : Nat := 4983230072969 + 3 ^ 40 * 390594 * 2
def baseEnd_390594 : Nat := 133708308508233355252465

theorem tailTrace_390594 : CollatzResearch.WordTrace tailWord_390594 prefixEnd_390594 133708308508233355252465 := by
  unfold tailWord_390594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561533386738030247350709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9497422364634747326268557 3561533386738030247350709)
  ·
    refine ⟨333893755006690335689129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3561533386738030247350709 333893755006690335689129)
    ·
      refine ⟨250420316255017751766847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333893755006690335689129 250420316255017751766847)
      ·
        refine ⟨375630474382526627650271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250420316255017751766847 375630474382526627650271)
        ·
          refine ⟨563445711573789941475407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375630474382526627650271 563445711573789941475407)
          ·
            refine ⟨845168567360684912213111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563445711573789941475407 845168567360684912213111)
            ·
              refine ⟨1267752851041027368319667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845168567360684912213111 1267752851041027368319667)
              ·
                refine ⟨1901629276561541052479501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267752851041027368319667 1901629276561541052479501)
                ·
                  refine ⟨713110978710577894679813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1901629276561541052479501 713110978710577894679813)
                  ·
                    refine ⟨133708308508233355252465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 713110978710577894679813 133708308508233355252465)
                    ·
                      rfl

theorem cell22_390594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_390594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390594 prefixEnd_390594 := by exact prefixLift 390594
  have htrace : WordTrace (prefixWord ++ tailWord_390594) baseStart_390594 baseEnd_390594 := by
    simpa [prefixWord, tailWord_390594, baseEnd_390594] using wordTrace_append hprefix tailTrace_390594
  have hstable : (prefixWord ++ tailWord_390594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390594).length < 2 ^ (prefixWord ++ tailWord_390594).sum := by decide
  have hdescent : baseEnd_390594 < baseStart_390594 := by decide
  rcases family_descends (prefixWord ++ tailWord_390594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390601 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_390601 : Nat := 118140960795 + 390601 * 2 ^ 59
def prefixEnd_390601 : Nat := 4983230072969 + 3 ^ 40 * 390601 * 2
def baseEnd_390601 : Nat := 133710704751287670327443

theorem tailTrace_390601 : CollatzResearch.WordTrace tailWord_390601 prefixEnd_390601 133710704751287670327443 := by
  unfold tailWord_390601
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246388857926761184907657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9497592571951174123271771 14246388857926761184907657)
  ·
    refine ⟨10684791643445070888680743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14246388857926761184907657 10684791643445070888680743)
    ·
      refine ⟨16027187465167606333021115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10684791643445070888680743 16027187465167606333021115)
      ·
        refine ⟨24040781197751409499531673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16027187465167606333021115 24040781197751409499531673)
        ·
          refine ⟨18030585898313557124648755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24040781197751409499531673 18030585898313557124648755)
          ·
            refine ⟨27045878847470335686973133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18030585898313557124648755 27045878847470335686973133)
            ·
              refine ⟨10142204567801375882614925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27045878847470335686973133 10142204567801375882614925)
              ·
                refine ⟨3803326712925515955980597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10142204567801375882614925 3803326712925515955980597)
                ·
                  refine ⟨356561879336767120873181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803326712925515955980597 356561879336767120873181)
                  ·
                    refine ⟨133710704751287670327443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356561879336767120873181 133710704751287670327443)
                    ·
                      rfl

theorem cell22_390601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_390601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390601 prefixEnd_390601 := by exact prefixLift 390601
  have htrace : WordTrace (prefixWord ++ tailWord_390601) baseStart_390601 baseEnd_390601 := by
    simpa [prefixWord, tailWord_390601, baseEnd_390601] using wordTrace_append hprefix tailTrace_390601
  have hstable : (prefixWord ++ tailWord_390601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390601).length < 2 ^ (prefixWord ++ tailWord_390601).sum := by decide
  have hdescent : baseEnd_390601 < baseStart_390601 := by decide
  rcases family_descends (prefixWord ++ tailWord_390601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390686 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_390686 : Nat := 118140960795 + 390686 * 2 ^ 59
def prefixEnd_390686 : Nat := 4983230072969 + 3 ^ 40 * 390686 * 2
def baseEnd_390686 : Nat := 133739801988375781952183

theorem tailTrace_390686 : CollatzResearch.WordTrace tailWord_390686 prefixEnd_390686 133739801988375781952183 := by
  unfold tailWord_390686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1781186132827352587718989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9499659375079213801167941 1781186132827352587718989)
  ·
    refine ⟨667944799810257220394621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1781186132827352587718989 667944799810257220394621)
    ·
      refine ⟨250479299928846457647983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 667944799810257220394621 250479299928846457647983)
      ·
        refine ⟨375718949893269686471975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250479299928846457647983 375718949893269686471975)
        ·
          refine ⟨563578424839904529707963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375718949893269686471975 563578424839904529707963)
          ·
            refine ⟨845367637259856794561945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563578424839904529707963 845367637259856794561945)
            ·
              refine ⟨634025727944892595921459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845367637259856794561945 634025727944892595921459)
              ·
                refine ⟨951038591917338893882189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634025727944892595921459 951038591917338893882189)
                ·
                  refine ⟨356639471969002085205821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951038591917338893882189 356639471969002085205821)
                  ·
                    refine ⟨133739801988375781952183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356639471969002085205821 133739801988375781952183)
                    ·
                      rfl

theorem cell22_390686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_390686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390686 prefixEnd_390686 := by exact prefixLift 390686
  have htrace : WordTrace (prefixWord ++ tailWord_390686) baseStart_390686 baseEnd_390686 := by
    simpa [prefixWord, tailWord_390686, baseEnd_390686] using wordTrace_append hprefix tailTrace_390686
  have hstable : (prefixWord ++ tailWord_390686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390686).length < 2 ^ (prefixWord ++ tailWord_390686).sum := by decide
  have hdescent : baseEnd_390686 < baseStart_390686 := by decide
  rcases family_descends (prefixWord ++ tailWord_390686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390727 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 4]
def baseStart_390727 : Nat := 118140960795 + 390727 * 2 ^ 59
def prefixEnd_390727 : Nat := 4983230072969 + 3 ^ 40 * 390727 * 2
def baseEnd_390727 : Nat := 44584612375421780559019

theorem tailTrace_390727 : CollatzResearch.WordTrace tailWord_390727 prefixEnd_390727 44584612375421780559019 := by
  unfold tailWord_390727
  simp only [CollatzResearch.WordTrace]
  refine ⟨14250984455470284703994435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9500656303646856469329623 14250984455470284703994435)
  ·
    refine ⟨21376476683205427055991653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14250984455470284703994435 21376476683205427055991653)
    ·
      refine ⟨4008089378101017572998435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21376476683205427055991653 4008089378101017572998435)
      ·
        refine ⟨6012134067151526359497653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4008089378101017572998435 6012134067151526359497653)
        ·
          refine ⟨563637568795455596202905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6012134067151526359497653 563637568795455596202905)
          ·
            refine ⟨422728176596591697152179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563637568795455596202905 422728176596591697152179)
            ·
              refine ⟨634092264894887545728269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422728176596591697152179 634092264894887545728269)
              ·
                refine ⟨237784599335582829648101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 634092264894887545728269 237784599335582829648101)
                ·
                  refine ⟨44584612375421780559019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237784599335582829648101 44584612375421780559019)
                  ·
                    rfl

theorem cell22_390727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 4].length) (baseStart_390727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390727 prefixEnd_390727 := by exact prefixLift 390727
  have htrace : WordTrace (prefixWord ++ tailWord_390727) baseStart_390727 baseEnd_390727 := by
    simpa [prefixWord, tailWord_390727, baseEnd_390727] using wordTrace_append hprefix tailTrace_390727
  have hstable : (prefixWord ++ tailWord_390727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390727).length < 2 ^ (prefixWord ++ tailWord_390727).sum := by decide
  have hdescent : baseEnd_390727 < baseStart_390727 := by decide
  rcases family_descends (prefixWord ++ tailWord_390727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390738 : List Nat := [3, 2, 2, 1, 2, 4, 8]
def baseStart_390738 : Nat := 118140960795 + 390738 * 2 ^ 59
def prefixEnd_390738 : Nat := 4983230072969 + 3 ^ 40 * 390738 * 2
def baseEnd_390738 : Nat := 4953985283372777024149

theorem tailTrace_390738 : CollatzResearch.WordTrace tailWord_390738 prefixEnd_390738 4953985283372777024149 := by
  unfold tailWord_390738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562846414607608395661217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9500923772286955721763245 3562846414607608395661217)
  ·
    refine ⟨2672134810955706296745913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3562846414607608395661217 2672134810955706296745913)
    ·
      refine ⟨2004101108216779722559435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2672134810955706296745913 2004101108216779722559435)
      ·
        refine ⟨3006151662325169583839153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004101108216779722559435 3006151662325169583839153)
        ·
          refine ⟨2254613746743877187879365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3006151662325169583839153 2254613746743877187879365)
          ·
            refine ⟨422740077514476972727381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2254613746743877187879365 422740077514476972727381)
            ·
              refine ⟨4953985283372777024149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 422740077514476972727381 4953985283372777024149)
              ·
                rfl

theorem cell22_390738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 8].length) (baseStart_390738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390738 prefixEnd_390738 := by exact prefixLift 390738
  have htrace : WordTrace (prefixWord ++ tailWord_390738) baseStart_390738 baseEnd_390738 := by
    simpa [prefixWord, tailWord_390738, baseEnd_390738] using wordTrace_append hprefix tailTrace_390738
  have hstable : (prefixWord ++ tailWord_390738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390738).length < 2 ^ (prefixWord ++ tailWord_390738).sum := by decide
  have hdescent : baseEnd_390738 < baseStart_390738 := by decide
  rcases family_descends (prefixWord ++ tailWord_390738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390890 : List Nat := [3, 1, 3, 1, 1, 1, 6, 6]
def baseStart_390890 : Nat := 118140960795 + 390890 * 2 ^ 59
def prefixEnd_390890 : Nat := 4983230072969 + 3 ^ 40 * 390890 * 2
def baseEnd_390890 : Nat := 14867737261931916650173

theorem tailTrace_390890 : CollatzResearch.WordTrace tailWord_390890 prefixEnd_390890 14867737261931916650173 := by
  unfold tailWord_390890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3564232388469940885544531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9504619702586509028118749 3564232388469940885544531)
  ·
    refine ⟨5346348582704911328316797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3564232388469940885544531 5346348582704911328316797)
    ·
      refine ⟨2004880718514341748118799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5346348582704911328316797 2004880718514341748118799)
      ·
        refine ⟨3007321077771512622178199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004880718514341748118799 3007321077771512622178199)
        ·
          refine ⟨4510981616657268933267299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007321077771512622178199 4510981616657268933267299)
          ·
            refine ⟨6766472424985903399900949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510981616657268933267299 6766472424985903399900949)
            ·
              refine ⟨317178394921214221870357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6766472424985903399900949 317178394921214221870357)
              ·
                refine ⟨14867737261931916650173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 317178394921214221870357 14867737261931916650173)
                ·
                  rfl

theorem cell22_390890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_390890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390890 prefixEnd_390890 := by exact prefixLift 390890
  have htrace : WordTrace (prefixWord ++ tailWord_390890) baseStart_390890 baseEnd_390890 := by
    simpa [prefixWord, tailWord_390890, baseEnd_390890] using wordTrace_append hprefix tailTrace_390890
  have hstable : (prefixWord ++ tailWord_390890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390890).length < 2 ^ (prefixWord ++ tailWord_390890).sum := by decide
  have hdescent : baseEnd_390890 < baseStart_390890 := by decide
  rcases family_descends (prefixWord ++ tailWord_390890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390922 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_390922 : Nat := 118140960795 + 390922 * 2 ^ 59
def prefixEnd_390922 : Nat := 4983230072969 + 3 ^ 40 * 390922 * 2
def baseEnd_390922 : Nat := 133820589611349833051459

theorem tailTrace_390922 : CollatzResearch.WordTrace tailWord_390922 prefixEnd_390922 133820589611349833051459 := by
  unfold tailWord_390922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3564524172440958251835755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9505397793175888671562013 3564524172440958251835755)
  ·
    refine ⟨5346786258661437377753633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3564524172440958251835755 5346786258661437377753633)
    ·
      refine ⟨4010089693996078033315225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5346786258661437377753633 4010089693996078033315225)
      ·
        refine ⟨3007567270497058524986419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4010089693996078033315225 3007567270497058524986419)
        ·
          refine ⟨4511350905745587787479629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007567270497058524986419 4511350905745587787479629)
          ·
            refine ⟨1691756589654595420304861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4511350905745587787479629 1691756589654595420304861)
            ·
              refine ⟨634408721120473282614323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1691756589654595420304861 634408721120473282614323)
              ·
                refine ⟨951613081680709923921485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634408721120473282614323 951613081680709923921485)
                ·
                  refine ⟨356854905630266221470557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951613081680709923921485 356854905630266221470557)
                  ·
                    refine ⟨133820589611349833051459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356854905630266221470557 133820589611349833051459)
                    ·
                      rfl

theorem cell22_390922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_390922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390922 prefixEnd_390922 := by exact prefixLift 390922
  have htrace : WordTrace (prefixWord ++ tailWord_390922) baseStart_390922 baseEnd_390922 := by
    simpa [prefixWord, tailWord_390922, baseEnd_390922] using wordTrace_append hprefix tailTrace_390922
  have hstable : (prefixWord ++ tailWord_390922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390922).length < 2 ^ (prefixWord ++ tailWord_390922).sum := by decide
  have hdescent : baseEnd_390922 < baseStart_390922 := by decide
  rcases family_descends (prefixWord ++ tailWord_390922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390969 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 5]
def baseStart_390969 : Nat := 118140960795 + 390969 * 2 ^ 59
def prefixEnd_390969 : Nat := 4983230072969 + 3 ^ 40 * 390969 * 2
def baseEnd_390969 : Nat := 44612226223952459042105

theorem tailTrace_390969 : CollatzResearch.WordTrace tailWord_390969 prefixEnd_390969 44612226223952459042105 := by
  unfold tailWord_390969
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259810920593560034303961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9506540613729040022869307 14259810920593560034303961)
  ·
    refine ⟨10694858190445170025727971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14259810920593560034303961 10694858190445170025727971)
    ·
      refine ⟨16042287285667755038591957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10694858190445170025727971 16042287285667755038591957)
      ·
        refine ⟨375991108257838008716999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16042287285667755038591957 375991108257838008716999)
        ·
          refine ⟨563986662386757013075499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375991108257838008716999 563986662386757013075499)
          ·
            refine ⟨845979993580135519613249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563986662386757013075499 845979993580135519613249)
            ·
              refine ⟨634484995185101639709937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845979993580135519613249 634484995185101639709937)
              ·
                refine ⟨475863746388826229782453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634484995185101639709937 475863746388826229782453)
                ·
                  refine ⟨44612226223952459042105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 475863746388826229782453 44612226223952459042105)
                  ·
                    rfl

theorem cell22_390969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_390969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390969 prefixEnd_390969 := by exact prefixLift 390969
  have htrace : WordTrace (prefixWord ++ tailWord_390969) baseStart_390969 baseEnd_390969 := by
    simpa [prefixWord, tailWord_390969, baseEnd_390969] using wordTrace_append hprefix tailTrace_390969
  have hstable : (prefixWord ++ tailWord_390969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390969).length < 2 ^ (prefixWord ++ tailWord_390969).sum := by decide
  have hdescent : baseEnd_390969 < baseStart_390969 := by decide
  rcases family_descends (prefixWord ++ tailWord_390969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390973 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_390973 : Nat := 118140960795 + 390973 * 2 ^ 59
def prefixEnd_390973 : Nat := 4983230072969 + 3 ^ 40 * 390973 * 2
def baseEnd_390973 : Nat := 133838047953602700026303

theorem tailTrace_390973 : CollatzResearch.WordTrace tailWord_390973 prefixEnd_390973 133838047953602700026303 := by
  unfold tailWord_390973
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259956812579068717449573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9506637875052712478299715 14259956812579068717449573)
  ·
    refine ⟨2673741902358575384521795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14259956812579068717449573 2673741902358575384521795)
    ·
      refine ⟨4010612853537863076782693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673741902358575384521795 4010612853537863076782693)
      ·
        refine ⟨751989910038349326896755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4010612853537863076782693 751989910038349326896755)
        ·
          refine ⟨1127984865057523990345133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751989910038349326896755 1127984865057523990345133)
          ·
            refine ⟨422994324396571496379425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1127984865057523990345133 422994324396571496379425)
            ·
              refine ⟨317245743297428622284569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422994324396571496379425 317245743297428622284569)
              ·
                refine ⟨237934307473071466713427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317245743297428622284569 237934307473071466713427)
                ·
                  refine ⟨356901461209607200070141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237934307473071466713427 356901461209607200070141)
                  ·
                    refine ⟨133838047953602700026303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356901461209607200070141 133838047953602700026303)
                    ·
                      rfl

theorem cell22_390973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_390973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390973 prefixEnd_390973 := by exact prefixLift 390973
  have htrace : WordTrace (prefixWord ++ tailWord_390973) baseStart_390973 baseEnd_390973 := by
    simpa [prefixWord, tailWord_390973, baseEnd_390973] using wordTrace_append hprefix tailTrace_390973
  have hstable : (prefixWord ++ tailWord_390973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390973).length < 2 ^ (prefixWord ++ tailWord_390973).sum := by decide
  have hdescent : baseEnd_390973 < baseStart_390973 := by decide
  rcases family_descends (prefixWord ++ tailWord_390973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390995 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 8, 3]
def baseStart_390995 : Nat := 118140960795 + 390995 * 2 ^ 59
def prefixEnd_390995 : Nat := 4983230072969 + 3 ^ 40 * 390995 * 2
def baseEnd_390995 : Nat := 133845579003201975976235

theorem tailTrace_390995 : CollatzResearch.WordTrace tailWord_390995 prefixEnd_390995 133845579003201975976235 := by
  unfold tailWord_390995
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260759218499366474750439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9507172812332910983166959 14260759218499366474750439)
  ·
    refine ⟨21391138827749049712125659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14260759218499366474750439 21391138827749049712125659)
    ·
      refine ⟨32086708241623574568188489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21391138827749049712125659 32086708241623574568188489)
      ·
        refine ⟨24065031181217680926141367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32086708241623574568188489 24065031181217680926141367)
        ·
          refine ⟨36097546771826521389212051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24065031181217680926141367 36097546771826521389212051)
          ·
            refine ⟨54146320157739782083818077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36097546771826521389212051 54146320157739782083818077)
            ·
              refine ⟨20304870059152418281431779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54146320157739782083818077 20304870059152418281431779)
              ·
                refine ⟨30457305088728627422147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20304870059152418281431779 30457305088728627422147669)
                ·
                  refine ⟨356921544008538602603293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30457305088728627422147669 356921544008538602603293)
                  ·
                    refine ⟨133845579003201975976235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356921544008538602603293 133845579003201975976235)
                    ·
                      rfl

theorem cell22_390995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 3].length) (baseStart_390995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_390995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_390995 prefixEnd_390995 := by exact prefixLift 390995
  have htrace : WordTrace (prefixWord ++ tailWord_390995) baseStart_390995 baseEnd_390995 := by
    simpa [prefixWord, tailWord_390995, baseEnd_390995] using wordTrace_append hprefix tailTrace_390995
  have hstable : (prefixWord ++ tailWord_390995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390995).length < 2 ^ (prefixWord ++ tailWord_390995).sum := by decide
  have hdescent : baseEnd_390995 < baseStart_390995 := by decide
  rcases family_descends (prefixWord ++ tailWord_390995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391057 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_391057 : Nat := 118140960795 + 391057 * 2 ^ 59
def prefixEnd_391057 : Nat := 4983230072969 + 3 ^ 40 * 391057 * 2
def baseEnd_391057 : Nat := 133866802870254480926045

theorem tailTrace_391057 : CollatzResearch.WordTrace tailWord_391057 prefixEnd_391057 133866802870254480926045 := by
  unfold tailWord_391057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263020544274751063507425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9508680362849834042338283 14263020544274751063507425)
  ·
    refine ⟨10697265408206063297630569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14263020544274751063507425 10697265408206063297630569)
    ·
      refine ⟨8022949056154547473222927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10697265408206063297630569 8022949056154547473222927)
      ·
        refine ⟨12034423584231821209834391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022949056154547473222927 12034423584231821209834391)
        ·
          refine ⟨18051635376347731814751587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12034423584231821209834391 18051635376347731814751587)
          ·
            refine ⟨27077453064521597722127381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18051635376347731814751587 27077453064521597722127381)
            ·
              refine ⟨1269255612399449893224721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27077453064521597722127381 1269255612399449893224721)
              ·
                refine ⟨951941709299587419918541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269255612399449893224721 951941709299587419918541)
                ·
                  refine ⟨356978140987345282469453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951941709299587419918541 356978140987345282469453)
                  ·
                    refine ⟨133866802870254480926045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356978140987345282469453 133866802870254480926045)
                    ·
                      rfl

theorem cell22_391057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_391057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391057 prefixEnd_391057 := by exact prefixLift 391057
  have htrace : WordTrace (prefixWord ++ tailWord_391057) baseStart_391057 baseEnd_391057 := by
    simpa [prefixWord, tailWord_391057, baseEnd_391057] using wordTrace_append hprefix tailTrace_391057
  have hstable : (prefixWord ++ tailWord_391057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391057).length < 2 ^ (prefixWord ++ tailWord_391057).sum := by decide
  have hdescent : baseEnd_391057 < baseStart_391057 := by decide
  rcases family_descends (prefixWord ++ tailWord_391057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391091 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 1, 3]
def baseStart_391091 : Nat := 118140960795 + 391091 * 2 ^ 59
def prefixEnd_391091 : Nat := 4983230072969 + 3 ^ 40 * 391091 * 2
def baseEnd_391091 : Nat := 133878441765089725575941

theorem tailTrace_391091 : CollatzResearch.WordTrace tailWord_391091 prefixEnd_391091 133878441765089725575941 := by
  unfold tailWord_391091
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264260626151574870245127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9509507084101049913496751 14264260626151574870245127)
  ·
    refine ⟨21396390939227362305367691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14264260626151574870245127 21396390939227362305367691)
    ·
      refine ⟨32094586408841043458051537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21396390939227362305367691 32094586408841043458051537)
      ·
        refine ⟨24070939806630782593538653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32094586408841043458051537 24070939806630782593538653)
        ·
          refine ⟨9026602427486543472576995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24070939806630782593538653 9026602427486543472576995)
          ·
            refine ⟨13539903641229815208865493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026602427486543472576995 13539903641229815208865493)
            ·
              refine ⟨317341491591323793957785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13539903641229815208865493 317341491591323793957785)
              ·
                refine ⟨238006118693492845468339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317341491591323793957785 238006118693492845468339)
                ·
                  refine ⟨357009178040239268202509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238006118693492845468339 357009178040239268202509)
                  ·
                    refine ⟨133878441765089725575941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357009178040239268202509 133878441765089725575941)
                    ·
                      rfl

theorem cell22_391091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 3].length) (baseStart_391091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391091 prefixEnd_391091 := by exact prefixLift 391091
  have htrace : WordTrace (prefixWord ++ tailWord_391091) baseStart_391091 baseEnd_391091 := by
    simpa [prefixWord, tailWord_391091, baseEnd_391091] using wordTrace_append hprefix tailTrace_391091
  have hstable : (prefixWord ++ tailWord_391091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391091).length < 2 ^ (prefixWord ++ tailWord_391091).sum := by decide
  have hdescent : baseEnd_391091 < baseStart_391091 := by decide
  rcases family_descends (prefixWord ++ tailWord_391091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391115 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 8]
def baseStart_391115 : Nat := 118140960795 + 391115 * 2 ^ 59
def prefixEnd_391115 : Nat := 4983230072969 + 3 ^ 40 * 391115 * 2
def baseEnd_391115 : Nat := 44628885818520554325289

theorem tailTrace_391115 : CollatzResearch.WordTrace tailWord_391115 prefixEnd_391115 44628885818520554325289 := by
  unfold tailWord_391115
  simp only [CollatzResearch.WordTrace]
  refine ⟨14265135978064626969118799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9510090652043084646079199 14265135978064626969118799)
  ·
    refine ⟨21397703967096940453678199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14265135978064626969118799 21397703967096940453678199)
    ·
      refine ⟨32096555950645410680517299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397703967096940453678199 32096555950645410680517299)
      ·
        refine ⟨48144833925968116020775949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32096555950645410680517299 48144833925968116020775949)
        ·
          refine ⟨18054312722238043507790981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48144833925968116020775949 18054312722238043507790981)
          ·
            refine ⟨3385183635419633157710809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18054312722238043507790981 3385183635419633157710809)
            ·
              refine ⟨2538887726564724868283107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3385183635419633157710809 2538887726564724868283107)
              ·
                refine ⟨3808331589847087302424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2538887726564724868283107 3808331589847087302424661)
                ·
                  refine ⟨44628885818520554325289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3808331589847087302424661 44628885818520554325289)
                  ·
                    rfl

theorem cell22_391115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_391115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391115 prefixEnd_391115 := by exact prefixLift 391115
  have htrace : WordTrace (prefixWord ++ tailWord_391115) baseStart_391115 baseEnd_391115 := by
    simpa [prefixWord, tailWord_391115, baseEnd_391115] using wordTrace_append hprefix tailTrace_391115
  have hstable : (prefixWord ++ tailWord_391115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391115).length < 2 ^ (prefixWord ++ tailWord_391115).sum := by decide
  have hdescent : baseEnd_391115 < baseStart_391115 := by decide
  rcases family_descends (prefixWord ++ tailWord_391115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391147 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 4, 3]
def baseStart_391147 : Nat := 118140960795 + 391147 * 2 ^ 59
def prefixEnd_391147 : Nat := 4983230072969 + 3 ^ 40 * 391147 * 2
def baseEnd_391147 : Nat := 133897611709524246175769

theorem tailTrace_391147 : CollatzResearch.WordTrace tailWord_391147 prefixEnd_391147 133897611709524246175769 := by
  unfold tailWord_391147
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266303113948696434283695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9510868742632464289522463 14266303113948696434283695)
  ·
    refine ⟨21399454670923044651425543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14266303113948696434283695 21399454670923044651425543)
    ·
      refine ⟨32099182006384566977138315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21399454670923044651425543 32099182006384566977138315)
      ·
        refine ⟨48148773009576850465707473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32099182006384566977138315 48148773009576850465707473)
        ·
          refine ⟨36111579757182637849280605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48148773009576850465707473 36111579757182637849280605)
          ·
            refine ⟨13541842408943489193480227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36111579757182637849280605 13541842408943489193480227)
            ·
              refine ⟨20312763613415233790220341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13541842408943489193480227 20312763613415233790220341)
              ·
                refine ⟨1904321588757678167833157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20312763613415233790220341 1904321588757678167833157)
                ·
                  refine ⟨357060297892064656468717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904321588757678167833157 357060297892064656468717)
                  ·
                    refine ⟨133897611709524246175769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357060297892064656468717 133897611709524246175769)
                    ·
                      rfl

theorem cell22_391147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 3].length) (baseStart_391147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391147 prefixEnd_391147 := by exact prefixLift 391147
  have htrace : WordTrace (prefixWord ++ tailWord_391147) baseStart_391147 baseEnd_391147 := by
    simpa [prefixWord, tailWord_391147, baseEnd_391147] using wordTrace_append hprefix tailTrace_391147
  have hstable : (prefixWord ++ tailWord_391147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391147).length < 2 ^ (prefixWord ++ tailWord_391147).sum := by decide
  have hdescent : baseEnd_391147 < baseStart_391147 := by decide
  rcases family_descends (prefixWord ++ tailWord_391147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391164 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_391164 : Nat := 118140960795 + 391164 * 2 ^ 59
def prefixEnd_391164 : Nat := 4983230072969 + 3 ^ 40 * 391164 * 2
def baseEnd_391164 : Nat := 133903431156941868500717

theorem tailTrace_391164 : CollatzResearch.WordTrace tailWord_391164 prefixEnd_391164 133903431156941868500717 := by
  unfold tailWord_391164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133461577443554168826273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9511282103258072225101697 7133461577443554168826273)
  ·
    refine ⟨5350096183082665626619705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7133461577443554168826273 5350096183082665626619705)
    ·
      refine ⟨4012572137311999219964779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5350096183082665626619705 4012572137311999219964779)
      ·
        refine ⟨6018858205967998829947169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012572137311999219964779 6018858205967998829947169)
        ·
          refine ⟨4514143654475999122460377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6018858205967998829947169 4514143654475999122460377)
          ·
            refine ⟨3385607740856999341845283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4514143654475999122460377 3385607740856999341845283)
            ·
              refine ⟨5078411611285499012767925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385607740856999341845283 5078411611285499012767925)
              ·
                refine ⟨476101088558015532446993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5078411611285499012767925 476101088558015532446993)
                ·
                  refine ⟨357075816418511649335245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476101088558015532446993 357075816418511649335245)
                  ·
                    refine ⟨133903431156941868500717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357075816418511649335245 133903431156941868500717)
                    ·
                      rfl

theorem cell22_391164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_391164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391164 prefixEnd_391164 := by exact prefixLift 391164
  have htrace : WordTrace (prefixWord ++ tailWord_391164) baseStart_391164 baseEnd_391164 := by
    simpa [prefixWord, tailWord_391164, baseEnd_391164] using wordTrace_append hprefix tailTrace_391164
  have hstable : (prefixWord ++ tailWord_391164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391164).length < 2 ^ (prefixWord ++ tailWord_391164).sum := by decide
  have hdescent : baseEnd_391164 < baseStart_391164 := by decide
  rcases family_descends (prefixWord ++ tailWord_391164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391260 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_391260 : Nat := 118140960795 + 391260 * 2 ^ 59
def prefixEnd_391260 : Nat := 4983230072969 + 3 ^ 40 * 391260 * 2
def baseEnd_391260 : Nat := 133936293918829618100423

theorem tailTrace_391260 : CollatzResearch.WordTrace tailWord_391260 prefixEnd_391260 133936293918829618100423 := by
  unfold tailWord_391260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135212281269658366573617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9513616375026211155431489 7135212281269658366573617)
  ·
    refine ⟨5351409210952243774930213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7135212281269658366573617 5351409210952243774930213)
    ·
      refine ⟨1003389227053545707799415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5351409210952243774930213 1003389227053545707799415)
      ·
        refine ⟨1505083840580318561699123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003389227053545707799415 1505083840580318561699123)
        ·
          refine ⟨2257625760870477842548685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505083840580318561699123 2257625760870477842548685)
          ·
            refine ⟨846609660326429190955757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2257625760870477842548685 846609660326429190955757)
            ·
              refine ⟨317478622622410946608409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846609660326429190955757 317478622622410946608409)
              ·
                refine ⟨238108966966808209956307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317478622622410946608409 238108966966808209956307)
                ·
                  refine ⟨357163450450212314934461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238108966966808209956307 357163450450212314934461)
                  ·
                    refine ⟨133936293918829618100423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357163450450212314934461 133936293918829618100423)
                    ·
                      rfl

theorem cell22_391260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_391260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391260 prefixEnd_391260 := by exact prefixLift 391260
  have htrace : WordTrace (prefixWord ++ tailWord_391260) baseStart_391260 baseEnd_391260 := by
    simpa [prefixWord, tailWord_391260, baseEnd_391260] using wordTrace_append hprefix tailTrace_391260
  have hstable : (prefixWord ++ tailWord_391260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391260).length < 2 ^ (prefixWord ++ tailWord_391260).sum := by decide
  have hdescent : baseEnd_391260 < baseStart_391260 := by decide
  rcases family_descends (prefixWord ++ tailWord_391260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391286 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_391286 : Nat := 118140960795 + 391286 * 2 ^ 59
def prefixEnd_391286 : Nat := 4983230072969 + 3 ^ 40 * 391286 * 2
def baseEnd_391286 : Nat := 133945194250174216950343

theorem tailTrace_391286 : CollatzResearch.WordTrace tailWord_391286 prefixEnd_391286 133945194250174216950343 := by
  unfold tailWord_391286
  simp only [CollatzResearch.WordTrace]
  refine ⟨891960803777820198349607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9514248573630082115729141 891960803777820198349607)
  ·
    refine ⟨1337941205666730297524411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891960803777820198349607 1337941205666730297524411)
    ·
      refine ⟨2006911808500095446286617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337941205666730297524411 2006911808500095446286617)
      ·
        refine ⟨1505183856375071584714963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2006911808500095446286617 1505183856375071584714963)
        ·
          refine ⟨2257775784562607377072445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505183856375071584714963 2257775784562607377072445)
          ·
            refine ⟨846665919210977766402167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2257775784562607377072445 846665919210977766402167)
            ·
              refine ⟨1269998878816466649603251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846665919210977766402167 1269998878816466649603251)
              ·
                refine ⟨1904998318224699974404877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269998878816466649603251 1904998318224699974404877)
                ·
                  refine ⟨714374369334262490401829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1904998318224699974404877 714374369334262490401829)
                  ·
                    refine ⟨133945194250174216950343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 714374369334262490401829 133945194250174216950343)
                    ·
                      rfl

theorem cell22_391286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_391286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391286 prefixEnd_391286 := by exact prefixLift 391286
  have htrace : WordTrace (prefixWord ++ tailWord_391286) baseStart_391286 baseEnd_391286 := by
    simpa [prefixWord, tailWord_391286, baseEnd_391286] using wordTrace_append hprefix tailTrace_391286
  have hstable : (prefixWord ++ tailWord_391286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391286).length < 2 ^ (prefixWord ++ tailWord_391286).sum := by decide
  have hdescent : baseEnd_391286 < baseStart_391286 := by decide
  rcases family_descends (prefixWord ++ tailWord_391286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391299 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 1, 5]
def baseStart_391299 : Nat := 118140960795 + 391299 * 2 ^ 59
def prefixEnd_391299 : Nat := 4983230072969 + 3 ^ 40 * 391299 * 2
def baseEnd_391299 : Nat := 133949644415846516375303

theorem tailTrace_391299 : CollatzResearch.WordTrace tailWord_391299 prefixEnd_391299 133949644415846516375303 := by
  unfold tailWord_391299
  simp only [CollatzResearch.WordTrace]
  refine ⟨14271847009398026393816951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9514564672932017595877967 14271847009398026393816951)
  ·
    refine ⟨21407770514097039590725427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14271847009398026393816951 21407770514097039590725427)
    ·
      refine ⟨32111655771145559386088141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21407770514097039590725427 32111655771145559386088141)
      ·
        refine ⟨12041870914179584769783053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32111655771145559386088141 12041870914179584769783053)
        ·
          refine ⟨4515701592817344288668645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12041870914179584769783053 4515701592817344288668645)
          ·
            refine ⟨846694048653252054125371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4515701592817344288668645 846694048653252054125371)
            ·
              refine ⟨1270041072979878081188057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846694048653252054125371 1270041072979878081188057)
              ·
                refine ⟨952530804734908560891043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270041072979878081188057 952530804734908560891043)
                ·
                  refine ⟨1428796207102362841336565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952530804734908560891043 1428796207102362841336565)
                  ·
                    refine ⟨133949644415846516375303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1428796207102362841336565 133949644415846516375303)
                    ·
                      rfl

theorem cell22_391299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_391299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391299 prefixEnd_391299 := by exact prefixLift 391299
  have htrace : WordTrace (prefixWord ++ tailWord_391299) baseStart_391299 baseEnd_391299 := by
    simpa [prefixWord, tailWord_391299, baseEnd_391299] using wordTrace_append hprefix tailTrace_391299
  have hstable : (prefixWord ++ tailWord_391299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391299).length < 2 ^ (prefixWord ++ tailWord_391299).sum := by decide
  have hdescent : baseEnd_391299 < baseStart_391299 := by decide
  rcases family_descends (prefixWord ++ tailWord_391299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391329 : List Nat := [1, 2, 3, 3, 1, 2, 3, 7]
def baseStart_391329 : Nat := 118140960795 + 391329 * 2 ^ 59
def prefixEnd_391329 : Nat := 4983230072969 + 3 ^ 40 * 391329 * 2
def baseEnd_391329 : Nat := 14884434892104048680579

theorem tailTrace_391329 : CollatzResearch.WordTrace tailWord_391329 prefixEnd_391329 14884434892104048680579 := by
  unfold tailWord_391329
  simp only [CollatzResearch.WordTrace]
  refine ⟨14272941199289341517409041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9515294132859561011606027 14272941199289341517409041)
  ·
    refine ⟨10704705899467006138056781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14272941199289341517409041 10704705899467006138056781)
    ·
      refine ⟨4014264712300127301771293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10704705899467006138056781 4014264712300127301771293)
      ·
        refine ⟨1505349267112547738164235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4014264712300127301771293 1505349267112547738164235)
        ·
          refine ⟨2258023900668821607246353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505349267112547738164235 2258023900668821607246353)
          ·
            refine ⟨1693517925501616205434765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2258023900668821607246353 1693517925501616205434765)
            ·
              refine ⟨635069222063106077038037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693517925501616205434765 635069222063106077038037)
              ·
                refine ⟨14884434892104048680579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 635069222063106077038037 14884434892104048680579)
                ·
                  rfl

theorem cell22_391329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 7].length) (baseStart_391329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391329 prefixEnd_391329 := by exact prefixLift 391329
  have htrace : WordTrace (prefixWord ++ tailWord_391329) baseStart_391329 baseEnd_391329 := by
    simpa [prefixWord, tailWord_391329, baseEnd_391329] using wordTrace_append hprefix tailTrace_391329
  have hstable : (prefixWord ++ tailWord_391329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391329).length < 2 ^ (prefixWord ++ tailWord_391329).sum := by decide
  have hdescent : baseEnd_391329 < baseStart_391329 := by decide
  rcases family_descends (prefixWord ++ tailWord_391329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391378 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_391378 : Nat := 118140960795 + 391378 * 2 ^ 59
def prefixEnd_391378 : Nat := 4983230072969 + 3 ^ 40 * 391378 * 2
def baseEnd_391378 : Nat := 133976687730316643650061

theorem tailTrace_391378 : CollatzResearch.WordTrace tailWord_391378 prefixEnd_391378 133976687730316643650061 := by
  unfold tailWord_391378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568682094027955721485697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9516485584074548590628525 3568682094027955721485697)
  ·
    refine ⟨2676511570520966791114273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3568682094027955721485697 2676511570520966791114273)
    ·
      refine ⟨2007383677890725093335705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2676511570520966791114273 2007383677890725093335705)
      ·
        refine ⟨1505537758418043820001779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2007383677890725093335705 1505537758418043820001779)
        ·
          refine ⟨2258306637627065730002669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505537758418043820001779 2258306637627065730002669)
          ·
            refine ⟨846864989110149648751001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2258306637627065730002669 846864989110149648751001)
            ·
              refine ⟨635148741832612236563251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846864989110149648751001 635148741832612236563251)
              ·
                refine ⟨952723112748918354844877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635148741832612236563251 952723112748918354844877)
                ·
                  refine ⟨357271167280844383066829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952723112748918354844877 357271167280844383066829)
                  ·
                    refine ⟨133976687730316643650061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357271167280844383066829 133976687730316643650061)
                    ·
                      rfl

theorem cell22_391378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_391378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391378 prefixEnd_391378 := by exact prefixLift 391378
  have htrace : WordTrace (prefixWord ++ tailWord_391378) baseStart_391378 baseEnd_391378 := by
    simpa [prefixWord, tailWord_391378, baseEnd_391378] using wordTrace_append hprefix tailTrace_391378
  have hstable : (prefixWord ++ tailWord_391378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391378).length < 2 ^ (prefixWord ++ tailWord_391378).sum := by decide
  have hdescent : baseEnd_391378 < baseStart_391378 := by decide
  rcases family_descends (prefixWord ++ tailWord_391378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391605 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 6]
def baseStart_391605 : Nat := 118140960795 + 391605 * 2 ^ 59
def prefixEnd_391605 : Nat := 4983230072969 + 3 ^ 40 * 391605 * 2
def baseEnd_391605 : Nat := 44684798156454572741455

theorem tailTrace_391605 : CollatzResearch.WordTrace tailWord_391605 prefixEnd_391605 44684798156454572741455 := by
  unfold tailWord_391605
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283007746289440654456269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9522005164192960436304179 14283007746289440654456269)
  ·
    refine ⟨5356127904858540245421101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14283007746289440654456269 5356127904858540245421101)
    ·
      refine ⟨2008547964321952592032913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5356127904858540245421101 2008547964321952592032913)
      ·
        refine ⟨1506410973241464444024685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2008547964321952592032913 1506410973241464444024685)
        ·
          refine ⟨564904114965549166509257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1506410973241464444024685 564904114965549166509257)
          ·
            refine ⟨423678086224161874881943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564904114965549166509257 423678086224161874881943)
            ·
              refine ⟨635517129336242812322915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423678086224161874881943 635517129336242812322915)
              ·
                refine ⟨953275694004364218484373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635517129336242812322915 953275694004364218484373)
                ·
                  refine ⟨44684798156454572741455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 953275694004364218484373 44684798156454572741455)
                  ·
                    rfl

theorem cell22_391605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_391605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391605 prefixEnd_391605 := by exact prefixLift 391605
  have htrace : WordTrace (prefixWord ++ tailWord_391605) baseStart_391605 baseEnd_391605 := by
    simpa [prefixWord, tailWord_391605, baseEnd_391605] using wordTrace_append hprefix tailTrace_391605
  have hstable : (prefixWord ++ tailWord_391605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391605).length < 2 ^ (prefixWord ++ tailWord_391605).sum := by decide
  have hdescent : baseEnd_391605 < baseStart_391605 := by decide
  rcases family_descends (prefixWord ++ tailWord_391605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391650 : List Nat := [3, 3, 3, 2, 1, 10]
def baseStart_391650 : Nat := 118140960795 + 391650 * 2 ^ 59
def prefixEnd_391650 : Nat := 4983230072969 + 3 ^ 40 * 391650 * 2
def baseEnd_391650 : Nat := 1655182702333316059867

theorem tailTrace_391650 : CollatzResearch.WordTrace tailWord_391650 prefixEnd_391650 1655182702333316059867 := by
  unfold tailWord_391650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571162257781603334961101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9523099354084275559896269 3571162257781603334961101)
  ·
    refine ⟨1339185846668101250610413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3571162257781603334961101 1339185846668101250610413)
    ·
      refine ⟨502194692500537968978905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1339185846668101250610413 502194692500537968978905)
      ·
        refine ⟨376646019375403476734179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502194692500537968978905 376646019375403476734179)
        ·
          refine ⟨564969029063105215101269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376646019375403476734179 564969029063105215101269)
          ·
            refine ⟨1655182702333316059867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 564969029063105215101269 1655182702333316059867)
            ·
              rfl

theorem cell22_391650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 10].length) (baseStart_391650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391650 prefixEnd_391650 := by exact prefixLift 391650
  have htrace : WordTrace (prefixWord ++ tailWord_391650) baseStart_391650 baseEnd_391650 := by
    simpa [prefixWord, tailWord_391650, baseEnd_391650] using wordTrace_append hprefix tailTrace_391650
  have hstable : (prefixWord ++ tailWord_391650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391650).length < 2 ^ (prefixWord ++ tailWord_391650).sum := by decide
  have hdescent : baseEnd_391650 < baseStart_391650 := by decide
  rcases family_descends (prefixWord ++ tailWord_391650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391686 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_391686 : Nat := 118140960795 + 391686 * 2 ^ 59
def prefixEnd_391686 : Nat := 4983230072969 + 3 ^ 40 * 391686 * 2
def baseEnd_391686 : Nat := 134082122424706506949117

theorem tailTrace_391686 : CollatzResearch.WordTrace tailWord_391686 prefixEnd_391686 134082122424706506949117 := by
  unfold tailWord_391686
  simp only [CollatzResearch.WordTrace]
  refine ⟨446436314343624734004841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9523974705997327658769941 446436314343624734004841)
  ·
    refine ⟨334827235757718550503631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 446436314343624734004841 334827235757718550503631)
    ·
      refine ⟨502240853636577825755447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334827235757718550503631 502240853636577825755447)
      ·
        refine ⟨753361280454866738633171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502240853636577825755447 753361280454866738633171)
        ·
          refine ⟨1130041920682300107949757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753361280454866738633171 1130041920682300107949757)
          ·
            refine ⟨423765720255862540481159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1130041920682300107949757 423765720255862540481159)
            ·
              refine ⟨635648580383793810721739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423765720255862540481159 635648580383793810721739)
              ·
                refine ⟨953472870575690716082609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635648580383793810721739 953472870575690716082609)
                ·
                  refine ⟨715104652931768037061957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953472870575690716082609 715104652931768037061957)
                  ·
                    refine ⟨134082122424706506949117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715104652931768037061957 134082122424706506949117)
                    ·
                      rfl

theorem cell22_391686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_391686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391686 prefixEnd_391686 := by exact prefixLift 391686
  have htrace : WordTrace (prefixWord ++ tailWord_391686) baseStart_391686 baseEnd_391686 := by
    simpa [prefixWord, tailWord_391686, baseEnd_391686] using wordTrace_append hprefix tailTrace_391686
  have hstable : (prefixWord ++ tailWord_391686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391686).length < 2 ^ (prefixWord ++ tailWord_391686).sum := by decide
  have hdescent : baseEnd_391686 < baseStart_391686 := by decide
  rcases family_descends (prefixWord ++ tailWord_391686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391712 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 5]
def baseStart_391712 : Nat := 118140960795 + 391712 * 2 ^ 59
def prefixEnd_391712 : Nat := 4983230072969 + 3 ^ 40 * 391712 * 2
def baseEnd_391712 : Nat := 44697007585350368599679

theorem tailTrace_391712 : CollatzResearch.WordTrace tailWord_391712 prefixEnd_391712 44697007585350368599679 := by
  unfold tailWord_391712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7143455178450898964300695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9524606904601198619067593 7143455178450898964300695)
  ·
    refine ⟨10715182767676348446451043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7143455178450898964300695 10715182767676348446451043)
    ·
      refine ⟨16072774151514522669676565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10715182767676348446451043 16072774151514522669676565)
      ·
        refine ⟨753411288352243250141089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16072774151514522669676565 753411288352243250141089)
        ·
          refine ⟨565058466264182437605817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753411288352243250141089 565058466264182437605817)
          ·
            refine ⟨423793849698136828204363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565058466264182437605817 423793849698136828204363)
            ·
              refine ⟨635690774547205242306545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423793849698136828204363 635690774547205242306545)
              ·
                refine ⟨476768080910403931729909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635690774547205242306545 476768080910403931729909)
                ·
                  refine ⟨44697007585350368599679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476768080910403931729909 44697007585350368599679)
                  ·
                    rfl

theorem cell22_391712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_391712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391712 prefixEnd_391712 := by exact prefixLift 391712
  have htrace : WordTrace (prefixWord ++ tailWord_391712) baseStart_391712 baseEnd_391712 := by
    simpa [prefixWord, tailWord_391712, baseEnd_391712] using wordTrace_append hprefix tailTrace_391712
  have hstable : (prefixWord ++ tailWord_391712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391712).length < 2 ^ (prefixWord ++ tailWord_391712).sum := by decide
  have hdescent : baseEnd_391712 < baseStart_391712 := by decide
  rcases family_descends (prefixWord ++ tailWord_391712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391789 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_391789 : Nat := 118140960795 + 391789 * 2 ^ 59
def prefixEnd_391789 : Nat := 4983230072969 + 3 ^ 40 * 391789 * 2
def baseEnd_391789 : Nat := 134117381429648571623801

theorem tailTrace_391789 : CollatzResearch.WordTrace tailWord_391789 prefixEnd_391789 134117381429648571623801 := by
  unfold tailWord_391789
  simp only [CollatzResearch.WordTrace]
  refine ⟨14289718777622840079154421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9526479185081893386102947 14289718777622840079154421)
  ·
    refine ⟨1339661135402141257420727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14289718777622840079154421 1339661135402141257420727)
    ·
      refine ⟨2009491703103211886131091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1339661135402141257420727 2009491703103211886131091)
      ·
        refine ⟨3014237554654817829196637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009491703103211886131091 3014237554654817829196637)
        ·
          refine ⟨1130339082995556685948739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3014237554654817829196637 1130339082995556685948739)
          ·
            refine ⟨1695508624493335028923109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130339082995556685948739 1695508624493335028923109)
            ·
              refine ⟨317907867092500317923083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1695508624493335028923109 317907867092500317923083)
              ·
                refine ⟨476861800638750476884625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317907867092500317923083 476861800638750476884625)
                ·
                  refine ⟨357646350479062857663469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476861800638750476884625 357646350479062857663469)
                  ·
                    refine ⟨134117381429648571623801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357646350479062857663469 134117381429648571623801)
                    ·
                      rfl

theorem cell22_391789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_391789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391789 prefixEnd_391789 := by exact prefixLift 391789
  have htrace : WordTrace (prefixWord ++ tailWord_391789) baseStart_391789 baseEnd_391789 := by
    simpa [prefixWord, tailWord_391789, baseEnd_391789] using wordTrace_append hprefix tailTrace_391789
  have hstable : (prefixWord ++ tailWord_391789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391789).length < 2 ^ (prefixWord ++ tailWord_391789).sum := by decide
  have hdescent : baseEnd_391789 < baseStart_391789 := by decide
  rcases family_descends (prefixWord ++ tailWord_391789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391817 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 1, 3]
def baseStart_391817 : Nat := 118140960795 + 391817 * 2 ^ 59
def prefixEnd_391817 : Nat := 4983230072969 + 3 ^ 40 * 391817 * 2
def baseEnd_391817 : Nat := 134126966401865831923715

theorem tailTrace_391817 : CollatzResearch.WordTrace tailWord_391817 prefixEnd_391817 134126966401865831923715 := by
  unfold tailWord_391817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14290740021521400861173705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9527160014347600574115803 14290740021521400861173705)
  ·
    refine ⟨10718055016141050645880279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14290740021521400861173705 10718055016141050645880279)
    ·
      refine ⟨16077082524211575968820419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718055016141050645880279 16077082524211575968820419)
      ·
        refine ⟨24115623786317363953230629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077082524211575968820419 24115623786317363953230629)
        ·
          refine ⟨4521679459934505741230743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24115623786317363953230629 4521679459934505741230743)
          ·
            refine ⟨6782519189901758611846115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521679459934505741230743 6782519189901758611846115)
            ·
              refine ⟨10173778784852637917769173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782519189901758611846115 10173778784852637917769173)
              ·
                refine ⟨238447940269983701197715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10173778784852637917769173 238447940269983701197715)
                ·
                  refine ⟨357671910404975551796573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238447940269983701197715 357671910404975551796573)
                  ·
                    refine ⟨134126966401865831923715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357671910404975551796573 134126966401865831923715)
                    ·
                      rfl

theorem cell22_391817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_391817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391817 prefixEnd_391817 := by exact prefixLift 391817
  have htrace : WordTrace (prefixWord ++ tailWord_391817) baseStart_391817 baseEnd_391817 := by
    simpa [prefixWord, tailWord_391817, baseEnd_391817] using wordTrace_append hprefix tailTrace_391817
  have hstable : (prefixWord ++ tailWord_391817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391817).length < 2 ^ (prefixWord ++ tailWord_391817).sum := by decide
  have hdescent : baseEnd_391817 < baseStart_391817 := by decide
  rcases family_descends (prefixWord ++ tailWord_391817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391905 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_391905 : Nat := 118140960795 + 391905 * 2 ^ 59
def prefixEnd_391905 : Nat := 4983230072969 + 3 ^ 40 * 391905 * 2
def baseEnd_391905 : Nat := 134157090600262935723445

theorem tailTrace_391905 : CollatzResearch.WordTrace tailWord_391905 prefixEnd_391905 134157090600262935723445 := by
  unfold tailWord_391905
  simp only [CollatzResearch.WordTrace]
  refine ⟨14293949645202591890377169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9529299763468394593584779 14293949645202591890377169)
  ·
    refine ⟨10720462233901943917782877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14293949645202591890377169 10720462233901943917782877)
    ·
      refine ⟨4020173337713228969168579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10720462233901943917782877 4020173337713228969168579)
      ·
        refine ⟨6030260006569843453752869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020173337713228969168579 6030260006569843453752869)
        ·
          refine ⟨1130673751231845647578663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6030260006569843453752869 1130673751231845647578663)
          ·
            refine ⟨1696010626847768471367995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130673751231845647578663 1696010626847768471367995)
            ·
              refine ⟨2544015940271652707051993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696010626847768471367995 2544015940271652707051993)
              ·
                refine ⟨1908011955203739530288995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2544015940271652707051993 1908011955203739530288995)
                ·
                  refine ⟨2862017932805609295433493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908011955203739530288995 2862017932805609295433493)
                  ·
                    refine ⟨134157090600262935723445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2862017932805609295433493 134157090600262935723445)
                    ·
                      rfl

theorem cell22_391905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_391905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391905 prefixEnd_391905 := by exact prefixLift 391905
  have htrace : WordTrace (prefixWord ++ tailWord_391905) baseStart_391905 baseEnd_391905 := by
    simpa [prefixWord, tailWord_391905, baseEnd_391905] using wordTrace_append hprefix tailTrace_391905
  have hstable : (prefixWord ++ tailWord_391905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391905).length < 2 ^ (prefixWord ++ tailWord_391905).sum := by decide
  have hdescent : baseEnd_391905 < baseStart_391905 := by decide
  rcases family_descends (prefixWord ++ tailWord_391905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391907 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 1, 5]
def baseStart_391907 : Nat := 118140960795 + 391907 * 2 ^ 59
def prefixEnd_391907 : Nat := 4983230072969 + 3 ^ 40 * 391907 * 2
def baseEnd_391907 : Nat := 134157775241135597173439

theorem tailTrace_391907 : CollatzResearch.WordTrace tailWord_391907 prefixEnd_391907 134157775241135597173439 := by
  unfold tailWord_391907
  simp only [CollatzResearch.WordTrace]
  refine ⟨14294022591195346231949975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9529348394130230821299983 14294022591195346231949975)
  ·
    refine ⟨21441033886793019347924963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14294022591195346231949975 21441033886793019347924963)
    ·
      refine ⟨32161550830189529021887445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21441033886793019347924963 32161550830189529021887445)
      ·
        refine ⟨753786347582567086450487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32161550830189529021887445 753786347582567086450487)
        ·
          refine ⟨1130679521373850629675731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753786347582567086450487 1130679521373850629675731)
          ·
            refine ⟨1696019282060775944513597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130679521373850629675731 1696019282060775944513597)
            ·
              refine ⟨636007230772790979192599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1696019282060775944513597 636007230772790979192599)
              ·
                refine ⟨954010846159186468788899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636007230772790979192599 954010846159186468788899)
                ·
                  refine ⟨1431016269238779703183349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954010846159186468788899 1431016269238779703183349)
                  ·
                    refine ⟨134157775241135597173439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1431016269238779703183349 134157775241135597173439)
                    ·
                      rfl

theorem cell22_391907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].length) (baseStart_391907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391907 prefixEnd_391907 := by exact prefixLift 391907
  have htrace : WordTrace (prefixWord ++ tailWord_391907) baseStart_391907 baseEnd_391907 := by
    simpa [prefixWord, tailWord_391907, baseEnd_391907] using wordTrace_append hprefix tailTrace_391907
  have hstable : (prefixWord ++ tailWord_391907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391907).length < 2 ^ (prefixWord ++ tailWord_391907).sum := by decide
  have hdescent : baseEnd_391907 < baseStart_391907 := by decide
  rcases family_descends (prefixWord ++ tailWord_391907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391950 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_391950 : Nat := 118140960795 + 391950 * 2 ^ 59
def prefixEnd_391950 : Nat := 4983230072969 + 3 ^ 40 * 391950 * 2
def baseEnd_391950 : Nat := 134172495019897818348307

theorem tailTrace_391950 : CollatzResearch.WordTrace tailWord_391950 prefixEnd_391950 134172495019897818348307 := by
  unfold tailWord_391950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786948866254945571970663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9530393953359709717176869 1786948866254945571970663)
  ·
    refine ⟨2680423299382418357955995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786948866254945571970663 2680423299382418357955995)
    ·
      refine ⟨4020634949073627536933993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680423299382418357955995 4020634949073627536933993)
      ·
        refine ⟨3015476211805220652700495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4020634949073627536933993 3015476211805220652700495)
        ·
          refine ⟨4523214317707830979050743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015476211805220652700495 4523214317707830979050743)
          ·
            refine ⟨6784821476561746468576115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523214317707830979050743 6784821476561746468576115)
            ·
              refine ⟨10177232214842619702864173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784821476561746468576115 10177232214842619702864173)
              ·
                refine ⟨3816462080565982388574065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10177232214842619702864173 3816462080565982388574065)
                ·
                  refine ⟨2862346560424486791430549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816462080565982388574065 2862346560424486791430549)
                  ·
                    refine ⟨134172495019897818348307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2862346560424486791430549 134172495019897818348307)
                    ·
                      rfl

theorem cell22_391950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_391950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391950 prefixEnd_391950 := by exact prefixLift 391950
  have htrace : WordTrace (prefixWord ++ tailWord_391950) baseStart_391950 baseEnd_391950 := by
    simpa [prefixWord, tailWord_391950, baseEnd_391950] using wordTrace_append hprefix tailTrace_391950
  have hstable : (prefixWord ++ tailWord_391950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391950).length < 2 ^ (prefixWord ++ tailWord_391950).sum := by decide
  have hdescent : baseEnd_391950 < baseStart_391950 := by decide
  rcases family_descends (prefixWord ++ tailWord_391950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391954 : List Nat := [3, 2, 4, 1, 2, 1, 2, 7]
def baseStart_391954 : Nat := 118140960795 + 391954 * 2 ^ 59
def prefixEnd_391954 : Nat := 4983230072969 + 3 ^ 40 * 391954 * 2
def baseEnd_391954 : Nat := 14908207144627015694255

theorem tailTrace_391954 : CollatzResearch.WordTrace tailWord_391954 prefixEnd_391954 14908207144627015694255 := by
  unfold tailWord_391954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573934205506268314727729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9530491214683382172607277 3573934205506268314727729)
  ·
    refine ⟨2680450654129701236045797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3573934205506268314727729 2680450654129701236045797)
    ·
      refine ⟨502584497649318981758587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2680450654129701236045797 502584497649318981758587)
      ·
        refine ⟨753876746473978472637881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502584497649318981758587 753876746473978472637881)
        ·
          refine ⟨565407559855483854478411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753876746473978472637881 565407559855483854478411)
          ·
            refine ⟨848111339783225781717617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565407559855483854478411 848111339783225781717617)
            ·
              refine ⟨636083504837419336288213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848111339783225781717617 636083504837419336288213)
              ·
                refine ⟨14908207144627015694255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 636083504837419336288213 14908207144627015694255)
                ·
                  rfl

theorem cell22_391954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_391954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_391954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_391954 prefixEnd_391954 := by exact prefixLift 391954
  have htrace : WordTrace (prefixWord ++ tailWord_391954) baseStart_391954 baseEnd_391954 := by
    simpa [prefixWord, tailWord_391954, baseEnd_391954] using wordTrace_append hprefix tailTrace_391954
  have hstable : (prefixWord ++ tailWord_391954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391954).length < 2 ^ (prefixWord ++ tailWord_391954).sum := by decide
  have hdescent : baseEnd_391954 < baseStart_391954 := by decide
  rcases family_descends (prefixWord ++ tailWord_391954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392012 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_392012 : Nat := 118140960795 + 392012 * 2 ^ 59
def prefixEnd_392012 : Nat := 4983230072969 + 3 ^ 40 * 392012 * 2
def baseEnd_392012 : Nat := 134193718886950323298117

theorem tailTrace_392012 : CollatzResearch.WordTrace tailWord_392012 prefixEnd_392012 134193718886950323298117 := by
  unfold tailWord_392012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148926127907474582261145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9531901503876632776348193 7148926127907474582261145)
  ·
    refine ⟨5361694595930605936695859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7148926127907474582261145 5361694595930605936695859)
    ·
      refine ⟨8042541893895908905043789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5361694595930605936695859 8042541893895908905043789)
      ·
        refine ⟨3015953210210965839391421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8042541893895908905043789 3015953210210965839391421)
        ·
          refine ⟨1130982453829112189771783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3015953210210965839391421 1130982453829112189771783)
          ·
            refine ⟨1696473680743668284657675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130982453829112189771783 1696473680743668284657675)
            ·
              refine ⟨2544710521115502426986513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696473680743668284657675 2544710521115502426986513)
              ·
                refine ⟨1908532890836626820239885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2544710521115502426986513 1908532890836626820239885)
                ·
                  refine ⟨715699834063735057589957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1908532890836626820239885 715699834063735057589957)
                  ·
                    refine ⟨134193718886950323298117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715699834063735057589957 134193718886950323298117)
                    ·
                      rfl

theorem cell22_392012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_392012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392012 prefixEnd_392012 := by exact prefixLift 392012
  have htrace : WordTrace (prefixWord ++ tailWord_392012) baseStart_392012 baseEnd_392012 := by
    simpa [prefixWord, tailWord_392012, baseEnd_392012] using wordTrace_append hprefix tailTrace_392012
  have hstable : (prefixWord ++ tailWord_392012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392012).length < 2 ^ (prefixWord ++ tailWord_392012).sum := by decide
  have hdescent : baseEnd_392012 < baseStart_392012 := by decide
  rcases family_descends (prefixWord ++ tailWord_392012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392044 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 4]
def baseStart_392044 : Nat := 118140960795 + 392044 * 2 ^ 59
def prefixEnd_392044 : Nat := 4983230072969 + 3 ^ 40 * 392044 * 2
def baseEnd_392044 : Nat := 44734891046970968832673

theorem tailTrace_392044 : CollatzResearch.WordTrace tailWord_392044 prefixEnd_392044 44734891046970968832673 := by
  unfold tailWord_392044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7149509695849509314843593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9532679594466012419791457 7149509695849509314843593)
  ·
    refine ⟨5362132271887131986132695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7149509695849509314843593 5362132271887131986132695)
    ·
      refine ⟨8043198407830697979199043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362132271887131986132695 8043198407830697979199043)
      ·
        refine ⟨12064797611746046968798565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043198407830697979199043 12064797611746046968798565)
        ·
          refine ⟨2262149552202383806649731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12064797611746046968798565 2262149552202383806649731)
          ·
            refine ⟨3393224328303575709974597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262149552202383806649731 3393224328303575709974597)
            ·
              refine ⟨636229561556920445620237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3393224328303575709974597 636229561556920445620237)
              ·
                refine ⟨238586085583845167107589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 636229561556920445620237 238586085583845167107589)
                ·
                  refine ⟨44734891046970968832673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238586085583845167107589 44734891046970968832673)
                  ·
                    rfl

theorem cell22_392044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_392044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392044 prefixEnd_392044 := by exact prefixLift 392044
  have htrace : WordTrace (prefixWord ++ tailWord_392044) baseStart_392044 baseEnd_392044 := by
    simpa [prefixWord, tailWord_392044, baseEnd_392044] using wordTrace_append hprefix tailTrace_392044
  have hstable : (prefixWord ++ tailWord_392044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392044).length < 2 ^ (prefixWord ++ tailWord_392044).sum := by decide
  have hdescent : baseEnd_392044 < baseStart_392044 := by decide
  rcases family_descends (prefixWord ++ tailWord_392044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392046 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_392046 : Nat := 118140960795 + 392046 * 2 ^ 59
def prefixEnd_392046 : Nat := 4983230072969 + 3 ^ 40 * 392046 * 2
def baseEnd_392046 : Nat := 134205357781785567948013

theorem tailTrace_392046 : CollatzResearch.WordTrace tailWord_392046 prefixEnd_392046 134205357781785567948013 := by
  unfold tailWord_392046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787386542211471621407499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9532728225127848647506661 1787386542211471621407499)
  ·
    refine ⟨2681079813317207432111249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1787386542211471621407499 2681079813317207432111249)
    ·
      refine ⟨2010809859987905574083437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2681079813317207432111249 2010809859987905574083437)
      ·
        refine ⟨754053697495464590281289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2010809859987905574083437 754053697495464590281289)
        ·
          refine ⟨565540273121598442710967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754053697495464590281289 565540273121598442710967)
          ·
            refine ⟨848310409682397664066451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565540273121598442710967 848310409682397664066451)
            ·
              refine ⟨1272465614523596496099677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848310409682397664066451 1272465614523596496099677)
              ·
                refine ⟨477174605446348686037379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1272465614523596496099677 477174605446348686037379)
                ·
                  refine ⟨715761908169523029056069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477174605446348686037379 715761908169523029056069)
                  ·
                    refine ⟨134205357781785567948013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 715761908169523029056069 134205357781785567948013)
                    ·
                      rfl

theorem cell22_392046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_392046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392046 prefixEnd_392046 := by exact prefixLift 392046
  have htrace : WordTrace (prefixWord ++ tailWord_392046) baseStart_392046 baseEnd_392046 := by
    simpa [prefixWord, tailWord_392046, baseEnd_392046] using wordTrace_append hprefix tailTrace_392046
  have hstable : (prefixWord ++ tailWord_392046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392046).length < 2 ^ (prefixWord ++ tailWord_392046).sum := by decide
  have hdescent : baseEnd_392046 < baseStart_392046 := by decide
  rcases family_descends (prefixWord ++ tailWord_392046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392059 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 2, 3]
def baseStart_392059 : Nat := 118140960795 + 392059 * 2 ^ 59
def prefixEnd_392059 : Nat := 4983230072969 + 3 ^ 40 * 392059 * 2
def baseEnd_392059 : Nat := 134209807947457867372973

theorem tailTrace_392059 : CollatzResearch.WordTrace tailWord_392059 prefixEnd_392059 134209807947457867372973 := by
  unfold tailWord_392059
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299566486644676191483231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9533044324429784127655487 14299566486644676191483231)
  ·
    refine ⟨21449349729967014287224847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14299566486644676191483231 21449349729967014287224847)
    ·
      refine ⟨32174024594950521430837271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21449349729967014287224847 32174024594950521430837271)
      ·
        refine ⟨48261036892425782146255907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32174024594950521430837271 48261036892425782146255907)
        ·
          refine ⟨72391555338638673219383861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48261036892425782146255907 72391555338638673219383861)
          ·
            refine ⟨6786708312997375614317237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72391555338638673219383861 6786708312997375614317237)
            ·
              refine ⟨636253904343503963842241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6786708312997375614317237 636253904343503963842241)
              ·
                refine ⟨477190428257627972881681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636253904343503963842241 477190428257627972881681)
                ·
                  refine ⟨357892821193220979661261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477190428257627972881681 357892821193220979661261)
                  ·
                    refine ⟨134209807947457867372973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357892821193220979661261 134209807947457867372973)
                    ·
                      rfl

theorem cell22_392059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 3].length) (baseStart_392059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392059 prefixEnd_392059 := by exact prefixLift 392059
  have htrace : WordTrace (prefixWord ++ tailWord_392059) baseStart_392059 baseEnd_392059 := by
    simpa [prefixWord, tailWord_392059, baseEnd_392059] using wordTrace_append hprefix tailTrace_392059
  have hstable : (prefixWord ++ tailWord_392059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392059).length < 2 ^ (prefixWord ++ tailWord_392059).sum := by decide
  have hdescent : baseEnd_392059 < baseStart_392059 := by decide
  rcases family_descends (prefixWord ++ tailWord_392059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392117 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 7]
def baseStart_392117 : Nat := 118140960795 + 392117 * 2 ^ 59
def prefixEnd_392117 : Nat := 4983230072969 + 3 ^ 40 * 392117 * 2
def baseEnd_392117 : Nat := 44743220844255016474265

theorem tailTrace_392117 : CollatzResearch.WordTrace tailWord_392117 prefixEnd_392117 44743220844255016474265 := by
  unfold tailWord_392117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14301681920434552097094605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9534454613623034731396403 14301681920434552097094605)
  ·
    refine ⟨5363130720162957036410477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14301681920434552097094605 5363130720162957036410477)
    ·
      refine ⟨2011174020061108888653929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5363130720162957036410477 2011174020061108888653929)
      ·
        refine ⟨1508380515045831666490447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2011174020061108888653929 1508380515045831666490447)
        ·
          refine ⟨2262570772568747499735671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508380515045831666490447 2262570772568747499735671)
          ·
            refine ⟨3393856158853121249603507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262570772568747499735671 3393856158853121249603507)
            ·
              refine ⟨5090784238279681874405261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393856158853121249603507 5090784238279681874405261)
              ·
                refine ⟨1909044089354880702901973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5090784238279681874405261 1909044089354880702901973)
                ·
                  refine ⟨44743220844255016474265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1909044089354880702901973 44743220844255016474265)
                  ·
                    rfl

theorem cell22_392117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_392117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392117 prefixEnd_392117 := by exact prefixLift 392117
  have htrace : WordTrace (prefixWord ++ tailWord_392117) baseStart_392117 baseEnd_392117 := by
    simpa [prefixWord, tailWord_392117, baseEnd_392117] using wordTrace_append hprefix tailTrace_392117
  have hstable : (prefixWord ++ tailWord_392117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392117).length < 2 ^ (prefixWord ++ tailWord_392117).sum := by decide
  have hdescent : baseEnd_392117 < baseStart_392117 := by decide
  rcases family_descends (prefixWord ++ tailWord_392117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392121 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_392121 : Nat := 118140960795 + 392121 * 2 ^ 59
def prefixEnd_392121 : Nat := 4983230072969 + 3 ^ 40 * 392121 * 2
def baseEnd_392121 : Nat := 134231031814510372322783

theorem tailTrace_392121 : CollatzResearch.WordTrace tailWord_392121 prefixEnd_392121 134231031814510372322783 := by
  unfold tailWord_392121
  simp only [CollatzResearch.WordTrace]
  refine ⟨14301827812420060780240217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9534551874946707186826811 14301827812420060780240217)
  ·
    refine ⟨10726370859315045585180163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14301827812420060780240217 10726370859315045585180163)
    ·
      refine ⟨16089556288972568377770245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726370859315045585180163 16089556288972568377770245)
      ·
        refine ⟨3016791804182356570831921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16089556288972568377770245 3016791804182356570831921)
        ·
          refine ⟨2262593853136767428123941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016791804182356570831921 2262593853136767428123941)
          ·
            refine ⟨424236347463143892773239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2262593853136767428123941 424236347463143892773239)
            ·
              refine ⟨636354521194715839159859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424236347463143892773239 636354521194715839159859)
              ·
                refine ⟨954531781792073758739789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636354521194715839159859 954531781792073758739789)
                ·
                  refine ⟨357949418172027659527421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954531781792073758739789 357949418172027659527421)
                  ·
                    refine ⟨134231031814510372322783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357949418172027659527421 134231031814510372322783)
                    ·
                      rfl

theorem cell22_392121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_392121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392121 prefixEnd_392121 := by exact prefixLift 392121
  have htrace : WordTrace (prefixWord ++ tailWord_392121) baseStart_392121 baseEnd_392121 := by
    simpa [prefixWord, tailWord_392121, baseEnd_392121] using wordTrace_append hprefix tailTrace_392121
  have hstable : (prefixWord ++ tailWord_392121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392121).length < 2 ^ (prefixWord ++ tailWord_392121).sum := by decide
  have hdescent : baseEnd_392121 < baseStart_392121 := by decide
  rcases family_descends (prefixWord ++ tailWord_392121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392228 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_392228 : Nat := 118140960795 + 392228 * 2 ^ 59
def prefixEnd_392228 : Nat := 4983230072969 + 3 ^ 40 * 392228 * 2
def baseEnd_392228 : Nat := 134267660101197759897455

theorem tailTrace_392228 : CollatzResearch.WordTrace tailWord_392228 prefixEnd_392228 134267660101197759897455 := by
  unfold tailWord_392228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152865211516209027192669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9537153615354945369590225 7152865211516209027192669)
  ·
    refine ⟨2682324454318578385197251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7152865211516209027192669 2682324454318578385197251)
    ·
      refine ⟨4023486681477867577795877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2682324454318578385197251 4023486681477867577795877)
      ·
        refine ⟨754403752777100170836727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4023486681477867577795877 754403752777100170836727)
        ·
          refine ⟨1131605629165650256255091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754403752777100170836727 1131605629165650256255091)
          ·
            refine ⟨1697408443748475384382637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131605629165650256255091 1697408443748475384382637)
            ·
              refine ⟨636528166405678269143489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1697408443748475384382637 636528166405678269143489)
              ·
                refine ⟨477396124804258701857617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636528166405678269143489 477396124804258701857617)
                ·
                  refine ⟨358047093603194026393213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477396124804258701857617 358047093603194026393213)
                  ·
                    refine ⟨134267660101197759897455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358047093603194026393213 134267660101197759897455)
                    ·
                      rfl

theorem cell22_392228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_392228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392228 prefixEnd_392228 := by exact prefixLift 392228
  have htrace : WordTrace (prefixWord ++ tailWord_392228) baseStart_392228 baseEnd_392228 := by
    simpa [prefixWord, tailWord_392228, baseEnd_392228] using wordTrace_append hprefix tailTrace_392228
  have hstable : (prefixWord ++ tailWord_392228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392228).length < 2 ^ (prefixWord ++ tailWord_392228).sum := by decide
  have hdescent : baseEnd_392228 < baseStart_392228 := by decide
  rcases family_descends (prefixWord ++ tailWord_392228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392273 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 1, 3]
def baseStart_392273 : Nat := 118140960795 + 392273 * 2 ^ 59
def prefixEnd_392273 : Nat := 4983230072969 + 3 ^ 40 * 392273 * 2
def baseEnd_392273 : Nat := 134283064520832642522317

theorem tailTrace_392273 : CollatzResearch.WordTrace tailWord_392273 prefixEnd_392273 134283064520832642522317 := by
  unfold tailWord_392273
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307371707869390739773473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9538247805246260493182315 14307371707869390739773473)
  ·
    refine ⟨10730528780902043054830105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14307371707869390739773473 10730528780902043054830105)
    ·
      refine ⟨8047896585676532291122579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10730528780902043054830105 8047896585676532291122579)
      ·
        refine ⟨12071844878514798436683869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047896585676532291122579 12071844878514798436683869)
        ·
          refine ⟨4526941829443049413756451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12071844878514798436683869 4526941829443049413756451)
          ·
            refine ⟨6790412744164574120634677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526941829443049413756451 6790412744164574120634677)
            ·
              refine ⟨636601194765428823809501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6790412744164574120634677 636601194765428823809501)
              ·
                refine ⟨238725448037035808928563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 636601194765428823809501 238725448037035808928563)
                ·
                  refine ⟨358088172055553713392845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238725448037035808928563 358088172055553713392845)
                  ·
                    refine ⟨134283064520832642522317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358088172055553713392845 134283064520832642522317)
                    ·
                      rfl

theorem cell22_392273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_392273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392273 prefixEnd_392273 := by exact prefixLift 392273
  have htrace : WordTrace (prefixWord ++ tailWord_392273) baseStart_392273 baseEnd_392273 := by
    simpa [prefixWord, tailWord_392273, baseEnd_392273] using wordTrace_append hprefix tailTrace_392273
  have hstable : (prefixWord ++ tailWord_392273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392273).length < 2 ^ (prefixWord ++ tailWord_392273).sum := by decide
  have hdescent : baseEnd_392273 < baseStart_392273 := by decide
  rcases family_descends (prefixWord ++ tailWord_392273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392290 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_392290 : Nat := 118140960795 + 392290 * 2 ^ 59
def prefixEnd_392290 : Nat := 4983230072969 + 3 ^ 40 * 392290 * 2
def baseEnd_392290 : Nat := 134288883968250264847265

theorem tailTrace_392290 : CollatzResearch.WordTrace tailWord_392290 prefixEnd_392290 134288883968250264847265 := by
  unfold tailWord_392290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576997937201950660785581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9538661165871868428761549 3576997937201950660785581)
  ·
    refine ⟨1341374226450731497794593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3576997937201950660785581 1341374226450731497794593)
    ·
      refine ⟨1006030669838048623345945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1341374226450731497794593 1006030669838048623345945)
      ·
        refine ⟨754523002378536467509459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1006030669838048623345945 754523002378536467509459)
        ·
          refine ⟨1131784503567804701264189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754523002378536467509459 1131784503567804701264189)
          ·
            refine ⟨424419188837926762974071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1131784503567804701264189 424419188837926762974071)
            ·
              refine ⟨636628783256890144461107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424419188837926762974071 636628783256890144461107)
              ·
                refine ⟨954943174885335216691661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636628783256890144461107 954943174885335216691661)
                ·
                  refine ⟨358103690582000706259373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954943174885335216691661 358103690582000706259373)
                  ·
                    refine ⟨134288883968250264847265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358103690582000706259373 134288883968250264847265)
                    ·
                      rfl

theorem cell22_392290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_392290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392290 prefixEnd_392290 := by exact prefixLift 392290
  have htrace : WordTrace (prefixWord ++ tailWord_392290) baseStart_392290 baseEnd_392290 := by
    simpa [prefixWord, tailWord_392290, baseEnd_392290] using wordTrace_append hprefix tailTrace_392290
  have hstable : (prefixWord ++ tailWord_392290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392290).length < 2 ^ (prefixWord ++ tailWord_392290).sum := by decide
  have hdescent : baseEnd_392290 < baseStart_392290 := by decide
  rcases family_descends (prefixWord ++ tailWord_392290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392329 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_392329 : Nat := 118140960795 + 392329 * 2 ^ 59
def prefixEnd_392329 : Nat := 4983230072969 + 3 ^ 40 * 392329 * 2
def baseEnd_392329 : Nat := 134302234465267163122145

theorem tailTrace_392329 : CollatzResearch.WordTrace tailWord_392329 prefixEnd_392329 134302234465267163122145 := by
  unfold tailWord_392329
  simp only [CollatzResearch.WordTrace]
  refine ⟨14309414195666512303812041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9539609463777674869208027 14309414195666512303812041)
  ·
    refine ⟨10732060646749884227859031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14309414195666512303812041 10732060646749884227859031)
    ·
      refine ⟨16098090970124826341788547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10732060646749884227859031 16098090970124826341788547)
      ·
        refine ⟨24147136455187239512682821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16098090970124826341788547 24147136455187239512682821)
        ·
          refine ⟨4527588085347607408628029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24147136455187239512682821 4527588085347607408628029)
          ·
            refine ⟨1697845532005352778235511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4527588085347607408628029 1697845532005352778235511)
            ·
              refine ⟨2546768298008029167353267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697845532005352778235511 2546768298008029167353267)
              ·
                refine ⟨3820152447012043751029901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546768298008029167353267 3820152447012043751029901)
                ·
                  refine ⟨1432557167629516406636213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3820152447012043751029901 1432557167629516406636213)
                  ·
                    refine ⟨134302234465267163122145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1432557167629516406636213 134302234465267163122145)
                    ·
                      rfl

theorem cell22_392329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_392329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392329 prefixEnd_392329 := by exact prefixLift 392329
  have htrace : WordTrace (prefixWord ++ tailWord_392329) baseStart_392329 baseEnd_392329 := by
    simpa [prefixWord, tailWord_392329, baseEnd_392329] using wordTrace_append hprefix tailTrace_392329
  have hstable : (prefixWord ++ tailWord_392329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392329).length < 2 ^ (prefixWord ++ tailWord_392329).sum := by decide
  have hdescent : baseEnd_392329 < baseStart_392329 := by decide
  rcases family_descends (prefixWord ++ tailWord_392329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392348 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 4]
def baseStart_392348 : Nat := 118140960795 + 392348 * 2 ^ 59
def prefixEnd_392348 : Nat := 4983230072969 + 3 ^ 40 * 392348 * 2
def baseEnd_392348 : Nat := 44769579517852482299029

theorem tailTrace_392348 : CollatzResearch.WordTrace tailWord_392348 prefixEnd_392348 44769579517852482299029 := by
  unfold tailWord_392348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7155053591298839274376849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9540071455065119032502465 7155053591298839274376849)
  ·
    refine ⟨5366290193474129455782637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7155053591298839274376849 5366290193474129455782637)
    ·
      refine ⟨2012358822552798545918489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5366290193474129455782637 2012358822552798545918489)
      ·
        refine ⟨1509269116914598909438867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2012358822552798545918489 1509269116914598909438867)
        ·
          refine ⟨2263903675371898364158301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509269116914598909438867 2263903675371898364158301)
          ·
            refine ⟨848963878264461886559363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2263903675371898364158301 848963878264461886559363)
            ·
              refine ⟨1273445817396692829839045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848963878264461886559363 1273445817396692829839045)
              ·
                refine ⟨238771090761879905594821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1273445817396692829839045 238771090761879905594821)
                ·
                  refine ⟨44769579517852482299029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238771090761879905594821 44769579517852482299029)
                  ·
                    rfl

theorem cell22_392348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_392348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392348 prefixEnd_392348 := by exact prefixLift 392348
  have htrace : WordTrace (prefixWord ++ tailWord_392348) baseStart_392348 baseEnd_392348 := by
    simpa [prefixWord, tailWord_392348, baseEnd_392348] using wordTrace_append hprefix tailTrace_392348
  have hstable : (prefixWord ++ tailWord_392348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392348).length < 2 ^ (prefixWord ++ tailWord_392348).sum := by decide
  have hdescent : baseEnd_392348 < baseStart_392348 := by decide
  rcases family_descends (prefixWord ++ tailWord_392348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392397 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_392397 : Nat := 118140960795 + 392397 * 2 ^ 59
def prefixEnd_392397 : Nat := 4983230072969 + 3 ^ 40 * 392397 * 2
def baseEnd_392397 : Nat := 134325512254937652421937

theorem tailTrace_392397 : CollatzResearch.WordTrace tailWord_392397 prefixEnd_392397 134325512254937652421937 := by
  unfold tailWord_392397
  simp only [CollatzResearch.WordTrace]
  refine ⟨14311894359420159917287445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9541262906280106611524963 14311894359420159917287445)
  ·
    refine ⟨670870048097819996122849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14311894359420159917287445 670870048097819996122849)
    ·
      refine ⟨503152536073364997092137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 670870048097819996122849 503152536073364997092137)
      ·
        refine ⟨377364402055023747819103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503152536073364997092137 377364402055023747819103)
        ·
          refine ⟨566046603082535621728655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377364402055023747819103 566046603082535621728655)
          ·
            refine ⟨849069904623803432592983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566046603082535621728655 849069904623803432592983)
            ·
              refine ⟨1273604856935705148889475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849069904623803432592983 1273604856935705148889475)
              ·
                refine ⟨1910407285403557723334213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273604856935705148889475 1910407285403557723334213)
                ·
                  refine ⟨358201366013167073125165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1910407285403557723334213 358201366013167073125165)
                  ·
                    refine ⟨134325512254937652421937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358201366013167073125165 134325512254937652421937)
                    ·
                      rfl

theorem cell22_392397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_392397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392397 prefixEnd_392397 := by exact prefixLift 392397
  have htrace : WordTrace (prefixWord ++ tailWord_392397) baseStart_392397 baseEnd_392397 := by
    simpa [prefixWord, tailWord_392397, baseEnd_392397] using wordTrace_append hprefix tailTrace_392397
  have hstable : (prefixWord ++ tailWord_392397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392397).length < 2 ^ (prefixWord ++ tailWord_392397).sum := by decide
  have hdescent : baseEnd_392397 < baseStart_392397 := by decide
  rcases family_descends (prefixWord ++ tailWord_392397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392481 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_392481 : Nat := 118140960795 + 392481 * 2 ^ 59
def prefixEnd_392481 : Nat := 4983230072969 + 3 ^ 40 * 392481 * 2
def baseEnd_392481 : Nat := 134354267171589433321679

theorem tailTrace_392481 : CollatzResearch.WordTrace tailWord_392481 prefixEnd_392481 134354267171589433321679 := by
  unfold tailWord_392481
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314958091115842263345297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9543305394077228175563531 14314958091115842263345297)
  ·
    refine ⟨10736218568336881697508973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14314958091115842263345297 10736218568336881697508973)
    ·
      refine ⟨4026081963126330636565865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10736218568336881697508973 4026081963126330636565865)
      ·
        refine ⟨3019561472344747977424399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4026081963126330636565865 3019561472344747977424399)
        ·
          refine ⟨4529342208517121966136599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019561472344747977424399 4529342208517121966136599)
          ·
            refine ⟨6794013312775682949204899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529342208517121966136599 6794013312775682949204899)
            ·
              refine ⟨10191019969163524423807349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794013312775682949204899 10191019969163524423807349)
              ·
                refine ⟨955408122109080414731939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10191019969163524423807349 955408122109080414731939)
                ·
                  refine ⟨1433112183163620622097909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955408122109080414731939 1433112183163620622097909)
                  ·
                    refine ⟨134354267171589433321679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1433112183163620622097909 134354267171589433321679)
                    ·
                      rfl

theorem cell22_392481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_392481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392481 prefixEnd_392481 := by exact prefixLift 392481
  have htrace : WordTrace (prefixWord ++ tailWord_392481) baseStart_392481 baseEnd_392481 := by
    simpa [prefixWord, tailWord_392481, baseEnd_392481] using wordTrace_append hprefix tailTrace_392481
  have hstable : (prefixWord ++ tailWord_392481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392481).length < 2 ^ (prefixWord ++ tailWord_392481).sum := by decide
  have hdescent : baseEnd_392481 < baseStart_392481 := by decide
  rcases family_descends (prefixWord ++ tailWord_392481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392485 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_392485 : Nat := 118140960795 + 392485 * 2 ^ 59
def prefixEnd_392485 : Nat := 4983230072969 + 3 ^ 40 * 392485 * 2
def baseEnd_392485 : Nat := 134355636453334756221667

theorem tailTrace_392485 : CollatzResearch.WordTrace tailWord_392485 prefixEnd_392485 134355636453334756221667 := by
  unfold tailWord_392485
  simp only [CollatzResearch.WordTrace]
  refine ⟨14315103983101350946490909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9543402655400900630993939 14315103983101350946490909)
  ·
    refine ⟨5368163993663006604934091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14315103983101350946490909 5368163993663006604934091)
    ·
      refine ⟨8052245990494509907401137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5368163993663006604934091 8052245990494509907401137)
      ·
        refine ⟨6039184492870882430550853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8052245990494509907401137 6039184492870882430550853)
        ·
          refine ⟨1132347092413290455728285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6039184492870882430550853 1132347092413290455728285)
          ·
            refine ⟨424630159654983920898107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1132347092413290455728285 424630159654983920898107)
            ·
              refine ⟨636945239482475881347161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424630159654983920898107 636945239482475881347161)
              ·
                refine ⟨477708929611856911010371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636945239482475881347161 477708929611856911010371)
                ·
                  refine ⟨716563394417785366515557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477708929611856911010371 716563394417785366515557)
                  ·
                    refine ⟨134355636453334756221667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716563394417785366515557 134355636453334756221667)
                    ·
                      rfl

theorem cell22_392485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_392485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392485 prefixEnd_392485 := by exact prefixLift 392485
  have htrace : WordTrace (prefixWord ++ tailWord_392485) baseStart_392485 baseEnd_392485 := by
    simpa [prefixWord, tailWord_392485, baseEnd_392485] using wordTrace_append hprefix tailTrace_392485
  have hstable : (prefixWord ++ tailWord_392485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392485).length < 2 ^ (prefixWord ++ tailWord_392485).sum := by decide
  have hdescent : baseEnd_392485 < baseStart_392485 := by decide
  rcases family_descends (prefixWord ++ tailWord_392485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392498 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_392498 : Nat := 118140960795 + 392498 * 2 ^ 59
def prefixEnd_392498 : Nat := 4983230072969 + 3 ^ 40 * 392498 * 2
def baseEnd_392498 : Nat := 134360086619007055646627

theorem tailTrace_392498 : CollatzResearch.WordTrace tailWord_392498 prefixEnd_392498 134360086619007055646627 := by
  unfold tailWord_392498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578894533013563541678537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9543718754702836111142765 3578894533013563541678537)
  ·
    refine ⟨2684170899760172656258903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3578894533013563541678537 2684170899760172656258903)
    ·
      refine ⟨4026256349640258984388355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2684170899760172656258903 4026256349640258984388355)
      ·
        refine ⟨6039384524460388476582533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026256349640258984388355 6039384524460388476582533)
        ·
          refine ⟨1132384598336322839359225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6039384524460388476582533 1132384598336322839359225)
          ·
            refine ⟨849288448752242129519419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132384598336322839359225 849288448752242129519419)
            ·
              refine ⟨1273932673128363194279129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849288448752242129519419 1273932673128363194279129)
              ·
                refine ⟨955449504846272395709347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273932673128363194279129 955449504846272395709347)
                ·
                  refine ⟨1433174257269408593564021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955449504846272395709347 1433174257269408593564021)
                  ·
                    refine ⟨134360086619007055646627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1433174257269408593564021 134360086619007055646627)
                    ·
                      rfl

theorem cell22_392498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_392498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392498 prefixEnd_392498 := by exact prefixLift 392498
  have htrace : WordTrace (prefixWord ++ tailWord_392498) baseStart_392498 baseEnd_392498 := by
    simpa [prefixWord, tailWord_392498, baseEnd_392498] using wordTrace_append hprefix tailTrace_392498
  have hstable : (prefixWord ++ tailWord_392498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392498).length < 2 ^ (prefixWord ++ tailWord_392498).sum := by decide
  have hdescent : baseEnd_392498 < baseStart_392498 := by decide
  rcases family_descends (prefixWord ++ tailWord_392498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392500 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 4]
def baseStart_392500 : Nat := 118140960795 + 392500 * 2 ^ 59
def prefixEnd_392500 : Nat := 4983230072969 + 3 ^ 40 * 392500 * 2
def baseEnd_392500 : Nat := 44786923753293239032207

theorem tailTrace_392500 : CollatzResearch.WordTrace tailWord_392500 prefixEnd_392500 44786923753293239032207 := by
  unfold tailWord_392500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157825539023504254143477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9543767385364672338857969 7157825539023504254143477)
  ·
    refine ⟨671046144283453523825951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7157825539023504254143477 671046144283453523825951)
    ·
      refine ⟨1006569216425180285738927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671046144283453523825951 1006569216425180285738927)
      ·
        refine ⟨1509853824637770428608391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006569216425180285738927 1509853824637770428608391)
        ·
          refine ⟨2264780736956655642912587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509853824637770428608391 2264780736956655642912587)
          ·
            refine ⟨3397171105434983464368881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264780736956655642912587 3397171105434983464368881)
            ·
              refine ⟨2547878329076237598276661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3397171105434983464368881 2547878329076237598276661)
              ·
                refine ⟨238863593350897274838437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2547878329076237598276661 238863593350897274838437)
                ·
                  refine ⟨44786923753293239032207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238863593350897274838437 44786923753293239032207)
                  ·
                    rfl

theorem cell22_392500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_392500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392500 prefixEnd_392500 := by exact prefixLift 392500
  have htrace : WordTrace (prefixWord ++ tailWord_392500) baseStart_392500 baseEnd_392500 := by
    simpa [prefixWord, tailWord_392500, baseEnd_392500] using wordTrace_append hprefix tailTrace_392500
  have hstable : (prefixWord ++ tailWord_392500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392500).length < 2 ^ (prefixWord ++ tailWord_392500).sum := by decide
  have hdescent : baseEnd_392500 < baseStart_392500 := by decide
  rcases family_descends (prefixWord ++ tailWord_392500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392534 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_392534 : Nat := 118140960795 + 392534 * 2 ^ 59
def prefixEnd_392534 : Nat := 4983230072969 + 3 ^ 40 * 392534 * 2
def baseEnd_392534 : Nat := 44790803384904987248839

theorem tailTrace_392534 : CollatzResearch.WordTrace tailWord_392534 prefixEnd_392534 44790803384904987248839 := by
  unfold tailWord_392534
  simp only [CollatzResearch.WordTrace]
  refine ⟨894805697495239519689041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9544594106615888210016437 894805697495239519689041)
  ·
    refine ⟨671104273121429639766781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 894805697495239519689041 671104273121429639766781)
    ·
      refine ⟨251664102420536114912543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 671104273121429639766781 251664102420536114912543)
      ·
        refine ⟨377496153630804172368815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251664102420536114912543 377496153630804172368815)
        ·
          refine ⟨566244230446206258553223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377496153630804172368815 566244230446206258553223)
          ·
            refine ⟨849366345669309387829835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566244230446206258553223 849366345669309387829835)
            ·
              refine ⟨1274049518503964081744753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849366345669309387829835 1274049518503964081744753)
              ·
                refine ⟨955537138877973061308565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274049518503964081744753 955537138877973061308565)
                ·
                  refine ⟨44790803384904987248839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 955537138877973061308565 44790803384904987248839)
                  ·
                    rfl

theorem cell22_392534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_392534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392534 prefixEnd_392534 := by exact prefixLift 392534
  have htrace : WordTrace (prefixWord ++ tailWord_392534) baseStart_392534 baseEnd_392534 := by
    simpa [prefixWord, tailWord_392534, baseEnd_392534] using wordTrace_append hprefix tailTrace_392534
  have hstable : (prefixWord ++ tailWord_392534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392534).length < 2 ^ (prefixWord ++ tailWord_392534).sum := by decide
  have hdescent : baseEnd_392534 < baseStart_392534 := by decide
  rcases family_descends (prefixWord ++ tailWord_392534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392571 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_392571 : Nat := 118140960795 + 392571 * 2 ^ 59
def prefixEnd_392571 : Nat := 4983230072969 + 3 ^ 40 * 392571 * 2
def baseEnd_392571 : Nat := 134385076010859198571403

theorem tailTrace_392571 : CollatzResearch.WordTrace tailWord_392571 prefixEnd_392571 134385076010859198571403 := by
  unfold tailWord_392571
  simp only [CollatzResearch.WordTrace]
  refine ⟨14318240660789787634121567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9545493773859858422747711 14318240660789787634121567)
  ·
    refine ⟨21477360991184681451182351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14318240660789787634121567 21477360991184681451182351)
    ·
      refine ⟨32216041486777022176773527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21477360991184681451182351 32216041486777022176773527)
      ·
        refine ⟨48324062230165533265160291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32216041486777022176773527 48324062230165533265160291)
        ·
          refine ⟨72486093345248299897740437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48324062230165533265160291 72486093345248299897740437)
          ·
            refine ⟨3397785625558514057706583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72486093345248299897740437 3397785625558514057706583)
            ·
              refine ⟨5096678438337771086559875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397785625558514057706583 5096678438337771086559875)
              ·
                refine ⟨7645017657506656629839813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096678438337771086559875 7645017657506656629839813)
                ·
                  refine ⟨1433440810782498118094965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7645017657506656629839813 1433440810782498118094965)
                  ·
                    refine ⟨134385076010859198571403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1433440810782498118094965 134385076010859198571403)
                    ·
                      rfl

theorem cell22_392571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_392571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392571 prefixEnd_392571 := by exact prefixLift 392571
  have htrace : WordTrace (prefixWord ++ tailWord_392571) baseStart_392571 baseEnd_392571 := by
    simpa [prefixWord, tailWord_392571, baseEnd_392571] using wordTrace_append hprefix tailTrace_392571
  have hstable : (prefixWord ++ tailWord_392571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392571).length < 2 ^ (prefixWord ++ tailWord_392571).sum := by decide
  have hdescent : baseEnd_392571 < baseStart_392571 := by decide
  rcases family_descends (prefixWord ++ tailWord_392571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392577 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_392577 : Nat := 118140960795 + 392577 * 2 ^ 59
def prefixEnd_392577 : Nat := 4983230072969 + 3 ^ 40 * 392577 * 2
def baseEnd_392577 : Nat := 134387129933477182921385

theorem tailTrace_392577 : CollatzResearch.WordTrace tailWord_392577 prefixEnd_392577 134387129933477182921385 := by
  unfold tailWord_392577
  simp only [CollatzResearch.WordTrace]
  refine ⟨14318459498768050658839985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9545639665845367105893323 14318459498768050658839985)
  ·
    refine ⟨10738844624076037994129989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14318459498768050658839985 10738844624076037994129989)
    ·
      refine ⟨2013533367014257123899373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10738844624076037994129989 2013533367014257123899373)
      ·
        refine ⟨755075012630346421462265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2013533367014257123899373 755075012630346421462265)
        ·
          refine ⟨566306259472759816096699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755075012630346421462265 566306259472759816096699)
          ·
            refine ⟨849459389209139724145049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566306259472759816096699 849459389209139724145049)
            ·
              refine ⟨637094541906854793108787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849459389209139724145049 637094541906854793108787)
              ·
                refine ⟨955641812860282189663181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637094541906854793108787 955641812860282189663181)
                ·
                  refine ⟨358365679822605821123693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955641812860282189663181 358365679822605821123693)
                  ·
                    refine ⟨134387129933477182921385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358365679822605821123693 134387129933477182921385)
                    ·
                      rfl

theorem cell22_392577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_392577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392577 prefixEnd_392577 := by exact prefixLift 392577
  have htrace : WordTrace (prefixWord ++ tailWord_392577) baseStart_392577 baseEnd_392577 := by
    simpa [prefixWord, tailWord_392577, baseEnd_392577] using wordTrace_append hprefix tailTrace_392577
  have hstable : (prefixWord ++ tailWord_392577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392577).length < 2 ^ (prefixWord ++ tailWord_392577).sum := by decide
  have hdescent : baseEnd_392577 < baseStart_392577 := by decide
  rcases family_descends (prefixWord ++ tailWord_392577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392648 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_392648 : Nat := 118140960795 + 392648 * 2 ^ 59
def prefixEnd_392648 : Nat := 4983230072969 + 3 ^ 40 * 392648 * 2
def baseEnd_392648 : Nat := 134411434684456664396167

theorem tailTrace_392648 : CollatzResearch.WordTrace tailWord_392648 prefixEnd_392648 134411434684456664396167 := by
  unfold tailWord_392648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160524540755414892337299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9547366054340553189783065 7160524540755414892337299)
  ·
    refine ⟨10740786811133122338505949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160524540755414892337299 10740786811133122338505949)
    ·
      refine ⟨4027795054174920876939731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10740786811133122338505949 4027795054174920876939731)
      ·
        refine ⟨6041692581262381315409597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027795054174920876939731 6041692581262381315409597)
        ·
          refine ⟨2265634717973392993278599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6041692581262381315409597 2265634717973392993278599)
          ·
            refine ⟨3398452076960089489917899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265634717973392993278599 3398452076960089489917899)
            ·
              refine ⟨5097678115440134234876849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398452076960089489917899 5097678115440134234876849)
              ·
                refine ⟨3823258586580100676157637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097678115440134234876849 3823258586580100676157637)
                ·
                  refine ⟨716860984983768876779557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3823258586580100676157637 716860984983768876779557)
                  ·
                    refine ⟨134411434684456664396167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716860984983768876779557 134411434684456664396167)
                    ·
                      rfl

theorem cell22_392648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_392648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392648 prefixEnd_392648 := by exact prefixLift 392648
  have htrace : WordTrace (prefixWord ++ tailWord_392648) baseStart_392648 baseEnd_392648 := by
    simpa [prefixWord, tailWord_392648, baseEnd_392648] using wordTrace_append hprefix tailTrace_392648
  have hstable : (prefixWord ++ tailWord_392648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392648).length < 2 ^ (prefixWord ++ tailWord_392648).sum := by decide
  have hdescent : baseEnd_392648 < baseStart_392648 := by decide
  rcases family_descends (prefixWord ++ tailWord_392648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392665 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_392665 : Nat := 118140960795 + 392665 * 2 ^ 59
def prefixEnd_392665 : Nat := 4983230072969 + 3 ^ 40 * 392665 * 2
def baseEnd_392665 : Nat := 134417254131874286721115

theorem tailTrace_392665 : CollatzResearch.WordTrace tailWord_392665 prefixEnd_392665 134417254131874286721115 := by
  unfold tailWord_392665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14321669122449241688043449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9547779414966161125362299 14321669122449241688043449)
  ·
    refine ⟨10741251841836931266032587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14321669122449241688043449 10741251841836931266032587)
    ·
      refine ⟨16111877762755396899048881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10741251841836931266032587 16111877762755396899048881)
      ·
        refine ⟨12083908322066547674286661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16111877762755396899048881 12083908322066547674286661)
        ·
          refine ⟨2265732810387477688928749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12083908322066547674286661 2265732810387477688928749)
          ·
            refine ⟨849649803895304133348281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2265732810387477688928749 849649803895304133348281)
            ·
              refine ⟨637237352921478100011211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849649803895304133348281 637237352921478100011211)
              ·
                refine ⟨955856029382217150016817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637237352921478100011211 955856029382217150016817)
                ·
                  refine ⟨716892022036662862512613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955856029382217150016817 716892022036662862512613)
                  ·
                    refine ⟨134417254131874286721115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716892022036662862512613 134417254131874286721115)
                    ·
                      rfl

theorem cell22_392665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_392665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392665 prefixEnd_392665 := by exact prefixLift 392665
  have htrace : WordTrace (prefixWord ++ tailWord_392665) baseStart_392665 baseEnd_392665 := by
    simpa [prefixWord, tailWord_392665, baseEnd_392665] using wordTrace_append hprefix tailTrace_392665
  have hstable : (prefixWord ++ tailWord_392665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392665).length < 2 ^ (prefixWord ++ tailWord_392665).sum := by decide
  have hdescent : baseEnd_392665 < baseStart_392665 := by decide
  rcases family_descends (prefixWord ++ tailWord_392665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392785 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_392785 : Nat := 118140960795 + 392785 * 2 ^ 59
def prefixEnd_392785 : Nat := 4983230072969 + 3 ^ 40 * 392785 * 2
def baseEnd_392785 : Nat := 134458332584233973720747

theorem tailTrace_392785 : CollatzResearch.WordTrace tailWord_392785 prefixEnd_392785 134458332584233973720747 := by
  unfold tailWord_392785
  simp only [CollatzResearch.WordTrace]
  refine ⟨14326045882014502182411809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9550697254676334788274539 14326045882014502182411809)
  ·
    refine ⟨10744534411510876636808857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14326045882014502182411809 10744534411510876636808857)
    ·
      refine ⟨8058400808633157477606643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10744534411510876636808857 8058400808633157477606643)
      ·
        refine ⟨12087601212949736216409965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8058400808633157477606643 12087601212949736216409965)
        ·
          refine ⟨4532850454856151081153737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12087601212949736216409965 4532850454856151081153737)
          ·
            refine ⟨3399637841142113310865303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4532850454856151081153737 3399637841142113310865303)
            ·
              refine ⟨5099456761713169966297955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399637841142113310865303 5099456761713169966297955)
              ·
                refine ⟨7649185142569754949446933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099456761713169966297955 7649185142569754949446933)
                ·
                  refine ⟨358555553557957263255325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7649185142569754949446933 358555553557957263255325)
                  ·
                    refine ⟨134458332584233973720747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358555553557957263255325 134458332584233973720747)
                    ·
                      rfl

theorem cell22_392785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_392785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392785 prefixEnd_392785 := by exact prefixLift 392785
  have htrace : WordTrace (prefixWord ++ tailWord_392785) baseStart_392785 baseEnd_392785 := by
    simpa [prefixWord, tailWord_392785, baseEnd_392785] using wordTrace_append hprefix tailTrace_392785
  have hstable : (prefixWord ++ tailWord_392785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392785).length < 2 ^ (prefixWord ++ tailWord_392785).sum := by decide
  have hdescent : baseEnd_392785 < baseStart_392785 := by decide
  rcases family_descends (prefixWord ++ tailWord_392785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392804 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 4]
def baseStart_392804 : Nat := 118140960795 + 392804 * 2 ^ 59
def prefixEnd_392804 : Nat := 4983230072969 + 3 ^ 40 * 392804 * 2
def baseEnd_392804 : Nat := 44821612224174752498563

theorem tailTrace_392804 : CollatzResearch.WordTrace tailWord_392804 prefixEnd_392804 44821612224174752498563 := by
  unfold tailWord_392804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163369434472834213676733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9551159245963778951568977 7163369434472834213676733)
  ·
    refine ⟨2686263537927312830128775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7163369434472834213676733 2686263537927312830128775)
    ·
      refine ⟨4029395306890969245193163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686263537927312830128775 4029395306890969245193163)
      ·
        refine ⟨6044092960336453867789745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029395306890969245193163 6044092960336453867789745)
        ·
          refine ⟨4533069720252340400842309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6044092960336453867789745 4533069720252340400842309)
          ·
            refine ⟨849950572547313825157933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4533069720252340400842309 849950572547313825157933)
            ·
              refine ⟨318731464705242684434225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849950572547313825157933 318731464705242684434225)
              ·
                refine ⟨239048598528932013325669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318731464705242684434225 239048598528932013325669)
                ·
                  refine ⟨44821612224174752498563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239048598528932013325669 44821612224174752498563)
                  ·
                    rfl

theorem cell22_392804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_392804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392804 prefixEnd_392804 := by exact prefixLift 392804
  have htrace : WordTrace (prefixWord ++ tailWord_392804) baseStart_392804 baseEnd_392804 := by
    simpa [prefixWord, tailWord_392804, baseEnd_392804] using wordTrace_append hprefix tailTrace_392804
  have hstable : (prefixWord ++ tailWord_392804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392804).length < 2 ^ (prefixWord ++ tailWord_392804).sum := by decide
  have hdescent : baseEnd_392804 < baseStart_392804 := by decide
  rcases family_descends (prefixWord ++ tailWord_392804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392862 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_392862 : Nat := 118140960795 + 392862 * 2 ^ 59
def prefixEnd_392862 : Nat := 4983230072969 + 3 ^ 40 * 392862 * 2
def baseEnd_392862 : Nat := 134484691257831439545511

theorem tailTrace_392862 : CollatzResearch.WordTrace tailWord_392862 prefixEnd_392862 134484691257831439545511 := by
  unfold tailWord_392862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791106787841943041620605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9552569535157029555309893 1791106787841943041620605)
  ·
    refine ⟨671665045440728640607727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1791106787841943041620605 671665045440728640607727)
    ·
      refine ⟨1007497568161092960911591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671665045440728640607727 1007497568161092960911591)
      ·
        refine ⟨1511246352241639441367387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007497568161092960911591 1511246352241639441367387)
        ·
          refine ⟨2266869528362459162051081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511246352241639441367387 2266869528362459162051081)
          ·
            refine ⟨1700152146271844371538311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2266869528362459162051081 1700152146271844371538311)
            ·
              refine ⟨2550228219407766557307467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700152146271844371538311 2550228219407766557307467)
              ·
                refine ⟨3825342329111649835961201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550228219407766557307467 3825342329111649835961201)
                ·
                  refine ⟨2869006746833737376970901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825342329111649835961201 2869006746833737376970901)
                  ·
                    refine ⟨134484691257831439545511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2869006746833737376970901 134484691257831439545511)
                    ·
                      rfl

theorem cell22_392862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_392862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392862 prefixEnd_392862 := by exact prefixLift 392862
  have htrace : WordTrace (prefixWord ++ tailWord_392862) baseStart_392862 baseEnd_392862 := by
    simpa [prefixWord, tailWord_392862, baseEnd_392862] using wordTrace_append hprefix tailTrace_392862
  have hstable : (prefixWord ++ tailWord_392862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392862).length < 2 ^ (prefixWord ++ tailWord_392862).sum := by decide
  have hdescent : baseEnd_392862 < baseStart_392862 := by decide
  rcases family_descends (prefixWord ++ tailWord_392862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392866 : List Nat := [3, 3, 1, 4, 2, 1, 1, 7]
def baseStart_392866 : Nat := 118140960795 + 392866 * 2 ^ 59
def prefixEnd_392866 : Nat := 4983230072969 + 3 ^ 40 * 392866 * 2
def baseEnd_392866 : Nat := 14942895615508529160611

theorem tailTrace_392866 : CollatzResearch.WordTrace tailWord_392866 prefixEnd_392866 14942895615508529160611 := by
  unfold tailWord_392866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582250048680263254027613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9552666796480702010740301 3582250048680263254027613)
  ·
    refine ⟨1343343768255098720260355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3582250048680263254027613 1343343768255098720260355)
    ·
      refine ⟨2015015652382648080390533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343343768255098720260355 2015015652382648080390533)
      ·
        refine ⟨377815434821746515073225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2015015652382648080390533 377815434821746515073225)
        ·
          refine ⟨283361576116309886304919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377815434821746515073225 283361576116309886304919)
          ·
            refine ⟨425042364174464829457379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283361576116309886304919 425042364174464829457379)
            ·
              refine ⟨637563546261697244186069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425042364174464829457379 637563546261697244186069)
              ·
                refine ⟨14942895615508529160611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 637563546261697244186069 14942895615508529160611)
                ·
                  rfl

theorem cell22_392866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_392866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392866 prefixEnd_392866 := by exact prefixLift 392866
  have htrace : WordTrace (prefixWord ++ tailWord_392866) baseStart_392866 baseEnd_392866 := by
    simpa [prefixWord, tailWord_392866, baseEnd_392866] using wordTrace_append hprefix tailTrace_392866
  have hstable : (prefixWord ++ tailWord_392866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392866).length < 2 ^ (prefixWord ++ tailWord_392866).sum := by decide
  have hdescent : baseEnd_392866 < baseStart_392866 := by decide
  rcases family_descends (prefixWord ++ tailWord_392866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392877 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 5]
def baseStart_392877 : Nat := 118140960795 + 392877 * 2 ^ 59
def prefixEnd_392877 : Nat := 4983230072969 + 3 ^ 40 * 392877 * 2
def baseEnd_392877 : Nat := 44829942021458800140155

theorem tailTrace_392877 : CollatzResearch.WordTrace tailWord_392877 prefixEnd_392877 44829942021458800140155 := by
  unfold tailWord_392877
  simp only [CollatzResearch.WordTrace]
  refine ⟨14329401397681201894760885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9552934265120801263173923 14329401397681201894760885)
  ·
    refine ⟨1343381381032612677633833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14329401397681201894760885 1343381381032612677633833)
    ·
      refine ⟨1007536035774459508225375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1343381381032612677633833 1007536035774459508225375)
      ·
        refine ⟨1511304053661689262338063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007536035774459508225375 1511304053661689262338063)
        ·
          refine ⟨2266956080492533893507095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511304053661689262338063 2266956080492533893507095)
          ·
            refine ⟨3400434120738800840260643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266956080492533893507095 3400434120738800840260643)
            ·
              refine ⟨5100651181108201260390965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400434120738800840260643 5100651181108201260390965)
              ·
                refine ⟨478186048228893868161653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5100651181108201260390965 478186048228893868161653)
                ·
                  refine ⟨44829942021458800140155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 478186048228893868161653 44829942021458800140155)
                  ·
                    rfl

theorem cell22_392877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_392877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392877 prefixEnd_392877 := by exact prefixLift 392877
  have htrace : WordTrace (prefixWord ++ tailWord_392877) baseStart_392877 baseEnd_392877 := by
    simpa [prefixWord, tailWord_392877, baseEnd_392877] using wordTrace_append hprefix tailTrace_392877
  have hstable : (prefixWord ++ tailWord_392877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392877).length < 2 ^ (prefixWord ++ tailWord_392877).sum := by decide
  have hdescent : baseEnd_392877 < baseStart_392877 := by decide
  rcases family_descends (prefixWord ++ tailWord_392877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392909 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_392909 : Nat := 118140960795 + 392909 * 2 ^ 59
def prefixEnd_392909 : Nat := 4983230072969 + 3 ^ 40 * 392909 * 2
def baseEnd_392909 : Nat := 134500780318338983620367

theorem tailTrace_392909 : CollatzResearch.WordTrace tailWord_392909 prefixEnd_392909 134500780318338983620367 := by
  unfold tailWord_392909
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330568533565271359925781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9553712355710180906617187 14330568533565271359925781)
  ·
    refine ⟨671745400010872094996521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14330568533565271359925781 671745400010872094996521)
    ·
      refine ⟨503809050008154071247391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 671745400010872094996521 503809050008154071247391)
      ·
        refine ⟨755713575012231106871087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503809050008154071247391 755713575012231106871087)
        ·
          refine ⟨1133570362518346660306631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755713575012231106871087 1133570362518346660306631)
          ·
            refine ⟨1700355543777519990459947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133570362518346660306631 1700355543777519990459947)
            ·
              refine ⟨2550533315666279985689921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700355543777519990459947 2550533315666279985689921)
              ·
                refine ⟨1912899986749709989267441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550533315666279985689921 1912899986749709989267441)
                ·
                  refine ⟨1434674990062282491950581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1912899986749709989267441 1434674990062282491950581)
                  ·
                    refine ⟨134500780318338983620367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1434674990062282491950581 134500780318338983620367)
                    ·
                      rfl

theorem cell22_392909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_392909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392909 prefixEnd_392909 := by exact prefixLift 392909
  have htrace : WordTrace (prefixWord ++ tailWord_392909) baseStart_392909 baseEnd_392909 := by
    simpa [prefixWord, tailWord_392909, baseEnd_392909] using wordTrace_append hprefix tailTrace_392909
  have hstable : (prefixWord ++ tailWord_392909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392909).length < 2 ^ (prefixWord ++ tailWord_392909).sum := by decide
  have hdescent : baseEnd_392909 < baseStart_392909 := by decide
  rcases family_descends (prefixWord ++ tailWord_392909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392922 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_392922 : Nat := 118140960795 + 392922 * 2 ^ 59
def prefixEnd_392922 : Nat := 4983230072969 + 3 ^ 40 * 392922 * 2
def baseEnd_392922 : Nat := 44835076828003761015109

theorem tailTrace_392922 : CollatzResearch.WordTrace tailWord_392922 prefixEnd_392922 44835076828003761015109 := by
  unfold tailWord_392922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582760670629543645037255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9554028455012116386766013 3582760670629543645037255)
  ·
    refine ⟨5374141005944315467555883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3582760670629543645037255 5374141005944315467555883)
    ·
      refine ⟨8061211508916473201333825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374141005944315467555883 8061211508916473201333825)
      ·
        refine ⟨6045908631687354901000369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8061211508916473201333825 6045908631687354901000369)
        ·
          refine ⟨4534431473765516175750277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6045908631687354901000369 4534431473765516175750277)
          ·
            refine ⟨850205901331034282953177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4534431473765516175750277 850205901331034282953177)
            ·
              refine ⟨637654425998275712214883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850205901331034282953177 637654425998275712214883)
              ·
                refine ⟨956481638997413568322325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637654425998275712214883 956481638997413568322325)
                ·
                  refine ⟨44835076828003761015109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 956481638997413568322325 44835076828003761015109)
                  ·
                    rfl

theorem cell22_392922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_392922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392922 prefixEnd_392922 := by exact prefixLift 392922
  have htrace : WordTrace (prefixWord ++ tailWord_392922) baseStart_392922 baseEnd_392922 := by
    simpa [prefixWord, tailWord_392922, baseEnd_392922] using wordTrace_append hprefix tailTrace_392922
  have hstable : (prefixWord ++ tailWord_392922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392922).length < 2 ^ (prefixWord ++ tailWord_392922).sum := by decide
  have hdescent : baseEnd_392922 < baseStart_392922 := by decide
  rcases family_descends (prefixWord ++ tailWord_392922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392966 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_392966 : Nat := 118140960795 + 392966 * 2 ^ 59
def prefixEnd_392966 : Nat := 4983230072969 + 3 ^ 40 * 392966 * 2
def baseEnd_392966 : Nat := 134520292583209834945193

theorem tailTrace_392966 : CollatzResearch.WordTrace tailWord_392966 prefixEnd_392966 134520292583209834945193 := by
  unfold tailWord_392966
  simp only [CollatzResearch.WordTrace]
  refine ⟨447895234198711565460961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9555098329572513396500501 447895234198711565460961)
  ·
    refine ⟨335921425649033674095721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 447895234198711565460961 335921425649033674095721)
    ·
      refine ⟨251941069236775255571791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335921425649033674095721 251941069236775255571791)
      ·
        refine ⟨377911603855162883357687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251941069236775255571791 377911603855162883357687)
        ·
          refine ⟨566867405782744325036531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377911603855162883357687 566867405782744325036531)
          ·
            refine ⟨850301108674116487554797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566867405782744325036531 850301108674116487554797)
            ·
              refine ⟨318862915752793682833049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 850301108674116487554797 318862915752793682833049)
              ·
                refine ⟨239147186814595262124787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318862915752793682833049 239147186814595262124787)
                ·
                  refine ⟨358720780221892893187181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239147186814595262124787 358720780221892893187181)
                  ·
                    refine ⟨134520292583209834945193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358720780221892893187181 134520292583209834945193)
                    ·
                      rfl

theorem cell22_392966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_392966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_392966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_392966 prefixEnd_392966 := by exact prefixLift 392966
  have htrace : WordTrace (prefixWord ++ tailWord_392966) baseStart_392966 baseEnd_392966 := by
    simpa [prefixWord, tailWord_392966, baseEnd_392966] using wordTrace_append hprefix tailTrace_392966
  have hstable : (prefixWord ++ tailWord_392966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392966).length < 2 ^ (prefixWord ++ tailWord_392966).sum := by decide
  have hdescent : baseEnd_392966 < baseStart_392966 := by decide
  rcases family_descends (prefixWord ++ tailWord_392966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393044 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_393044 : Nat := 118140960795 + 393044 * 2 ^ 59
def prefixEnd_393044 : Nat := 4983230072969 + 3 ^ 40 * 393044 * 2
def baseEnd_393044 : Nat := 134546993577243631494953

theorem tailTrace_393044 : CollatzResearch.WordTrace tailWord_393044 prefixEnd_393044 134546993577243631494953 := by
  unfold tailWord_393044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167746194038094708045093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9556994925384126277393457 7167746194038094708045093)
  ·
    refine ⟨1343952411382142757758455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7167746194038094708045093 1343952411382142757758455)
    ·
      refine ⟨2015928617073214136637683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343952411382142757758455 2015928617073214136637683)
      ·
        refine ⟨3023892925609821204956525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015928617073214136637683 3023892925609821204956525)
        ·
          refine ⟨1133959847103682951858697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3023892925609821204956525 1133959847103682951858697)
          ·
            refine ⟨850469885327762213894023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1133959847103682951858697 850469885327762213894023)
            ·
              refine ⟨1275704827991643320841035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850469885327762213894023 1275704827991643320841035)
              ·
                refine ⟨1913557241987464981261553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275704827991643320841035 1913557241987464981261553)
                ·
                  refine ⟨1435167931490598735946165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1913557241987464981261553 1435167931490598735946165)
                  ·
                    refine ⟨134546993577243631494953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1435167931490598735946165 134546993577243631494953)
                    ·
                      rfl

theorem cell22_393044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_393044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393044 prefixEnd_393044 := by exact prefixLift 393044
  have htrace : WordTrace (prefixWord ++ tailWord_393044) baseStart_393044 baseEnd_393044 := by
    simpa [prefixWord, tailWord_393044, baseEnd_393044] using wordTrace_append hprefix tailTrace_393044
  have hstable : (prefixWord ++ tailWord_393044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393044).length < 2 ^ (prefixWord ++ tailWord_393044).sum := by decide
  have hdescent : baseEnd_393044 < baseStart_393044 := by decide
  rcases family_descends (prefixWord ++ tailWord_393044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393057 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 6]
def baseStart_393057 : Nat := 118140960795 + 393057 * 2 ^ 59
def prefixEnd_393057 : Nat := 4983230072969 + 3 ^ 40 * 393057 * 2
def baseEnd_393057 : Nat := 44850481247638643639971

theorem tailTrace_393057 : CollatzResearch.WordTrace tailWord_393057 prefixEnd_393057 44850481247638643639971 := by
  unfold tailWord_393057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14335966537029092636313425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9557311024686061757542283 14335966537029092636313425)
  ·
    refine ⟨10751974902771819477235069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14335966537029092636313425 10751974902771819477235069)
    ·
      refine ⟨4031990588539432303963151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10751974902771819477235069 4031990588539432303963151)
      ·
        refine ⟨6047985882809148455944727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031990588539432303963151 6047985882809148455944727)
        ·
          refine ⟨9071978824213722683917091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047985882809148455944727 9071978824213722683917091)
          ·
            refine ⟨13607968236320584025875637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9071978824213722683917091 13607968236320584025875637)
            ·
              refine ⟨1275747022155054752425841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13607968236320584025875637 1275747022155054752425841)
              ·
                refine ⟨956810266616291064319381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275747022155054752425841 956810266616291064319381)
                ·
                  refine ⟨44850481247638643639971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 956810266616291064319381 44850481247638643639971)
                  ·
                    rfl

theorem cell22_393057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_393057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393057 prefixEnd_393057 := by exact prefixLift 393057
  have htrace : WordTrace (prefixWord ++ tailWord_393057) baseStart_393057 baseEnd_393057 := by
    simpa [prefixWord, tailWord_393057, baseEnd_393057] using wordTrace_append hprefix tailTrace_393057
  have hstable : (prefixWord ++ tailWord_393057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393057).length < 2 ^ (prefixWord ++ tailWord_393057).sum := by decide
  have hdescent : baseEnd_393057 < baseStart_393057 := by decide
  rcases family_descends (prefixWord ++ tailWord_393057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393087 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 4, 4]
def baseStart_393087 : Nat := 118140960795 + 393087 * 2 ^ 59
def prefixEnd_393087 : Nat := 4983230072969 + 3 ^ 40 * 393087 * 2
def baseEnd_393087 : Nat := 134561713356005852669821

theorem tailTrace_393087 : CollatzResearch.WordTrace tailWord_393087 prefixEnd_393087 134561713356005852669821 := by
  unfold tailWord_393087
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337060726920407759905515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9558040484613605173270343 14337060726920407759905515)
  ·
    refine ⟨21505591090380611639858273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14337060726920407759905515 21505591090380611639858273)
    ·
      refine ⟨16129193317785458729893705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21505591090380611639858273 16129193317785458729893705)
      ·
        refine ⟨12096894988339094047420279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16129193317785458729893705 12096894988339094047420279)
        ·
          refine ⟨18145342482508641071130419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12096894988339094047420279 18145342482508641071130419)
          ·
            refine ⟨27218013723762961606695629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18145342482508641071130419 27218013723762961606695629)
            ·
              refine ⟨10206755146411110602510861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27218013723762961606695629 10206755146411110602510861)
              ·
                refine ⟨3827533179904166475941573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10206755146411110602510861 3827533179904166475941573)
                ·
                  refine ⟨717662471232031214239045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3827533179904166475941573 717662471232031214239045)
                  ·
                    refine ⟨134561713356005852669821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717662471232031214239045 134561713356005852669821)
                    ·
                      rfl

theorem cell22_393087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_393087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393087 prefixEnd_393087 := by exact prefixLift 393087
  have htrace : WordTrace (prefixWord ++ tailWord_393087) baseStart_393087 baseEnd_393087 := by
    simpa [prefixWord, tailWord_393087, baseEnd_393087] using wordTrace_append hprefix tailTrace_393087
  have hstable : (prefixWord ++ tailWord_393087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393087).length < 2 ^ (prefixWord ++ tailWord_393087).sum := by decide
  have hdescent : baseEnd_393087 < baseStart_393087 := by decide
  rcases family_descends (prefixWord ++ tailWord_393087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393106 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_393106 : Nat := 118140960795 + 393106 * 2 ^ 59
def prefixEnd_393106 : Nat := 4983230072969 + 3 ^ 40 * 393106 * 2
def baseEnd_393106 : Nat := 134568217444296136444763

theorem tailTrace_393106 : CollatzResearch.WordTrace tailWord_393106 prefixEnd_393106 134568217444296136444763 := by
  unfold tailWord_393106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3584438428462893501211793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9558502475901049336564781 3584438428462893501211793)
  ·
    refine ⟨2688328821347170125908845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3584438428462893501211793 2688328821347170125908845)
    ·
      refine ⟨1008123308005188797215817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2688328821347170125908845 1008123308005188797215817)
      ·
        refine ⟨756092481003891597911863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1008123308005188797215817 756092481003891597911863)
        ·
          refine ⟨1134138721505837396867795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756092481003891597911863 1134138721505837396867795)
          ·
            refine ⟨1701208082258756095301693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134138721505837396867795 1701208082258756095301693)
            ·
              refine ⟨637953030847033535738135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1701208082258756095301693 637953030847033535738135)
              ·
                refine ⟨956929546270550303607203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637953030847033535738135 956929546270550303607203)
                ·
                  refine ⟨1435394319405825455410805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956929546270550303607203 1435394319405825455410805)
                  ·
                    refine ⟨134568217444296136444763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1435394319405825455410805 134568217444296136444763)
                    ·
                      rfl

theorem cell22_393106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_393106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393106 prefixEnd_393106 := by exact prefixLift 393106
  have htrace : WordTrace (prefixWord ++ tailWord_393106) baseStart_393106 baseEnd_393106 := by
    simpa [prefixWord, tailWord_393106, baseEnd_393106] using wordTrace_append hprefix tailTrace_393106
  have hstable : (prefixWord ++ tailWord_393106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393106).length < 2 ^ (prefixWord ++ tailWord_393106).sum := by decide
  have hdescent : baseEnd_393106 < baseStart_393106 := by decide
  rcases family_descends (prefixWord ++ tailWord_393106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393119 : List Nat := [1, 1, 2, 5, 3, 1, 1, 8]
def baseStart_393119 : Nat := 118140960795 + 393119 * 2 ^ 59
def prefixEnd_393119 : Nat := 4983230072969 + 3 ^ 40 * 393119 * 2
def baseEnd_393119 : Nat := 14952518623329826207747

theorem tailTrace_393119 : CollatzResearch.WordTrace tailWord_393119 prefixEnd_393119 14952518623329826207747 := by
  unfold tailWord_393119
  simp only [CollatzResearch.WordTrace]
  refine ⟨14338227862804477225070411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9558818575202984816713607 14338227862804477225070411)
  ·
    refine ⟨21507341794206715837605617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14338227862804477225070411 21507341794206715837605617)
    ·
      refine ⟨16130506345655036878204213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21507341794206715837605617 16130506345655036878204213)
      ·
        refine ⟨1512234969905159707331645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16130506345655036878204213 1512234969905159707331645)
        ·
          refine ⟨567088113714434890249367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1512234969905159707331645 567088113714434890249367)
          ·
            refine ⟨850632170571652335374051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567088113714434890249367 850632170571652335374051)
            ·
              refine ⟨1275948255857478503061077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850632170571652335374051 1275948255857478503061077)
              ·
                refine ⟨14952518623329826207747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1275948255857478503061077 14952518623329826207747)
                ·
                  rfl

theorem cell22_393119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 8].length) (baseStart_393119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393119 prefixEnd_393119 := by exact prefixLift 393119
  have htrace : WordTrace (prefixWord ++ tailWord_393119) baseStart_393119 baseEnd_393119 := by
    simpa [prefixWord, tailWord_393119, baseEnd_393119] using wordTrace_append hprefix tailTrace_393119
  have hstable : (prefixWord ++ tailWord_393119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393119).length < 2 ^ (prefixWord ++ tailWord_393119).sum := by decide
  have hdescent : baseEnd_393119 < baseStart_393119 := by decide
  rcases family_descends (prefixWord ++ tailWord_393119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393226 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_393226 : Nat := 118140960795 + 393226 * 2 ^ 59
def prefixEnd_393226 : Nat := 4983230072969 + 3 ^ 40 * 393226 * 2
def baseEnd_393226 : Nat := 44869765298885274481465

theorem tailTrace_393226 : CollatzResearch.WordTrace tailWord_393226 prefixEnd_393226 44869765298885274481465 := by
  unfold tailWord_393226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585532618354208624803883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9561420315611222999477021 3585532618354208624803883)
  ·
    refine ⟨5378298927531312937205825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3585532618354208624803883 5378298927531312937205825)
    ·
      refine ⟨4033724195648484702904369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5378298927531312937205825 4033724195648484702904369)
      ·
        refine ⟨3025293146736363527178277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4033724195648484702904369 3025293146736363527178277)
        ·
          refine ⟨567242465013068161345927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3025293146736363527178277 567242465013068161345927)
          ·
            refine ⟨850863697519602242018891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567242465013068161345927 850863697519602242018891)
            ·
              refine ⟨1276295546279403363028337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850863697519602242018891 1276295546279403363028337)
              ·
                refine ⟨957221659709552522271253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276295546279403363028337 957221659709552522271253)
                ·
                  refine ⟨44869765298885274481465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 957221659709552522271253 44869765298885274481465)
                  ·
                    rfl

theorem cell22_393226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_393226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393226 prefixEnd_393226 := by exact prefixLift 393226
  have htrace : WordTrace (prefixWord ++ tailWord_393226) baseStart_393226 baseEnd_393226 := by
    simpa [prefixWord, tailWord_393226, baseEnd_393226] using wordTrace_append hprefix tailTrace_393226
  have hstable : (prefixWord ++ tailWord_393226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393226).length < 2 ^ (prefixWord ++ tailWord_393226).sum := by decide
  have hdescent : baseEnd_393226 < baseStart_393226 := by decide
  rcases family_descends (prefixWord ++ tailWord_393226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393245 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_393245 : Nat := 118140960795 + 393245 * 2 ^ 59
def prefixEnd_393245 : Nat := 4983230072969 + 3 ^ 40 * 393245 * 2
def baseEnd_393245 : Nat := 134615799984946107219337

theorem tailTrace_393245 : CollatzResearch.WordTrace tailWord_393245 prefixEnd_393245 134615799984946107219337 := by
  unfold tailWord_393245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14342823460348000744157189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9561882306898667162771459 14342823460348000744157189)
  ·
    refine ⟨2689279398815250139529473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14342823460348000744157189 2689279398815250139529473)
    ·
      refine ⟨2016959549111437604647105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2689279398815250139529473 2016959549111437604647105)
      ·
        refine ⟨1512719661833578203485329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2016959549111437604647105 1512719661833578203485329)
        ·
          refine ⟨1134539746375183652613997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1512719661833578203485329 1134539746375183652613997)
          ·
            refine ⟨425452404890693869730249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1134539746375183652613997 425452404890693869730249)
            ·
              refine ⟨319089303668020402297687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425452404890693869730249 319089303668020402297687)
              ·
                refine ⟨478633955502030603446531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319089303668020402297687 478633955502030603446531)
                ·
                  refine ⟨717950933253045905169797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478633955502030603446531 717950933253045905169797)
                  ·
                    refine ⟨134615799984946107219337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 717950933253045905169797 134615799984946107219337)
                    ·
                      rfl

theorem cell22_393245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_393245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393245 prefixEnd_393245 := by exact prefixLift 393245
  have htrace : WordTrace (prefixWord ++ tailWord_393245) baseStart_393245 baseEnd_393245 := by
    simpa [prefixWord, tailWord_393245, baseEnd_393245] using wordTrace_append hprefix tailTrace_393245
  have hstable : (prefixWord ++ tailWord_393245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393245).length < 2 ^ (prefixWord ++ tailWord_393245).sum := by decide
  have hdescent : baseEnd_393245 < baseStart_393245 := by decide
  rcases family_descends (prefixWord ++ tailWord_393245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393258 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_393258 : Nat := 118140960795 + 393258 * 2 ^ 59
def prefixEnd_393258 : Nat := 4983230072969 + 3 ^ 40 * 393258 * 2
def baseEnd_393258 : Nat := 134620250150618406644297

theorem tailTrace_393258 : CollatzResearch.WordTrace tailWord_393258 prefixEnd_393258 134620250150618406644297 := by
  unfold tailWord_393258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585824402325225991095107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9562198406200602642920285 3585824402325225991095107)
  ·
    refine ⟨5378736603487838986642661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3585824402325225991095107 5378736603487838986642661)
    ·
      refine ⟨1008513113153969809995499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5378736603487838986642661 1008513113153969809995499)
      ·
        refine ⟨1512769669730954714993249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008513113153969809995499 1512769669730954714993249)
        ·
          refine ⟨1134577252298216036244937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1512769669730954714993249 1134577252298216036244937)
          ·
            refine ⟨850932939223662027183703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1134577252298216036244937 850932939223662027183703)
            ·
              refine ⟨1276399408835493040775555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850932939223662027183703 1276399408835493040775555)
              ·
                refine ⟨1914599113253239561163333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276399408835493040775555 1914599113253239561163333)
                ·
                  refine ⟨358987333734982417718125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914599113253239561163333 358987333734982417718125)
                  ·
                    refine ⟨134620250150618406644297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358987333734982417718125 134620250150618406644297)
                    ·
                      rfl

theorem cell22_393258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_393258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393258 prefixEnd_393258 := by exact prefixLift 393258
  have htrace : WordTrace (prefixWord ++ tailWord_393258) baseStart_393258 baseEnd_393258 := by
    simpa [prefixWord, tailWord_393258, baseEnd_393258] using wordTrace_append hprefix tailTrace_393258
  have hstable : (prefixWord ++ tailWord_393258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393258).length < 2 ^ (prefixWord ++ tailWord_393258).sum := by decide
  have hdescent : baseEnd_393258 < baseStart_393258 := by decide
  rcases family_descends (prefixWord ++ tailWord_393258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393344 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_393344 : Nat := 118140960795 + 393344 * 2 ^ 59
def prefixEnd_393344 : Nat := 4983230072969 + 3 ^ 40 * 393344 * 2
def baseEnd_393344 : Nat := 44883229902714282998011

theorem tailTrace_393344 : CollatzResearch.WordTrace tailWord_393344 prefixEnd_393344 44883229902714282998011 := by
  unfold tailWord_393344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173217143494670326005543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9564289524659560434674057 7173217143494670326005543)
  ·
    refine ⟨10759825715242005489008315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7173217143494670326005543 10759825715242005489008315)
    ·
      refine ⟨16139738572863008233512473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759825715242005489008315 16139738572863008233512473)
      ·
        refine ⟨12104803929647256175134355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16139738572863008233512473 12104803929647256175134355)
        ·
          refine ⟨18157205894470884262701533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12104803929647256175134355 18157205894470884262701533)
          ·
            refine ⟨6808952210426581598513075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18157205894470884262701533 6808952210426581598513075)
            ·
              refine ⟨10213428315639872397769613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808952210426581598513075 10213428315639872397769613)
              ·
                refine ⟨3830035618364952149163605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10213428315639872397769613 3830035618364952149163605)
                ·
                  refine ⟨44883229902714282998011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3830035618364952149163605 44883229902714282998011)
                  ·
                    rfl

theorem cell22_393344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_393344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393344 prefixEnd_393344 := by exact prefixLift 393344
  have htrace : WordTrace (prefixWord ++ tailWord_393344) baseStart_393344 baseEnd_393344 := by
    simpa [prefixWord, tailWord_393344, baseEnd_393344] using wordTrace_append hprefix tailTrace_393344
  have hstable : (prefixWord ++ tailWord_393344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393344).length < 2 ^ (prefixWord ++ tailWord_393344).sum := by decide
  have hdescent : baseEnd_393344 < baseStart_393344 := by decide
  rcases family_descends (prefixWord ++ tailWord_393344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393408 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_393408 : Nat := 118140960795 + 393408 * 2 ^ 59
def prefixEnd_393408 : Nat := 4983230072969 + 3 ^ 40 * 393408 * 2
def baseEnd_393408 : Nat := 134671598216068015393837

theorem tailTrace_393408 : CollatzResearch.WordTrace tailWord_393408 prefixEnd_393408 134671598216068015393837 := by
  unfold tailWord_393408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174384279378739791170439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9565845705838319721560585 7174384279378739791170439)
  ·
    refine ⟨10761576419068109686755659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7174384279378739791170439 10761576419068109686755659)
    ·
      refine ⟨16142364628602164530133489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10761576419068109686755659 16142364628602164530133489)
      ·
        refine ⟨12106773471451623397600117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16142364628602164530133489 12106773471451623397600117)
        ·
          refine ⟨1135010012948589693525011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12106773471451623397600117 1135010012948589693525011)
          ·
            refine ⟨1702515019422884540287517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135010012948589693525011 1702515019422884540287517)
            ·
              refine ⟨638443132283581702607819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1702515019422884540287517 638443132283581702607819)
              ·
                refine ⟨957664698425372553911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638443132283581702607819 957664698425372553911729)
                ·
                  refine ⟨718248523819029415433797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 957664698425372553911729 718248523819029415433797)
                  ·
                    refine ⟨134671598216068015393837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718248523819029415433797 134671598216068015393837)
                    ·
                      rfl

theorem cell22_393408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_393408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393408 prefixEnd_393408 := by exact prefixLift 393408
  have htrace : WordTrace (prefixWord ++ tailWord_393408) baseStart_393408 baseEnd_393408 := by
    simpa [prefixWord, tailWord_393408, baseEnd_393408] using wordTrace_append hprefix tailTrace_393408
  have hstable : (prefixWord ++ tailWord_393408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393408).length < 2 ^ (prefixWord ++ tailWord_393408).sum := by decide
  have hdescent : baseEnd_393408 < baseStart_393408 := by decide
  rcases family_descends (prefixWord ++ tailWord_393408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393502 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_393502 : Nat := 118140960795 + 393502 * 2 ^ 59
def prefixEnd_393502 : Nat := 4983230072969 + 3 ^ 40 * 393502 * 2
def baseEnd_393502 : Nat := 44901258779027701181183

theorem tailTrace_393502 : CollatzResearch.WordTrace tailWord_393502 prefixEnd_393502 44901258779027701181183 := by
  unfold tailWord_393502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794024627552116704532845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9568131346944622424175173 1794024627552116704532845)
  ·
    refine ⟨672759235332043764199817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1794024627552116704532845 672759235332043764199817)
    ·
      refine ⟨504569426499032823149863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 672759235332043764199817 504569426499032823149863)
      ·
        refine ⟨756854139748549234724795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504569426499032823149863 756854139748549234724795)
        ·
          refine ⟨1135281209622823852087193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756854139748549234724795 1135281209622823852087193)
          ·
            refine ⟨851460907217117889065395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135281209622823852087193 851460907217117889065395)
            ·
              refine ⟨1277191360825676833598093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851460907217117889065395 1277191360825676833598093)
              ·
                refine ⟨478946760309628812599285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1277191360825676833598093 478946760309628812599285)
                ·
                  refine ⟨44901258779027701181183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 478946760309628812599285 44901258779027701181183)
                  ·
                    rfl

theorem cell22_393502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_393502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393502 prefixEnd_393502 := by exact prefixLift 393502
  have htrace : WordTrace (prefixWord ++ tailWord_393502) baseStart_393502 baseEnd_393502 := by
    simpa [prefixWord, tailWord_393502, baseEnd_393502] using wordTrace_append hprefix tailTrace_393502
  have hstable : (prefixWord ++ tailWord_393502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393502).length < 2 ^ (prefixWord ++ tailWord_393502).sum := by decide
  have hdescent : baseEnd_393502 < baseStart_393502 := by decide
  rcases family_descends (prefixWord ++ tailWord_393502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393528 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_393528 : Nat := 118140960795 + 393528 * 2 ^ 59
def prefixEnd_393528 : Nat := 4983230072969 + 3 ^ 40 * 393528 * 2
def baseEnd_393528 : Nat := 134712676668427702393469

theorem tailTrace_393528 : CollatzResearch.WordTrace tailWord_393528 prefixEnd_393528 134712676668427702393469 := by
  unfold tailWord_393528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176572659161370038354619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9568763545548493384472825 7176572659161370038354619)
  ·
    refine ⟨10764858988742055057531929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7176572659161370038354619 10764858988742055057531929)
    ·
      refine ⟨8073644241556541293148947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10764858988742055057531929 8073644241556541293148947)
      ·
        refine ⟨12110466362334811939723421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8073644241556541293148947 12110466362334811939723421)
        ·
          refine ⟨4541424885875554477396283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12110466362334811939723421 4541424885875554477396283)
          ·
            refine ⟨6812137328813331716094425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541424885875554477396283 6812137328813331716094425)
            ·
              refine ⟨5109102996609998787070819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6812137328813331716094425 5109102996609998787070819)
              ·
                refine ⟨7663654494914998180606229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5109102996609998787070819 7663654494914998180606229)
                ·
                  refine ⟨359233804449140539715917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7663654494914998180606229 359233804449140539715917)
                  ·
                    refine ⟨134712676668427702393469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 359233804449140539715917 134712676668427702393469)
                    ·
                      rfl

theorem cell22_393528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_393528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393528 prefixEnd_393528 := by exact prefixLift 393528
  have htrace : WordTrace (prefixWord ++ tailWord_393528) baseStart_393528 baseEnd_393528 := by
    simpa [prefixWord, tailWord_393528, baseEnd_393528] using wordTrace_append hprefix tailTrace_393528
  have hstable : (prefixWord ++ tailWord_393528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393528).length < 2 ^ (prefixWord ++ tailWord_393528).sum := by decide
  have hdescent : baseEnd_393528 < baseStart_393528 := by decide
  rcases family_descends (prefixWord ++ tailWord_393528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393543 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 2, 4]
def baseStart_393543 : Nat := 118140960795 + 393543 * 2 ^ 59
def prefixEnd_393543 : Nat := 4983230072969 + 3 ^ 40 * 393543 * 2
def baseEnd_393543 : Nat := 134717811474972663268423

theorem tailTrace_393543 : CollatzResearch.WordTrace tailWord_393543 prefixEnd_393543 134717811474972663268423 := by
  unfold tailWord_393543
  simp only [CollatzResearch.WordTrace]
  refine ⟨14353692413268397638505283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9569128275512265092336855 14353692413268397638505283)
  ·
    refine ⟨21530538619902596457757925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14353692413268397638505283 21530538619902596457757925)
    ·
      refine ⟨4036975991231736835829611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21530538619902596457757925 4036975991231736835829611)
      ·
        refine ⟨6055463986847605253744417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036975991231736835829611 6055463986847605253744417)
        ·
          refine ⟨4541597990135703940308313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6055463986847605253744417 4541597990135703940308313)
          ·
            refine ⟨3406198492601777955231235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4541597990135703940308313 3406198492601777955231235)
            ·
              refine ⟨5109297738902666932846853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406198492601777955231235 5109297738902666932846853)
              ·
                refine ⟨957993326044250049908785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5109297738902666932846853 957993326044250049908785)
                ·
                  refine ⟨718494994533187537431589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 957993326044250049908785 718494994533187537431589)
                  ·
                    refine ⟨134717811474972663268423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718494994533187537431589 134717811474972663268423)
                    ·
                      rfl

theorem cell22_393543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_393543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393543 prefixEnd_393543 := by exact prefixLift 393543
  have htrace : WordTrace (prefixWord ++ tailWord_393543) baseStart_393543 baseEnd_393543 := by
    simpa [prefixWord, tailWord_393543, baseEnd_393543] using wordTrace_append hprefix tailTrace_393543
  have hstable : (prefixWord ++ tailWord_393543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393543).length < 2 ^ (prefixWord ++ tailWord_393543).sum := by decide
  have hdescent : baseEnd_393543 < baseStart_393543 := by decide
  rcases family_descends (prefixWord ++ tailWord_393543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393575 : List Nat := [1, 1, 5, 1, 3, 2, 3, 6]
def baseStart_393575 : Nat := 118140960795 + 393575 * 2 ^ 59
def prefixEnd_393575 : Nat := 4983230072969 + 3 ^ 40 * 393575 * 2
def baseEnd_393575 : Nat := 14969862858770582940925

theorem tailTrace_393575 : CollatzResearch.WordTrace tailWord_393575 prefixEnd_393575 14969862858770582940925 := by
  unfold tailWord_393575
  simp only [CollatzResearch.WordTrace]
  refine ⟨14354859549152467103670179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9569906366101644735780119 14354859549152467103670179)
  ·
    refine ⟨21532289323728700655505269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14354859549152467103670179 21532289323728700655505269)
    ·
      refine ⟨2018652124099565686453619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21532289323728700655505269 2018652124099565686453619)
      ·
        refine ⟨3027978186149348529680429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018652124099565686453619 3027978186149348529680429)
        ·
          refine ⟨1135491819806005698630161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3027978186149348529680429 1135491819806005698630161)
          ·
            refine ⟨851618864854504273972621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135491819806005698630161 851618864854504273972621)
            ·
              refine ⟨319357074320439102739733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 851618864854504273972621 319357074320439102739733)
              ·
                refine ⟨14969862858770582940925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 319357074320439102739733 14969862858770582940925)
                ·
                  rfl

theorem cell22_393575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 6].length) (baseStart_393575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393575 prefixEnd_393575 := by exact prefixLift 393575
  have htrace : WordTrace (prefixWord ++ tailWord_393575) baseStart_393575 baseEnd_393575 := by
    simpa [prefixWord, tailWord_393575, baseEnd_393575] using wordTrace_append hprefix tailTrace_393575
  have hstable : (prefixWord ++ tailWord_393575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393575).length < 2 ^ (prefixWord ++ tailWord_393575).sum := by decide
  have hdescent : baseEnd_393575 < baseStart_393575 := by decide
  rcases family_descends (prefixWord ++ tailWord_393575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393607 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 1, 3]
def baseStart_393607 : Nat := 118140960795 + 393607 * 2 ^ 59
def prefixEnd_393607 : Nat := 4983230072969 + 3 ^ 40 * 393607 * 2
def baseEnd_393607 : Nat := 134739719982897829668227

theorem tailTrace_393607 : CollatzResearch.WordTrace tailWord_393607 prefixEnd_393607 134739719982897829668227 := by
  unfold tailWord_393607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14356026685036536568835075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9570684456691024379223383 14356026685036536568835075)
  ·
    refine ⟨21534040027554804853252613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14356026685036536568835075 21534040027554804853252613)
    ·
      refine ⟨4037632505166525909984865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21534040027554804853252613 4037632505166525909984865)
      ·
        refine ⟨3028224378874894432488649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4037632505166525909984865 3028224378874894432488649)
        ·
          refine ⟨2271168284156170824366487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3028224378874894432488649 2271168284156170824366487)
          ·
            refine ⟨3406752426234256236549731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271168284156170824366487 3406752426234256236549731)
            ·
              refine ⟨5110128639351384354824597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406752426234256236549731 5110128639351384354824597)
              ·
                refine ⟨239537279969596141632403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5110128639351384354824597 239537279969596141632403)
                ·
                  refine ⟨359305919954394212448605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239537279969596141632403 359305919954394212448605)
                  ·
                    refine ⟨134739719982897829668227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 359305919954394212448605 134739719982897829668227)
                    ·
                      rfl

theorem cell22_393607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_393607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393607 prefixEnd_393607 := by exact prefixLift 393607
  have htrace : WordTrace (prefixWord ++ tailWord_393607) baseStart_393607 baseEnd_393607 := by
    simpa [prefixWord, tailWord_393607, baseEnd_393607] using wordTrace_append hprefix tailTrace_393607
  have hstable : (prefixWord ++ tailWord_393607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393607).length < 2 ^ (prefixWord ++ tailWord_393607).sum := by decide
  have hdescent : baseEnd_393607 < baseStart_393607 := by decide
  rcases family_descends (prefixWord ++ tailWord_393607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393650 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_393650 : Nat := 118140960795 + 393650 * 2 ^ 59
def prefixEnd_393650 : Nat := 4983230072969 + 3 ^ 40 * 393650 * 2
def baseEnd_393650 : Nat := 134754439761660050843095

theorem tailTrace_393650 : CollatzResearch.WordTrace tailWord_393650 prefixEnd_393650 134754439761660050843095 := by
  unfold tailWord_393650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589398755970188728162601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9571730015920503275100269 3589398755970188728162601)
  ·
    refine ⟨2692049066977641546121951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3589398755970188728162601 2692049066977641546121951)
    ·
      refine ⟨4038073600466462319182927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692049066977641546121951 4038073600466462319182927)
      ·
        refine ⟨6057110400699693478774391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038073600466462319182927 6057110400699693478774391)
        ·
          refine ⟨9085665601049540218161587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6057110400699693478774391 9085665601049540218161587)
          ·
            refine ⟨13628498401574310327242381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9085665601049540218161587 13628498401574310327242381)
            ·
              refine ⟨5110686900590366372715893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13628498401574310327242381 5110686900590366372715893)
              ·
                refine ⟨479126896930346847442115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5110686900590366372715893 479126896930346847442115)
                ·
                  refine ⟨718690345395520271163173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479126896930346847442115 718690345395520271163173)
                  ·
                    refine ⟨134754439761660050843095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718690345395520271163173 134754439761660050843095)
                    ·
                      rfl

theorem cell22_393650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_393650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393650 prefixEnd_393650 := by exact prefixLift 393650
  have htrace : WordTrace (prefixWord ++ tailWord_393650) baseStart_393650 baseEnd_393650 := by
    simpa [prefixWord, tailWord_393650, baseEnd_393650] using wordTrace_append hprefix tailTrace_393650
  have hstable : (prefixWord ++ tailWord_393650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393650).length < 2 ^ (prefixWord ++ tailWord_393650).sum := by decide
  have hdescent : baseEnd_393650 < baseStart_393650 := by decide
  rcases family_descends (prefixWord ++ tailWord_393650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393684 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_393684 : Nat := 118140960795 + 393684 * 2 ^ 59
def prefixEnd_393684 : Nat := 4983230072969 + 3 ^ 40 * 393684 * 2
def baseEnd_393684 : Nat := 134766078656495295492991

theorem tailTrace_393684 : CollatzResearch.WordTrace tailWord_393684 prefixEnd_393684 134766078656495295492991 := by
  unfold tailWord_393684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179417552878789359694053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9572556737171719146258737 7179417552878789359694053)
  ·
    refine ⟨1346140791164773004942635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7179417552878789359694053 1346140791164773004942635)
    ·
      refine ⟨2019211186747159507413953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346140791164773004942635 2019211186747159507413953)
      ·
        refine ⟨1514408390060369630560465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2019211186747159507413953 1514408390060369630560465)
        ·
          refine ⟨1135806292545277222920349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514408390060369630560465 1135806292545277222920349)
          ·
            refine ⟨425927359704478958595131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1135806292545277222920349 425927359704478958595131)
            ·
              refine ⟨638891039556718437892697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425927359704478958595131 638891039556718437892697)
              ·
                refine ⟨479168279667538828419523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638891039556718437892697 479168279667538828419523)
                ·
                  refine ⟨718752419501308242629285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479168279667538828419523 718752419501308242629285)
                  ·
                    refine ⟨134766078656495295492991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718752419501308242629285 134766078656495295492991)
                    ·
                      rfl

theorem cell22_393684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_393684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393684 prefixEnd_393684 := by exact prefixLift 393684
  have htrace : WordTrace (prefixWord ++ tailWord_393684) baseStart_393684 baseEnd_393684 := by
    simpa [prefixWord, tailWord_393684, baseEnd_393684] using wordTrace_append hprefix tailTrace_393684
  have hstable : (prefixWord ++ tailWord_393684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393684).length < 2 ^ (prefixWord ++ tailWord_393684).sum := by decide
  have hdescent : baseEnd_393684 < baseStart_393684 := by decide
  rcases family_descends (prefixWord ++ tailWord_393684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393695 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 2, 4]
def baseStart_393695 : Nat := 118140960795 + 393695 * 2 ^ 59
def prefixEnd_393695 : Nat := 4983230072969 + 3 ^ 40 * 393695 * 2
def baseEnd_393695 : Nat := 134769844181294933467957

theorem tailTrace_393695 : CollatzResearch.WordTrace tailWord_393695 prefixEnd_393695 134769844181294933467957 := by
  unfold tailWord_393695
  simp only [CollatzResearch.WordTrace]
  refine ⟨14359236308717727598038539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9572824205811818398692359 14359236308717727598038539)
  ·
    refine ⟨21538854463076591397057809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14359236308717727598038539 21538854463076591397057809)
    ·
      refine ⟨16154140847307443547793357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21538854463076591397057809 16154140847307443547793357)
      ·
        refine ⟨6057802817740291330422509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16154140847307443547793357 6057802817740291330422509)
        ·
          refine ⟨2271676056652609248908441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6057802817740291330422509 2271676056652609248908441)
          ·
            refine ⟨1703757042489456936681331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271676056652609248908441 1703757042489456936681331)
            ·
              refine ⟨2555635563734185405021997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703757042489456936681331 2555635563734185405021997)
              ·
                refine ⟨958363336400319526883249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2555635563734185405021997 958363336400319526883249)
                ·
                  refine ⟨718772502300239645162437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 958363336400319526883249 718772502300239645162437)
                  ·
                    refine ⟨134769844181294933467957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718772502300239645162437 134769844181294933467957)
                    ·
                      rfl

theorem cell22_393695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_393695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393695 prefixEnd_393695 := by exact prefixLift 393695
  have htrace : WordTrace (prefixWord ++ tailWord_393695) baseStart_393695 baseEnd_393695 := by
    simpa [prefixWord, tailWord_393695, baseEnd_393695] using wordTrace_append hprefix tailTrace_393695
  have hstable : (prefixWord ++ tailWord_393695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393695).length < 2 ^ (prefixWord ++ tailWord_393695).sum := by decide
  have hdescent : baseEnd_393695 < baseStart_393695 := by decide
  rcases family_descends (prefixWord ++ tailWord_393695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393742 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_393742 : Nat := 118140960795 + 393742 * 2 ^ 59
def prefixEnd_393742 : Nat := 4983230072969 + 3 ^ 40 * 393742 * 2
def baseEnd_393742 : Nat := 134785933241802477542813

theorem tailTrace_393742 : CollatzResearch.WordTrace tailWord_393742 prefixEnd_393742 134785933241802477542813 := by
  unfold tailWord_393742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1795118817443431828124935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9573967026364969749999653 1795118817443431828124935)
  ·
    refine ⟨2692678226165147742187403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1795118817443431828124935 2692678226165147742187403)
    ·
      refine ⟨4039017339247721613281105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692678226165147742187403 4039017339247721613281105)
      ·
        refine ⟨3029263004435791209960829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4039017339247721613281105 3029263004435791209960829)
        ·
          refine ⟨1135973626663421703735311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3029263004435791209960829 1135973626663421703735311)
          ·
            refine ⟨1703960439995132555602967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135973626663421703735311 1703960439995132555602967)
            ·
              refine ⟨2555940659992698833404451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703960439995132555602967 2555940659992698833404451)
              ·
                refine ⟨3833910989989048250106677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555940659992698833404451 3833910989989048250106677)
                ·
                  refine ⟨359429155311473273447501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3833910989989048250106677 359429155311473273447501)
                  ·
                    refine ⟨134785933241802477542813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 359429155311473273447501 134785933241802477542813)
                    ·
                      rfl

theorem cell22_393742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_393742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393742 prefixEnd_393742 := by exact prefixLift 393742
  have htrace : WordTrace (prefixWord ++ tailWord_393742) baseStart_393742 baseEnd_393742 := by
    simpa [prefixWord, tailWord_393742, baseEnd_393742] using wordTrace_append hprefix tailTrace_393742
  have hstable : (prefixWord ++ tailWord_393742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393742).length < 2 ^ (prefixWord ++ tailWord_393742).sum := by decide
  have hdescent : baseEnd_393742 < baseStart_393742 := by decide
  rcases family_descends (prefixWord ++ tailWord_393742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393789 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 5]
def baseStart_393789 : Nat := 118140960795 + 393789 * 2 ^ 59
def prefixEnd_393789 : Nat := 4983230072969 + 3 ^ 40 * 393789 * 2
def baseEnd_393789 : Nat := 44934007434103340539223

theorem tailTrace_393789 : CollatzResearch.WordTrace tailWord_393789 prefixEnd_393789 44934007434103340539223 := by
  unfold tailWord_393789
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362664770377181651960421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9575109846918121101306947 14362664770377181651960421)
  ·
    refine ⟨2692999644445721559742579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14362664770377181651960421 2692999644445721559742579)
    ·
      refine ⟨4039499466668582339613869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692999644445721559742579 4039499466668582339613869)
      ·
        refine ⟨1514812300000718377355201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4039499466668582339613869 1514812300000718377355201)
        ·
          refine ⟨1136109225000538783016401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514812300000718377355201 1136109225000538783016401)
          ·
            refine ⟨852081918750404087262301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136109225000538783016401 852081918750404087262301)
            ·
              refine ⟨319530719531401532723363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852081918750404087262301 319530719531401532723363)
              ·
                refine ⟨479296079297102299085045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319530719531401532723363 479296079297102299085045)
                ·
                  refine ⟨44934007434103340539223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479296079297102299085045 44934007434103340539223)
                  ·
                    rfl

theorem cell22_393789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_393789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393789 prefixEnd_393789 := by exact prefixLift 393789
  have htrace : WordTrace (prefixWord ++ tailWord_393789) baseStart_393789 baseEnd_393789 := by
    simpa [prefixWord, tailWord_393789, baseEnd_393789] using wordTrace_append hprefix tailTrace_393789
  have hstable : (prefixWord ++ tailWord_393789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393789).length < 2 ^ (prefixWord ++ tailWord_393789).sum := by decide
  have hdescent : baseEnd_393789 < baseStart_393789 := by decide
  rcases family_descends (prefixWord ++ tailWord_393789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393802 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_393802 : Nat := 118140960795 + 393802 * 2 ^ 59
def prefixEnd_393802 : Nat := 4983230072969 + 3 ^ 40 * 393802 * 2
def baseEnd_393802 : Nat := 134806472467982321042629

theorem tailTrace_393802 : CollatzResearch.WordTrace tailWord_393802 prefixEnd_393802 134806472467982321042629 := by
  unfold tailWord_393802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590784729832521218045915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9575425946220056581455773 3590784729832521218045915)
  ·
    refine ⟨5386177094748781827068873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3590784729832521218045915 5386177094748781827068873)
    ·
      refine ⟨4039632821061586370301655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5386177094748781827068873 4039632821061586370301655)
      ·
        refine ⟨6059449231592379555452483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039632821061586370301655 6059449231592379555452483)
        ·
          refine ⟨9089173847388569333178725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6059449231592379555452483 9089173847388569333178725)
          ·
            refine ⟨1704220096385356749971011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9089173847388569333178725 1704220096385356749971011)
            ·
              refine ⟨2556330144578035124956517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704220096385356749971011 2556330144578035124956517)
              ·
                refine ⟨479311902108381585929347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2556330144578035124956517 479311902108381585929347)
                ·
                  refine ⟨718967853162572378894021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479311902108381585929347 718967853162572378894021)
                  ·
                    refine ⟨134806472467982321042629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 718967853162572378894021 134806472467982321042629)
                    ·
                      rfl

theorem cell22_393802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_393802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393802 prefixEnd_393802 := by exact prefixLift 393802
  have htrace : WordTrace (prefixWord ++ tailWord_393802) baseStart_393802 baseEnd_393802 := by
    simpa [prefixWord, tailWord_393802, baseEnd_393802] using wordTrace_append hprefix tailTrace_393802
  have hstable : (prefixWord ++ tailWord_393802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393802).length < 2 ^ (prefixWord ++ tailWord_393802).sum := by decide
  have hdescent : baseEnd_393802 < baseStart_393802 := by decide
  rcases family_descends (prefixWord ++ tailWord_393802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393815 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_393815 : Nat := 118140960795 + 393815 * 2 ^ 59
def prefixEnd_393815 : Nat := 4983230072969 + 3 ^ 40 * 393815 * 2
def baseEnd_393815 : Nat := 134810922633654620467589

theorem tailTrace_393815 : CollatzResearch.WordTrace tailWord_393815 prefixEnd_393815 134810922633654620467589 := by
  unfold tailWord_393815
  simp only [CollatzResearch.WordTrace]
  refine ⟨14363613068282988092406899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9575742045521992061604599 14363613068282988092406899)
  ·
    refine ⟨21545419602424482138610349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14363613068282988092406899 21545419602424482138610349)
    ·
      refine ⟨8079532350909180801978881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21545419602424482138610349 8079532350909180801978881)
      ·
        refine ⟨6059649263181885601484161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8079532350909180801978881 6059649263181885601484161)
        ·
          refine ⟨4544736947386414201113121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6059649263181885601484161 4544736947386414201113121)
          ·
            refine ⟨3408552710539810650834841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544736947386414201113121 3408552710539810650834841)
            ·
              refine ⟨2556414532904857988126131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408552710539810650834841 2556414532904857988126131)
              ·
                refine ⟨3834621799357286982189197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556414532904857988126131 3834621799357286982189197)
                ·
                  refine ⟨1437983174758982618320949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3834621799357286982189197 1437983174758982618320949)
                  ·
                    refine ⟨134810922633654620467589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1437983174758982618320949 134810922633654620467589)
                    ·
                      rfl

theorem cell22_393815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_393815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393815 prefixEnd_393815 := by exact prefixLift 393815
  have htrace : WordTrace (prefixWord ++ tailWord_393815) baseStart_393815 baseEnd_393815 := by
    simpa [prefixWord, tailWord_393815, baseEnd_393815] using wordTrace_append hprefix tailTrace_393815
  have hstable : (prefixWord ++ tailWord_393815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393815).length < 2 ^ (prefixWord ++ tailWord_393815).sum := by decide
  have hdescent : baseEnd_393815 < baseStart_393815 := by decide
  rcases family_descends (prefixWord ++ tailWord_393815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393849 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_393849 : Nat := 118140960795 + 393849 * 2 ^ 59
def prefixEnd_393849 : Nat := 4983230072969 + 3 ^ 40 * 393849 * 2
def baseEnd_393849 : Nat := 134822561528489865117485

theorem tailTrace_393849 : CollatzResearch.WordTrace tailWord_393849 prefixEnd_393849 134822561528489865117485 := by
  unfold tailWord_393849
  simp only [CollatzResearch.WordTrace]
  refine ⟨14364853150159811899144601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9576568766773207932763067 14364853150159811899144601)
  ·
    refine ⟨10773639862619858924358451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14364853150159811899144601 10773639862619858924358451)
    ·
      refine ⟨16160459793929788386537677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773639862619858924358451 16160459793929788386537677)
      ·
        refine ⟨6060172422723670644951629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16160459793929788386537677 6060172422723670644951629)
        ·
          refine ⟨2272564658521376491856861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6060172422723670644951629 2272564658521376491856861)
          ·
            refine ⟨852211746945516184446323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2272564658521376491856861 852211746945516184446323)
            ·
              refine ⟨1278317620418274276669485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852211746945516184446323 1278317620418274276669485)
              ·
                refine ⟨479369107656852853751057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278317620418274276669485 479369107656852853751057)
                ·
                  refine ⟨359526830742639640313293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479369107656852853751057 359526830742639640313293)
                  ·
                    refine ⟨134822561528489865117485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 359526830742639640313293 134822561528489865117485)
                    ·
                      rfl

theorem cell22_393849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_393849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393849 prefixEnd_393849 := by exact prefixLift 393849
  have htrace : WordTrace (prefixWord ++ tailWord_393849) baseStart_393849 baseEnd_393849 := by
    simpa [prefixWord, tailWord_393849, baseEnd_393849] using wordTrace_append hprefix tailTrace_393849
  have hstable : (prefixWord ++ tailWord_393849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393849).length < 2 ^ (prefixWord ++ tailWord_393849).sum := by decide
  have hdescent : baseEnd_393849 < baseStart_393849 := by decide
  rcases family_descends (prefixWord ++ tailWord_393849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393907 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 5]
def baseStart_393907 : Nat := 118140960795 + 393907 * 2 ^ 59
def prefixEnd_393907 : Nat := 4983230072969 + 3 ^ 40 * 393907 * 2
def baseEnd_393907 : Nat := 44947472037932349055769

theorem tailTrace_393907 : CollatzResearch.WordTrace tailWord_393907 prefixEnd_393907 44947472037932349055769 := by
  unfold tailWord_393907
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366968583949687804755975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9577979055966458536503983 14366968583949687804755975)
  ·
    refine ⟨21550452875924531707133963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14366968583949687804755975 21550452875924531707133963)
    ·
      refine ⟨32325679313886797560700945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21550452875924531707133963 32325679313886797560700945)
      ·
        refine ⟨24244259485415098170525709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32325679313886797560700945 24244259485415098170525709)
        ·
          refine ⟨9091597307030661813947141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24244259485415098170525709 9091597307030661813947141)
          ·
            refine ⟨1704674495068249090115089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9091597307030661813947141 1704674495068249090115089)
            ·
              refine ⟨1278505871301186817586317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704674495068249090115089 1278505871301186817586317)
              ·
                refine ⟨479439701737945056594869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278505871301186817586317 479439701737945056594869)
                ·
                  refine ⟨44947472037932349055769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479439701737945056594869 44947472037932349055769)
                  ·
                    rfl

theorem cell22_393907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 5].length) (baseStart_393907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_393907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_393907 prefixEnd_393907 := by exact prefixLift 393907
  have htrace : WordTrace (prefixWord ++ tailWord_393907) baseStart_393907 baseEnd_393907 := by
    simpa [prefixWord, tailWord_393907, baseEnd_393907] using wordTrace_append hprefix tailTrace_393907
  have hstable : (prefixWord ++ tailWord_393907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393907).length < 2 ^ (prefixWord ++ tailWord_393907).sum := by decide
  have hdescent : baseEnd_393907 < baseStart_393907 := by decide
  rcases family_descends (prefixWord ++ tailWord_393907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394018 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_394018 : Nat := 118140960795 + 394018 * 2 ^ 59
def prefixEnd_394018 : Nat := 4983230072969 + 3 ^ 40 * 394018 * 2
def baseEnd_394018 : Nat := 134880413682229757641967

theorem tailTrace_394018 : CollatzResearch.WordTrace tailWord_394018 prefixEnd_394018 134880413682229757641967 := by
  unfold tailWord_394018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592754271636888440511677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9580678057698369174697805 3592754271636888440511677)
  ·
    refine ⟨1347282851863833165191879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3592754271636888440511677 1347282851863833165191879)
    ·
      refine ⟨2020924277795749747787819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347282851863833165191879 2020924277795749747787819)
      ·
        refine ⟨3031386416693624621681729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020924277795749747787819 3031386416693624621681729)
        ·
          refine ⟨2273539812520218466261297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031386416693624621681729 2273539812520218466261297)
          ·
            refine ⟨1705154859390163849695973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273539812520218466261297 1705154859390163849695973)
            ·
              refine ⟨319716536135655721817995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1705154859390163849695973 319716536135655721817995)
              ·
                refine ⟨479574804203483582726993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319716536135655721817995 479574804203483582726993)
                ·
                  refine ⟨359681103152612687045245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479574804203483582726993 359681103152612687045245)
                  ·
                    refine ⟨134880413682229757641967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 359681103152612687045245 134880413682229757641967)
                    ·
                      rfl

theorem cell22_394018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_394018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394018 prefixEnd_394018 := by exact prefixLift 394018
  have htrace : WordTrace (prefixWord ++ tailWord_394018) baseStart_394018 baseEnd_394018 := by
    simpa [prefixWord, tailWord_394018, baseEnd_394018] using wordTrace_append hprefix tailTrace_394018
  have hstable : (prefixWord ++ tailWord_394018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394018).length < 2 ^ (prefixWord ++ tailWord_394018).sum := by decide
  have hdescent : baseEnd_394018 < baseStart_394018 := by decide
  rcases family_descends (prefixWord ++ tailWord_394018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394054 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_394054 : Nat := 118140960795 + 394054 * 2 ^ 59
def prefixEnd_394054 : Nat := 4983230072969 + 3 ^ 40 * 394054 * 2
def baseEnd_394054 : Nat := 44964245739312554580619

theorem tailTrace_394054 : CollatzResearch.WordTrace tailWord_394054 prefixEnd_394054 44964245739312554580619 := by
  unfold tailWord_394054
  simp only [CollatzResearch.WordTrace]
  refine ⟨449135316075535372198663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9581553409611421273571477 449135316075535372198663)
  ·
    refine ⟨673702974113303058297995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449135316075535372198663 673702974113303058297995)
    ·
      refine ⟨1010554461169954587446993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673702974113303058297995 1010554461169954587446993)
      ·
        refine ⟨757915845877465940585245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1010554461169954587446993 757915845877465940585245)
        ·
          refine ⟨284218442204049727719467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 757915845877465940585245 284218442204049727719467)
          ·
            refine ⟨426327663306074591579201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284218442204049727719467 426327663306074591579201)
            ·
              refine ⟨319745747479555943684401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426327663306074591579201 319745747479555943684401)
              ·
                refine ⟨239809310609666957763301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319745747479555943684401 239809310609666957763301)
                ·
                  refine ⟨44964245739312554580619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239809310609666957763301 44964245739312554580619)
                  ·
                    rfl

theorem cell22_394054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_394054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394054 prefixEnd_394054 := by exact prefixLift 394054
  have htrace : WordTrace (prefixWord ++ tailWord_394054) baseStart_394054 baseEnd_394054 := by
    simpa [prefixWord, tailWord_394054, baseEnd_394054] using wordTrace_append hprefix tailTrace_394054
  have hstable : (prefixWord ++ tailWord_394054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394054).length < 2 ^ (prefixWord ++ tailWord_394054).sum := by decide
  have hdescent : baseEnd_394054 < baseStart_394054 := by decide
  rcases family_descends (prefixWord ++ tailWord_394054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394074 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_394074 : Nat := 118140960795 + 394074 * 2 ^ 59
def prefixEnd_394074 : Nat := 4983230072969 + 3 ^ 40 * 394074 * 2
def baseEnd_394074 : Nat := 134899583626664278241795

theorem tailTrace_394074 : CollatzResearch.WordTrace tailWord_394074 prefixEnd_394074 134899583626664278241795 := by
  unfold tailWord_394074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593264893586168831521319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9582039716229783550723517 3593264893586168831521319)
  ·
    refine ⟨5389897340379253247281979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593264893586168831521319 5389897340379253247281979)
    ·
      refine ⟨8084846010568879870922969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389897340379253247281979 8084846010568879870922969)
      ·
        refine ⟨6063634507926659903192227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8084846010568879870922969 6063634507926659903192227)
        ·
          refine ⟨9095451761889989854788341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6063634507926659903192227 9095451761889989854788341)
          ·
            refine ⟨852698602677186548886407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9095451761889989854788341 852698602677186548886407)
            ·
              refine ⟨1279047904015779823329611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852698602677186548886407 1279047904015779823329611)
              ·
                refine ⟨1918571856023669734994417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279047904015779823329611 1918571856023669734994417)
                ·
                  refine ⟨1438928892017752301245813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918571856023669734994417 1438928892017752301245813)
                  ·
                    refine ⟨134899583626664278241795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1438928892017752301245813 134899583626664278241795)
                    ·
                      rfl

theorem cell22_394074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_394074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394074 prefixEnd_394074 := by exact prefixLift 394074
  have htrace : WordTrace (prefixWord ++ tailWord_394074) baseStart_394074 baseEnd_394074 := by
    simpa [prefixWord, tailWord_394074, baseEnd_394074] using wordTrace_append hprefix tailTrace_394074
  have hstable : (prefixWord ++ tailWord_394074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394074).length < 2 ^ (prefixWord ++ tailWord_394074).sum := by decide
  have hdescent : baseEnd_394074 < baseStart_394074 := by decide
  rcases family_descends (prefixWord ++ tailWord_394074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394076 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_394076 : Nat := 118140960795 + 394076 * 2 ^ 59
def prefixEnd_394076 : Nat := 4983230072969 + 3 ^ 40 * 394076 * 2
def baseEnd_394076 : Nat := 44966756089178979897263

theorem tailTrace_394076 : CollatzResearch.WordTrace tailWord_394076 prefixEnd_394076 44966756089178979897263 := by
  unfold tailWord_394076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186566260168714833829041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9582088346891619778438721 7186566260168714833829041)
  ·
    refine ⟨5389924695126536125371781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7186566260168714833829041 5389924695126536125371781)
    ·
      refine ⟨1010610880336225523507209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5389924695126536125371781 1010610880336225523507209)
      ·
        refine ⟨757958160252169142630407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1010610880336225523507209 757958160252169142630407)
        ·
          refine ⟨1136937240378253713945611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757958160252169142630407 1136937240378253713945611)
          ·
            refine ⟨1705405860567380570918417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136937240378253713945611 1705405860567380570918417)
            ·
              refine ⟨1279054395425535428188813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705405860567380570918417 1279054395425535428188813)
              ·
                refine ⟨479645398284575785570805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1279054395425535428188813 479645398284575785570805)
                ·
                  refine ⟨44966756089178979897263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479645398284575785570805 44966756089178979897263)
                  ·
                    rfl

theorem cell22_394076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_394076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394076 prefixEnd_394076 := by exact prefixLift 394076
  have htrace : WordTrace (prefixWord ++ tailWord_394076) baseStart_394076 baseEnd_394076 := by
    simpa [prefixWord, tailWord_394076, baseEnd_394076] using wordTrace_append hprefix tailTrace_394076
  have hstable : (prefixWord ++ tailWord_394076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394076).length < 2 ^ (prefixWord ++ tailWord_394076).sum := by decide
  have hdescent : baseEnd_394076 < baseStart_394076 := by decide
  rcases family_descends (prefixWord ++ tailWord_394076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394110 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_394110 : Nat := 118140960795 + 394110 * 2 ^ 59
def prefixEnd_394110 : Nat := 4983230072969 + 3 ^ 40 * 394110 * 2
def baseEnd_394110 : Nat := 44970635720790728113895

theorem tailTrace_394110 : CollatzResearch.WordTrace tailWord_394110 prefixEnd_394110 44970635720790728113895 := by
  unfold tailWord_394110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796796575276781684299473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9582915068142835649597189 1796796575276781684299473)
  ·
    refine ⟨1347597431457586263224605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1796796575276781684299473 1347597431457586263224605)
    ·
      refine ⟨505349036796594848709227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1347597431457586263224605 505349036796594848709227)
      ·
        refine ⟨758023555194892273063841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505349036796594848709227 758023555194892273063841)
        ·
          refine ⟨568517666396169204797881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758023555194892273063841 568517666396169204797881)
          ·
            refine ⟨426388249797126903598411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568517666396169204797881 426388249797126903598411)
            ·
              refine ⟨639582374695690355397617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426388249797126903598411 639582374695690355397617)
              ·
                refine ⟨479686781021767766548213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639582374695690355397617 479686781021767766548213)
                ·
                  refine ⟨44970635720790728113895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479686781021767766548213 44970635720790728113895)
                  ·
                    rfl

theorem cell22_394110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_394110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394110 prefixEnd_394110 := by exact prefixLift 394110
  have htrace : WordTrace (prefixWord ++ tailWord_394110) baseStart_394110 baseEnd_394110 := by
    simpa [prefixWord, tailWord_394110, baseEnd_394110] using wordTrace_append hprefix tailTrace_394110
  have hstable : (prefixWord ++ tailWord_394110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394110).length < 2 ^ (prefixWord ++ tailWord_394110).sum := by decide
  have hdescent : baseEnd_394110 < baseStart_394110 := by decide
  rcases family_descends (prefixWord ++ tailWord_394110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394121 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 4]
def baseStart_394121 : Nat := 118140960795 + 394121 * 2 ^ 59
def prefixEnd_394121 : Nat := 4983230072969 + 3 ^ 40 * 394121 * 2
def baseEnd_394121 : Nat := 44971890895723940772217

theorem tailTrace_394121 : CollatzResearch.WordTrace tailWord_394121 prefixEnd_394121 44971890895723940772217 := by
  unfold tailWord_394121
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374773805174402353046217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9583182536782934902030811 14374773805174402353046217)
  ·
    refine ⟨10781080353880801764784663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14374773805174402353046217 10781080353880801764784663)
    ·
      refine ⟨16171620530821202647176995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781080353880801764784663 16171620530821202647176995)
      ·
        refine ⟨24257430796231803970765493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16171620530821202647176995 24257430796231803970765493)
        ·
          refine ⟨2274134137146731622259265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24257430796231803970765493 2274134137146731622259265)
          ·
            refine ⟨1705600602860048716694449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274134137146731622259265 1705600602860048716694449)
            ·
              refine ⟨1279200452145036537520837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705600602860048716694449 1279200452145036537520837)
              ·
                refine ⟨239850084777194350785157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1279200452145036537520837 239850084777194350785157)
                ·
                  refine ⟨44971890895723940772217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239850084777194350785157 44971890895723940772217)
                  ·
                    rfl

theorem cell22_394121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_394121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394121 prefixEnd_394121 := by exact prefixLift 394121
  have htrace : WordTrace (prefixWord ++ tailWord_394121) baseStart_394121 baseEnd_394121 := by
    simpa [prefixWord, tailWord_394121, baseEnd_394121] using wordTrace_append hprefix tailTrace_394121
  have hstable : (prefixWord ++ tailWord_394121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394121).length < 2 ^ (prefixWord ++ tailWord_394121).sum := by decide
  have hdescent : baseEnd_394121 < baseStart_394121 := by decide
  rcases family_descends (prefixWord ++ tailWord_394121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394209 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_394209 : Nat := 118140960795 + 394209 * 2 ^ 59
def prefixEnd_394209 : Nat := 4983230072969 + 3 ^ 40 * 394209 * 2
def baseEnd_394209 : Nat := 134945796885568926116381

theorem tailTrace_394209 : CollatzResearch.WordTrace tailWord_394209 prefixEnd_394209 134945796885568926116381 := by
  unfold tailWord_394209
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377983428855593382249681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9585322285903728921499787 14377983428855593382249681)
  ·
    refine ⟨10783487571641695036687261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14377983428855593382249681 10783487571641695036687261)
    ·
      refine ⟨4043807839365635638757723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10783487571641695036687261 4043807839365635638757723)
      ·
        refine ⟨6065711759048453458136585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043807839365635638757723 6065711759048453458136585)
        ·
          refine ⟨4549283819286340093602439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065711759048453458136585 4549283819286340093602439)
          ·
            refine ⟨6823925728929510140403659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549283819286340093602439 6823925728929510140403659)
            ·
              refine ⟨10235888593394265210605489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823925728929510140403659 10235888593394265210605489)
              ·
                refine ⟨7676916445045698907954117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10235888593394265210605489 7676916445045698907954117)
                ·
                  refine ⟨1439421833446068545241397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7676916445045698907954117 1439421833446068545241397)
                  ·
                    refine ⟨134945796885568926116381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1439421833446068545241397 134945796885568926116381)
                    ·
                      rfl

theorem cell22_394209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_394209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394209 prefixEnd_394209 := by exact prefixLift 394209
  have htrace : WordTrace (prefixWord ++ tailWord_394209) baseStart_394209 baseEnd_394209 := by
    simpa [prefixWord, tailWord_394209, baseEnd_394209] using wordTrace_append hprefix tailTrace_394209
  have hstable : (prefixWord ++ tailWord_394209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394209).length < 2 ^ (prefixWord ++ tailWord_394209).sum := by decide
  have hdescent : baseEnd_394209 < baseStart_394209 := by decide
  rcases family_descends (prefixWord ++ tailWord_394209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394241 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_394241 : Nat := 118140960795 + 394241 * 2 ^ 59
def prefixEnd_394241 : Nat := 4983230072969 + 3 ^ 40 * 394241 * 2
def baseEnd_394241 : Nat := 134956751139531509316283

theorem tailTrace_394241 : CollatzResearch.WordTrace tailWord_394241 prefixEnd_394241 134956751139531509316283 := by
  unfold tailWord_394241
  simp only [CollatzResearch.WordTrace]
  refine ⟨14379150564739662847414577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9586100376493108564943051 14379150564739662847414577)
  ·
    refine ⟨10784362923554747135560933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14379150564739662847414577 10784362923554747135560933)
    ·
      refine ⟨2022068048166515087917675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10784362923554747135560933 2022068048166515087917675)
      ·
        refine ⟨3033102072249772631876513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022068048166515087917675 3033102072249772631876513)
        ·
          refine ⟨2274826554187329473907385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3033102072249772631876513 2274826554187329473907385)
          ·
            refine ⟨1706119915640497105430539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274826554187329473907385 1706119915640497105430539)
            ·
              refine ⟨2559179873460745658145809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706119915640497105430539 2559179873460745658145809)
              ·
                refine ⟨1919384905095559243609357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559179873460745658145809 1919384905095559243609357)
                ·
                  refine ⟨719769339410834716353509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1919384905095559243609357 719769339410834716353509)
                  ·
                    refine ⟨134956751139531509316283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 719769339410834716353509 134956751139531509316283)
                    ·
                      rfl

theorem cell22_394241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_394241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394241 prefixEnd_394241 := by exact prefixLift 394241
  have htrace : WordTrace (prefixWord ++ tailWord_394241) baseStart_394241 baseEnd_394241 := by
    simpa [prefixWord, tailWord_394241, baseEnd_394241] using wordTrace_append hprefix tailTrace_394241
  have hstable : (prefixWord ++ tailWord_394241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394241).length < 2 ^ (prefixWord ++ tailWord_394241).sum := by decide
  have hdescent : baseEnd_394241 < baseStart_394241 := by decide
  rcases family_descends (prefixWord ++ tailWord_394241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394271 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 1, 5]
def baseStart_394271 : Nat := 118140960795 + 394271 * 2 ^ 59
def prefixEnd_394271 : Nat := 4983230072969 + 3 ^ 40 * 394271 * 2
def baseEnd_394271 : Nat := 134967020752621431066191

theorem tailTrace_394271 : CollatzResearch.WordTrace tailWord_394271 prefixEnd_394271 134967020752621431066191 := by
  unfold tailWord_394271
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380244754630977971006667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9586829836420651980671111 14380244754630977971006667)
  ·
    refine ⟨21570367131946466956510001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14380244754630977971006667 21570367131946466956510001)
    ·
      refine ⟨16177775348959850217382501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21570367131946466956510001 16177775348959850217382501)
      ·
        refine ⟨3033332877929971915759219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16177775348959850217382501 3033332877929971915759219)
        ·
          refine ⟨4549999316894957873638829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033332877929971915759219 4549999316894957873638829)
          ·
            refine ⟨1706249743835609202614561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4549999316894957873638829 1706249743835609202614561)
            ·
              refine ⟨1279687307876706901960921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706249743835609202614561 1279687307876706901960921)
              ·
                refine ⟨959765480907530176470691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279687307876706901960921 959765480907530176470691)
                ·
                  refine ⟨1439648221361295264706037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959765480907530176470691 1439648221361295264706037)
                  ·
                    refine ⟨134967020752621431066191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1439648221361295264706037 134967020752621431066191)
                    ·
                      rfl

theorem cell22_394271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_394271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394271 prefixEnd_394271 := by exact prefixLift 394271
  have htrace : WordTrace (prefixWord ++ tailWord_394271) baseStart_394271 baseEnd_394271 := by
    simpa [prefixWord, tailWord_394271, baseEnd_394271] using wordTrace_append hprefix tailTrace_394271
  have hstable : (prefixWord ++ tailWord_394271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394271).length < 2 ^ (prefixWord ++ tailWord_394271).sum := by decide
  have hdescent : baseEnd_394271 < baseStart_394271 := by decide
  rcases family_descends (prefixWord ++ tailWord_394271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394273 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 4]
def baseStart_394273 : Nat := 118140960795 + 394273 * 2 ^ 59
def prefixEnd_394273 : Nat := 4983230072969 + 3 ^ 40 * 394273 * 2
def baseEnd_394273 : Nat := 44989235131164697505395

theorem tailTrace_394273 : CollatzResearch.WordTrace tailWord_394273 prefixEnd_394273 44989235131164697505395 := by
  unfold tailWord_394273
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380317700623732312579473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9586878467082488208386315 14380317700623732312579473)
  ·
    refine ⟨10785238275467799234434605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14380317700623732312579473 10785238275467799234434605)
    ·
      refine ⟨4044464353300424712912977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10785238275467799234434605 4044464353300424712912977)
      ·
        refine ⟨3033348264975318534684733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4044464353300424712912977 3033348264975318534684733)
        ·
          refine ⟨1137505599365744450506775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3033348264975318534684733 1137505599365744450506775)
          ·
            refine ⟨1706258399048616675760163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137505599365744450506775 1706258399048616675760163)
            ·
              refine ⟨2559387598572925013640245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706258399048616675760163 2559387598572925013640245)
              ·
                refine ⟨239942587366211720028773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2559387598572925013640245 239942587366211720028773)
                ·
                  refine ⟨44989235131164697505395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239942587366211720028773 44989235131164697505395)
                  ·
                    rfl

theorem cell22_394273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_394273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394273 prefixEnd_394273 := by exact prefixLift 394273
  have htrace : WordTrace (prefixWord ++ tailWord_394273) baseStart_394273 baseEnd_394273 := by
    simpa [prefixWord, tailWord_394273, baseEnd_394273] using wordTrace_append hprefix tailTrace_394273
  have hstable : (prefixWord ++ tailWord_394273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394273).length < 2 ^ (prefixWord ++ tailWord_394273).sum := by decide
  have hdescent : baseEnd_394273 < baseStart_394273 := by decide
  rcases family_descends (prefixWord ++ tailWord_394273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394275 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 1, 4]
def baseStart_394275 : Nat := 118140960795 + 394275 * 2 ^ 59
def prefixEnd_394275 : Nat := 4983230072969 + 3 ^ 40 * 394275 * 2
def baseEnd_394275 : Nat := 134968390034366753966179

theorem tailTrace_394275 : CollatzResearch.WordTrace tailWord_394275 prefixEnd_394275 134968390034366753966179 := by
  unfold tailWord_394275
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380390646616486654152279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9586927097744324436101519 14380390646616486654152279)
  ·
    refine ⟨21570585969924729981228419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14380390646616486654152279 21570585969924729981228419)
    ·
      refine ⟨32355878954887094971842629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21570585969924729981228419 32355878954887094971842629)
      ·
        refine ⟨6066727304041330307220493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32355878954887094971842629 6066727304041330307220493)
        ·
          refine ⟨2275022739015498865207685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6066727304041330307220493 2275022739015498865207685)
          ·
            refine ⟨426566763565406037226441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2275022739015498865207685 426566763565406037226441)
            ·
              refine ⟨319925072674054527919831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426566763565406037226441 319925072674054527919831)
              ·
                refine ⟨479887609011081791879747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319925072674054527919831 479887609011081791879747)
                ·
                  refine ⟨719831413516622687819621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479887609011081791879747 719831413516622687819621)
                  ·
                    refine ⟨134968390034366753966179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 719831413516622687819621 134968390034366753966179)
                    ·
                      rfl

theorem cell22_394275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 4].length) (baseStart_394275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394275 prefixEnd_394275 := by exact prefixLift 394275
  have htrace : WordTrace (prefixWord ++ tailWord_394275) baseStart_394275 baseEnd_394275 := by
    simpa [prefixWord, tailWord_394275, baseEnd_394275] using wordTrace_append hprefix tailTrace_394275
  have hstable : (prefixWord ++ tailWord_394275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394275).length < 2 ^ (prefixWord ++ tailWord_394275).sum := by decide
  have hdescent : baseEnd_394275 < baseStart_394275 := by decide
  rcases family_descends (prefixWord ++ tailWord_394275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394284 : List Nat := [2, 2, 1, 1, 1, 2, 13]
def baseStart_394284 : Nat := 118140960795 + 394284 * 2 ^ 59
def prefixEnd_394284 : Nat := 4983230072969 + 3 ^ 40 * 394284 * 2
def baseEnd_394284 : Nat := 4998943367344212240413

theorem tailTrace_394284 : CollatzResearch.WordTrace tailWord_394284 prefixEnd_394284 4998943367344212240413 := by
  unfold tailWord_394284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190359451791940595614953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9587145935722587460819937 7190359451791940595614953)
  ·
    refine ⟨5392769588843955446711215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7190359451791940595614953 5392769588843955446711215)
    ·
      refine ⟨8089154383265933170066823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5392769588843955446711215 8089154383265933170066823)
      ·
        refine ⟨12133731574898899755100235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8089154383265933170066823 12133731574898899755100235)
        ·
          refine ⟨18200597362348349632650353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133731574898899755100235 18200597362348349632650353)
          ·
            refine ⟨13650448021761262224487765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18200597362348349632650353 13650448021761262224487765)
            ·
              refine ⟨4998943367344212240413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 13650448021761262224487765 4998943367344212240413)
              ·
                rfl

theorem cell22_394284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 13].length) (baseStart_394284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394284 prefixEnd_394284 := by exact prefixLift 394284
  have htrace : WordTrace (prefixWord ++ tailWord_394284) baseStart_394284 baseEnd_394284 := by
    simpa [prefixWord, tailWord_394284, baseEnd_394284] using wordTrace_append hprefix tailTrace_394284
  have hstable : (prefixWord ++ tailWord_394284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394284).length < 2 ^ (prefixWord ++ tailWord_394284).sum := by decide
  have hdescent : baseEnd_394284 < baseStart_394284 := by decide
  rcases family_descends (prefixWord ++ tailWord_394284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394299 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_394299 : Nat := 118140960795 + 394299 * 2 ^ 59
def prefixEnd_394299 : Nat := 4983230072969 + 3 ^ 40 * 394299 * 2
def baseEnd_394299 : Nat := 134976605724838691366105

theorem tailTrace_394299 : CollatzResearch.WordTrace tailWord_394299 prefixEnd_394299 134976605724838691366105 := by
  unfold tailWord_394299
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381265998529538753025951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9587510665686359168683967 14381265998529538753025951)
  ·
    refine ⟨21571898997794308129538927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14381265998529538753025951 21571898997794308129538927)
    ·
      refine ⟨32357848496691462194308391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21571898997794308129538927 32357848496691462194308391)
      ·
        refine ⟨48536772745037193291462587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32357848496691462194308391 48536772745037193291462587)
        ·
          refine ⟨72805159117555789937193881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48536772745037193291462587 72805159117555789937193881)
          ·
            refine ⟨54603869338166842452895411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72805159117555789937193881 54603869338166842452895411)
            ·
              refine ⟨81905804007250263679343117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54603869338166842452895411 81905804007250263679343117)
              ·
                refine ⟨30714676502718848879753669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81905804007250263679343117 30714676502718848879753669)
                ·
                  refine ⟨5759001844259784164953813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30714676502718848879753669 5759001844259784164953813)
                  ·
                    refine ⟨134976605724838691366105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5759001844259784164953813 134976605724838691366105)
                    ·
                      rfl

theorem cell22_394299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_394299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394299 prefixEnd_394299 := by exact prefixLift 394299
  have htrace : WordTrace (prefixWord ++ tailWord_394299) baseStart_394299 baseEnd_394299 := by
    simpa [prefixWord, tailWord_394299, baseEnd_394299] using wordTrace_append hprefix tailTrace_394299
  have hstable : (prefixWord ++ tailWord_394299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394299).length < 2 ^ (prefixWord ++ tailWord_394299).sum := by decide
  have hdescent : baseEnd_394299 < baseStart_394299 := by decide
  rcases family_descends (prefixWord ++ tailWord_394299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394305 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_394305 : Nat := 118140960795 + 394305 * 2 ^ 59
def prefixEnd_394305 : Nat := 4983230072969 + 3 ^ 40 * 394305 * 2
def baseEnd_394305 : Nat := 134978659647456675716087

theorem tailTrace_394305 : CollatzResearch.WordTrace tailWord_394305 prefixEnd_394305 134978659647456675716087 := by
  unfold tailWord_394305
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381484836507801777744369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9587656557671867851829579 14381484836507801777744369)
  ·
    refine ⟨10786113627380851333308277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14381484836507801777744369 10786113627380851333308277)
    ·
      refine ⟨1011198152566954812497651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10786113627380851333308277 1011198152566954812497651)
      ·
        refine ⟨1516797228850432218746477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011198152566954812497651 1516797228850432218746477)
        ·
          refine ⟨568798960818912082029929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1516797228850432218746477 568798960818912082029929)
          ·
            refine ⟨426599220614184061522447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568798960818912082029929 426599220614184061522447)
            ·
              refine ⟨639898830921276092283671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426599220614184061522447 639898830921276092283671)
              ·
                refine ⟨959848246381914138425507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639898830921276092283671 959848246381914138425507)
                ·
                  refine ⟨1439772369572871207638261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959848246381914138425507 1439772369572871207638261)
                  ·
                    refine ⟨134978659647456675716087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1439772369572871207638261 134978659647456675716087)
                    ·
                      rfl

theorem cell22_394305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_394305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394305 prefixEnd_394305 := by exact prefixLift 394305
  have htrace : WordTrace (prefixWord ++ tailWord_394305) baseStart_394305 baseEnd_394305 := by
    simpa [prefixWord, tailWord_394305, baseEnd_394305] using wordTrace_append hprefix tailTrace_394305
  have hstable : (prefixWord ++ tailWord_394305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394305).length < 2 ^ (prefixWord ++ tailWord_394305).sum := by decide
  have hdescent : baseEnd_394305 < baseStart_394305 := by decide
  rcases family_descends (prefixWord ++ tailWord_394305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394350 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_394350 : Nat := 118140960795 + 394350 * 2 ^ 59
def prefixEnd_394350 : Nat := 4983230072969 + 3 ^ 40 * 394350 * 2
def baseEnd_394350 : Nat := 134994064067091558340949

theorem tailTrace_394350 : CollatzResearch.WordTrace tailWord_394350 prefixEnd_394350 134994064067091558340949 := by
  unfold tailWord_394350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797890765168096807891563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9588750747563182975421669 1797890765168096807891563)
  ·
    refine ⟨2696836147752145211837345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797890765168096807891563 2696836147752145211837345)
    ·
      refine ⟨2022627110814108908878009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2696836147752145211837345 2022627110814108908878009)
      ·
        refine ⟨1516970333110581681658507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2022627110814108908878009 1516970333110581681658507)
        ·
          refine ⟨2275455499665872522487761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516970333110581681658507 2275455499665872522487761)
          ·
            refine ⟨1706591624749404391865821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2275455499665872522487761 1706591624749404391865821)
            ·
              refine ⟨639971859281026646949683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1706591624749404391865821 639971859281026646949683)
              ·
                refine ⟨959957788921539970424525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639971859281026646949683 959957788921539970424525)
                ·
                  refine ⟨359984170845577488909197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959957788921539970424525 359984170845577488909197)
                  ·
                    refine ⟨134994064067091558340949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 359984170845577488909197 134994064067091558340949)
                    ·
                      rfl

theorem cell22_394350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_394350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394350 prefixEnd_394350 := by exact prefixLift 394350
  have htrace : WordTrace (prefixWord ++ tailWord_394350) baseStart_394350 baseEnd_394350 := by
    simpa [prefixWord, tailWord_394350, baseEnd_394350] using wordTrace_append hprefix tailTrace_394350
  have hstable : (prefixWord ++ tailWord_394350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394350).length < 2 ^ (prefixWord ++ tailWord_394350).sum := by decide
  have hdescent : baseEnd_394350 < baseStart_394350 := by decide
  rcases family_descends (prefixWord ++ tailWord_394350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394410 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_394410 : Nat := 118140960795 + 394410 * 2 ^ 59
def prefixEnd_394410 : Nat := 4983230072969 + 3 ^ 40 * 394410 * 2
def baseEnd_394410 : Nat := 135014603293271401840765

theorem tailTrace_394410 : CollatzResearch.WordTrace tailWord_394410 prefixEnd_394410 135014603293271401840765 := by
  unfold tailWord_394410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596328625281851177579171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9590209667418269806877789 3596328625281851177579171)
  ·
    refine ⟨5394492937922776766368757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3596328625281851177579171 5394492937922776766368757)
    ·
      refine ⟨505733712930260321847071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5394492937922776766368757 505733712930260321847071)
      ·
        refine ⟨758600569395390482770607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505733712930260321847071 758600569395390482770607)
        ·
          refine ⟨1137900854093085724155911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758600569395390482770607 1137900854093085724155911)
          ·
            refine ⟨1706851281139628586233867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137900854093085724155911 1706851281139628586233867)
            ·
              refine ⟨2560276921709442879350801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706851281139628586233867 2560276921709442879350801)
              ·
                refine ⟨1920207691282082159513101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560276921709442879350801 1920207691282082159513101)
                ·
                  refine ⟨720077884230780809817413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1920207691282082159513101 720077884230780809817413)
                  ·
                    refine ⟨135014603293271401840765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720077884230780809817413 135014603293271401840765)
                    ·
                      rfl

theorem cell22_394410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_394410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394410 prefixEnd_394410 := by exact prefixLift 394410
  have htrace : WordTrace (prefixWord ++ tailWord_394410) baseStart_394410 baseEnd_394410 := by
    simpa [prefixWord, tailWord_394410, baseEnd_394410] using wordTrace_append hprefix tailTrace_394410
  have hstable : (prefixWord ++ tailWord_394410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394410).length < 2 ^ (prefixWord ++ tailWord_394410).sum := by decide
  have hdescent : baseEnd_394410 < baseStart_394410 := by decide
  rcases family_descends (prefixWord ++ tailWord_394410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394423 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 1, 5]
def baseStart_394423 : Nat := 118140960795 + 394423 * 2 ^ 59
def prefixEnd_394423 : Nat := 4983230072969 + 3 ^ 40 * 394423 * 2
def baseEnd_394423 : Nat := 135019053458943701265725

theorem tailTrace_394423 : CollatzResearch.WordTrace tailWord_394423 prefixEnd_394423 135019053458943701265725 := by
  unfold tailWord_394423
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385788650080307930539923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9590525766720205287026615 14385788650080307930539923)
  ·
    refine ⟨21578682975120461895809885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14385788650080307930539923 21578682975120461895809885)
    ·
      refine ⟨8092006115670173210928707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21578682975120461895809885 8092006115670173210928707)
      ·
        refine ⟨12138009173505259816393061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092006115670173210928707 12138009173505259816393061)
        ·
          refine ⟨2275876720032236215573699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12138009173505259816393061 2275876720032236215573699)
          ·
            refine ⟨3413815080048354323360549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275876720032236215573699 3413815080048354323360549)
            ·
              refine ⟨640090327509066435630103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3413815080048354323360549 640090327509066435630103)
              ·
                refine ⟨960135491263599653445155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640090327509066435630103 960135491263599653445155)
                ·
                  refine ⟨1440203236895399480167733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960135491263599653445155 1440203236895399480167733)
                  ·
                    refine ⟨135019053458943701265725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1440203236895399480167733 135019053458943701265725)
                    ·
                      rfl

theorem cell22_394423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_394423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394423 prefixEnd_394423 := by exact prefixLift 394423
  have htrace : WordTrace (prefixWord ++ tailWord_394423) baseStart_394423 baseEnd_394423 := by
    simpa [prefixWord, tailWord_394423, baseEnd_394423] using wordTrace_append hprefix tailTrace_394423
  have hstable : (prefixWord ++ tailWord_394423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394423).length < 2 ^ (prefixWord ++ tailWord_394423).sum := by decide
  have hdescent : baseEnd_394423 < baseStart_394423 := by decide
  rcases family_descends (prefixWord ++ tailWord_394423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394453 : List Nat := [1, 3, 2, 4, 1, 2, 9]
def baseStart_394453 : Nat := 118140960795 + 394453 * 2 ^ 59
def prefixEnd_394453 : Nat := 4983230072969 + 3 ^ 40 * 394453 * 2
def baseEnd_394453 : Nat := 5001086039704949000579

theorem tailTrace_394453 : CollatzResearch.WordTrace tailWord_394453 prefixEnd_394453 5001086039704949000579 := by
  unfold tailWord_394453
  simp only [CollatzResearch.WordTrace]
  refine ⟨14386882839971623054132013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9591255226647748702754675 14386882839971623054132013)
  ·
    refine ⟨5395081064989358645299505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14386882839971623054132013 5395081064989358645299505)
    ·
      refine ⟨4046310798742018983974629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5395081064989358645299505 4046310798742018983974629)
      ·
        refine ⟨758683274764128559495243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4046310798742018983974629 758683274764128559495243)
        ·
          refine ⟨1138024912146192839242865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758683274764128559495243 1138024912146192839242865)
          ·
            refine ⟨853518684109644629432149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138024912146192839242865 853518684109644629432149)
            ·
              refine ⟨5001086039704949000579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 853518684109644629432149 5001086039704949000579)
              ·
                rfl

theorem cell22_394453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 9].length) (baseStart_394453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394453 prefixEnd_394453 := by exact prefixLift 394453
  have htrace : WordTrace (prefixWord ++ tailWord_394453) baseStart_394453 baseEnd_394453 := by
    simpa [prefixWord, tailWord_394453, baseEnd_394453] using wordTrace_append hprefix tailTrace_394453
  have hstable : (prefixWord ++ tailWord_394453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394453).length < 2 ^ (prefixWord ++ tailWord_394453).sum := by decide
  have hdescent : baseEnd_394453 < baseStart_394453 := by decide
  rcases family_descends (prefixWord ++ tailWord_394453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394519 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 1, 3]
def baseStart_394519 : Nat := 118140960795 + 394519 * 2 ^ 59
def prefixEnd_394519 : Nat := 4983230072969 + 3 ^ 40 * 394519 * 2
def baseEnd_394519 : Nat := 135051916220831450865431

theorem tailTrace_394519 : CollatzResearch.WordTrace tailWord_394519 prefixEnd_394519 135051916220831450865431 := by
  unfold tailWord_394519
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389290057732516326034611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9592860038488344217356407 14389290057732516326034611)
  ·
    refine ⟨21583935086598774489051917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14389290057732516326034611 21583935086598774489051917)
    ·
      refine ⟨8093975657474540433394469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21583935086598774489051917 8093975657474540433394469)
      ·
        refine ⟨1517620435776476331261463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8093975657474540433394469 1517620435776476331261463)
        ·
          refine ⟨2276430653664714496892195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517620435776476331261463 2276430653664714496892195)
          ·
            refine ⟨3414645980497071745338293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276430653664714496892195 3414645980497071745338293)
            ·
              refine ⟨320123060671600476125465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3414645980497071745338293 320123060671600476125465)
              ·
                refine ⟨240092295503700357094099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320123060671600476125465 240092295503700357094099)
                ·
                  refine ⟨360138443255550535641149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240092295503700357094099 360138443255550535641149)
                  ·
                    refine ⟨135051916220831450865431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360138443255550535641149 135051916220831450865431)
                    ·
                      rfl

theorem cell22_394519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_394519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394519 prefixEnd_394519 := by exact prefixLift 394519
  have htrace : WordTrace (prefixWord ++ tailWord_394519) baseStart_394519 baseEnd_394519 := by
    simpa [prefixWord, tailWord_394519, baseEnd_394519] using wordTrace_append hprefix tailTrace_394519
  have hstable : (prefixWord ++ tailWord_394519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394519).length < 2 ^ (prefixWord ++ tailWord_394519).sum := by decide
  have hdescent : baseEnd_394519 < baseStart_394519 := by decide
  rcases family_descends (prefixWord ++ tailWord_394519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394545 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_394545 : Nat := 118140960795 + 394545 * 2 ^ 59
def prefixEnd_394545 : Nat := 4983230072969 + 3 ^ 40 * 394545 * 2
def baseEnd_394545 : Nat := 135060816552176049715351

theorem tailTrace_394545 : CollatzResearch.WordTrace tailWord_394545 prefixEnd_394545 135060816552176049715351 := by
  unfold tailWord_394545
  simp only [CollatzResearch.WordTrace]
  refine ⟨14390238355638322766481089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9593492237092215177654059 14390238355638322766481089)
  ·
    refine ⟨10792678766728742074860817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14390238355638322766481089 10792678766728742074860817)
    ·
      refine ⟨8094509075046556556145613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10792678766728742074860817 8094509075046556556145613)
      ·
        refine ⟨3035440903142458708554605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8094509075046556556145613 3035440903142458708554605)
        ·
          refine ⟨1138290338678422015707977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3035440903142458708554605 1138290338678422015707977)
          ·
            refine ⟨853717754008816511780983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138290338678422015707977 853717754008816511780983)
            ·
              refine ⟨1280576631013224767671475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853717754008816511780983 1280576631013224767671475)
              ·
                refine ⟨1920864946519837151507213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280576631013224767671475 1920864946519837151507213)
                ·
                  refine ⟨720324354944938931815205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1920864946519837151507213 720324354944938931815205)
                  ·
                    refine ⟨135060816552176049715351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720324354944938931815205 135060816552176049715351)
                    ·
                      rfl

theorem cell22_394545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_394545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394545 prefixEnd_394545 := by exact prefixLift 394545
  have htrace : WordTrace (prefixWord ++ tailWord_394545) baseStart_394545 baseEnd_394545 := by
    simpa [prefixWord, tailWord_394545, baseEnd_394545] using wordTrace_append hprefix tailTrace_394545
  have hstable : (prefixWord ++ tailWord_394545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394545).length < 2 ^ (prefixWord ++ tailWord_394545).sum := by decide
  have hdescent : baseEnd_394545 < baseStart_394545 := by decide
  rcases family_descends (prefixWord ++ tailWord_394545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394560 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 4]
def baseStart_394560 : Nat := 118140960795 + 394560 * 2 ^ 59
def prefixEnd_394560 : Nat := 4983230072969 + 3 ^ 40 * 394560 * 2
def baseEnd_394560 : Nat := 45021983786240336863435

theorem tailTrace_394560 : CollatzResearch.WordTrace tailWord_394560 prefixEnd_394560 45021983786240336863435 := by
  unfold tailWord_394560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195392725291990164138567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9593856967055986885518089 7195392725291990164138567)
  ·
    refine ⟨10793089087937985246207851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7195392725291990164138567 10793089087937985246207851)
    ·
      refine ⟨16189633631906977869311777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10793089087937985246207851 16189633631906977869311777)
      ·
        refine ⟨12142225223930233401983833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16189633631906977869311777 12142225223930233401983833)
        ·
          refine ⟨9106668917947675051487875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12142225223930233401983833 9106668917947675051487875)
          ·
            refine ⟨13660003376921512577231813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9106668917947675051487875 13660003376921512577231813)
            ·
              refine ⟨2561250633172783608230965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13660003376921512577231813 2561250633172783608230965)
              ·
                refine ⟨240117246859948463271653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2561250633172783608230965 240117246859948463271653)
                ·
                  refine ⟨45021983786240336863435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240117246859948463271653 45021983786240336863435)
                  ·
                    rfl

theorem cell22_394560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_394560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394560 prefixEnd_394560 := by exact prefixLift 394560
  have htrace : WordTrace (prefixWord ++ tailWord_394560) baseStart_394560 baseEnd_394560 := by
    simpa [prefixWord, tailWord_394560, baseEnd_394560] using wordTrace_append hprefix tailTrace_394560
  have hstable : (prefixWord ++ tailWord_394560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394560).length < 2 ^ (prefixWord ++ tailWord_394560).sum := by decide
  have hdescent : baseEnd_394560 < baseStart_394560 := by decide
  rcases family_descends (prefixWord ++ tailWord_394560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394566 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_394566 : Nat := 118140960795 + 394566 * 2 ^ 59
def prefixEnd_394566 : Nat := 4983230072969 + 3 ^ 40 * 394566 * 2
def baseEnd_394566 : Nat := 45022668427112998313429

theorem tailTrace_394566 : CollatzResearch.WordTrace tailWord_394566 prefixEnd_394566 45022668427112998313429 := by
  unfold tailWord_394566
  simp only [CollatzResearch.WordTrace]
  refine ⟨449718884017570104781111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9594002859041495568663701 449718884017570104781111)
  ·
    refine ⟨674578326026355157171667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449718884017570104781111 674578326026355157171667)
    ·
      refine ⟨1011867489039532735757501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674578326026355157171667 1011867489039532735757501)
      ·
        refine ⟨379450308389824775909063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1011867489039532735757501 379450308389824775909063)
        ·
          refine ⟨569175462584737163863595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379450308389824775909063 569175462584737163863595)
          ·
            refine ⟨853763193877105745795393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569175462584737163863595 853763193877105745795393)
            ·
              refine ⟨640322395407829309346545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853763193877105745795393 640322395407829309346545)
              ·
                refine ⟨480241796555871982009909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640322395407829309346545 480241796555871982009909)
                ·
                  refine ⟨45022668427112998313429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480241796555871982009909 45022668427112998313429)
                  ·
                    rfl

theorem cell22_394566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_394566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394566 prefixEnd_394566 := by exact prefixLift 394566
  have htrace : WordTrace (prefixWord ++ tailWord_394566) baseStart_394566 baseEnd_394566 := by
    simpa [prefixWord, tailWord_394566, baseEnd_394566] using wordTrace_append hprefix tailTrace_394566
  have hstable : (prefixWord ++ tailWord_394566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394566).length < 2 ^ (prefixWord ++ tailWord_394566).sum := by decide
  have hdescent : baseEnd_394566 < baseStart_394566 := by decide
  rcases family_descends (prefixWord ++ tailWord_394566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394592 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 2, 3]
def baseStart_394592 : Nat := 118140960795 + 394592 * 2 ^ 59
def prefixEnd_394592 : Nat := 4983230072969 + 3 ^ 40 * 394592 * 2
def baseEnd_394592 : Nat := 135076905612683593790207

theorem tailTrace_394592 : CollatzResearch.WordTrace tailWord_394592 prefixEnd_394592 135076905612683593790207 := by
  unfold tailWord_394592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195976293234024896721015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9594635057645366528961353 7195976293234024896721015)
  ·
    refine ⟨10793964439851037345081523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7195976293234024896721015 10793964439851037345081523)
    ·
      refine ⟨16190946659776556017622285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10793964439851037345081523 16190946659776556017622285)
      ·
        refine ⟨6071604997416208506608357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16190946659776556017622285 6071604997416208506608357)
        ·
          refine ⟨1138425937015539094989067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6071604997416208506608357 1138425937015539094989067)
          ·
            refine ⟨1707638905523308642483601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138425937015539094989067 1707638905523308642483601)
            ·
              refine ⟨1280729179142481481862701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707638905523308642483601 1280729179142481481862701)
              ·
                refine ⟨480273442178430555698513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1280729179142481481862701 480273442178430555698513)
                ·
                  refine ⟨360205081633822916773885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480273442178430555698513 360205081633822916773885)
                  ·
                    refine ⟨135076905612683593790207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360205081633822916773885 135076905612683593790207)
                    ·
                      rfl

theorem cell22_394592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_394592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394592 prefixEnd_394592 := by exact prefixLift 394592
  have htrace : WordTrace (prefixWord ++ tailWord_394592) baseStart_394592 baseEnd_394592 := by
    simpa [prefixWord, tailWord_394592, baseEnd_394592] using wordTrace_append hprefix tailTrace_394592
  have hstable : (prefixWord ++ tailWord_394592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394592).length < 2 ^ (prefixWord ++ tailWord_394592).sum := by decide
  have hdescent : baseEnd_394592 < baseStart_394592 := by decide
  rcases family_descends (prefixWord ++ tailWord_394592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394618 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_394618 : Nat := 118140960795 + 394618 * 2 ^ 59
def prefixEnd_394618 : Nat := 4983230072969 + 3 ^ 40 * 394618 * 2
def baseEnd_394618 : Nat := 135085805944028192640127

theorem tailTrace_394618 : CollatzResearch.WordTrace tailWord_394618 prefixEnd_394618 135085805944028192640127 := by
  unfold tailWord_394618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598225221093464058472127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9595267256249237489259005 3598225221093464058472127)
  ·
    refine ⟨5397337831640196087708191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3598225221093464058472127 5397337831640196087708191)
    ·
      refine ⟨8096006747460294131562287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5397337831640196087708191 8096006747460294131562287)
      ·
        refine ⟨12144010121190441197343431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096006747460294131562287 12144010121190441197343431)
        ·
          refine ⟨18216015181785661796015147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12144010121190441197343431 18216015181785661796015147)
          ·
            refine ⟨27324022772678492694022721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18216015181785661796015147 27324022772678492694022721)
            ·
              refine ⟨20493017079508869520517041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27324022772678492694022721 20493017079508869520517041)
              ·
                refine ⟨15369762809631652140387781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20493017079508869520517041 15369762809631652140387781)
                ·
                  refine ⟨2881830526805934776322709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15369762809631652140387781 2881830526805934776322709)
                  ·
                    refine ⟨135085805944028192640127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2881830526805934776322709 135085805944028192640127)
                    ·
                      rfl

theorem cell22_394618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_394618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394618 prefixEnd_394618 := by exact prefixLift 394618
  have htrace : WordTrace (prefixWord ++ tailWord_394618) baseStart_394618 baseEnd_394618 := by
    simpa [prefixWord, tailWord_394618, baseEnd_394618] using wordTrace_append hprefix tailTrace_394618
  have hstable : (prefixWord ++ tailWord_394618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394618).length < 2 ^ (prefixWord ++ tailWord_394618).sum := by decide
  have hdescent : baseEnd_394618 < baseStart_394618 := by decide
  rcases family_descends (prefixWord ++ tailWord_394618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394620 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_394620 : Nat := 118140960795 + 394620 * 2 ^ 59
def prefixEnd_394620 : Nat := 4983230072969 + 3 ^ 40 * 394620 * 2
def baseEnd_394620 : Nat := 135086490584900854090121

theorem tailTrace_394620 : CollatzResearch.WordTrace tailWord_394620 prefixEnd_394620 135086490584900854090121 := by
  unfold tailWord_394620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196486915183305287730657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9595315886911073716974209 7196486915183305287730657)
  ·
    refine ⟨5397365186387478965797993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7196486915183305287730657 5397365186387478965797993)
    ·
      refine ⟨4048023889790609224348495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5397365186387478965797993 4048023889790609224348495)
      ·
        refine ⟨6072035834685913836522743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048023889790609224348495 6072035834685913836522743)
        ·
          refine ⟨9108053752028870754784115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072035834685913836522743 9108053752028870754784115)
          ·
            refine ⟨13662080628043306132176173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108053752028870754784115 13662080628043306132176173)
            ·
              refine ⟨5123280235516239799566065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13662080628043306132176173 5123280235516239799566065)
              ·
                refine ⟨3842460176637179849674549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123280235516239799566065 3842460176637179849674549)
                ·
                  refine ⟨360230641559735610906989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842460176637179849674549 360230641559735610906989)
                  ·
                    refine ⟨135086490584900854090121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360230641559735610906989 135086490584900854090121)
                    ·
                      rfl

theorem cell22_394620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_394620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394620 prefixEnd_394620 := by exact prefixLift 394620
  have htrace : WordTrace (prefixWord ++ tailWord_394620) baseStart_394620 baseEnd_394620 := by
    simpa [prefixWord, tailWord_394620, baseEnd_394620] using wordTrace_append hprefix tailTrace_394620
  have hstable : (prefixWord ++ tailWord_394620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394620).length < 2 ^ (prefixWord ++ tailWord_394620).sum := by decide
  have hdescent : baseEnd_394620 < baseStart_394620 := by decide
  rcases family_descends (prefixWord ++ tailWord_394620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394626 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_394626 : Nat := 118140960795 + 394626 * 2 ^ 59
def prefixEnd_394626 : Nat := 4983230072969 + 3 ^ 40 * 394626 * 2
def baseEnd_394626 : Nat := 135088544507518838440103

theorem tailTrace_394626 : CollatzResearch.WordTrace tailWord_394626 prefixEnd_394626 135088544507518838440103 := by
  unfold tailWord_394626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598298167086218400044933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9595461778896582400119821 3598298167086218400044933)
  ·
    refine ⟨674680906328665950008425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3598298167086218400044933 674680906328665950008425)
    ·
      refine ⟨506010679746499462506319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 674680906328665950008425 506010679746499462506319)
      ·
        refine ⟨759016019619749193759479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506010679746499462506319 759016019619749193759479)
        ·
          refine ⟨1138524029429623790639219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759016019619749193759479 1138524029429623790639219)
          ·
            refine ⟨1707786044144435685958829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138524029429623790639219 1707786044144435685958829)
            ·
              refine ⟨640419766554163382234561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707786044144435685958829 640419766554163382234561)
              ·
                refine ⟨480314824915622536675921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640419766554163382234561 480314824915622536675921)
                ·
                  refine ⟨360236118686716902506941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480314824915622536675921 360236118686716902506941)
                  ·
                    refine ⟨135088544507518838440103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360236118686716902506941 135088544507518838440103)
                    ·
                      rfl

theorem cell22_394626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_394626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394626 prefixEnd_394626 := by exact prefixLift 394626
  have htrace : WordTrace (prefixWord ++ tailWord_394626) baseStart_394626 baseEnd_394626 := by
    simpa [prefixWord, tailWord_394626, baseEnd_394626] using wordTrace_append hprefix tailTrace_394626
  have hstable : (prefixWord ++ tailWord_394626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394626).length < 2 ^ (prefixWord ++ tailWord_394626).sum := by decide
  have hdescent : baseEnd_394626 < baseStart_394626 := by decide
  rcases family_descends (prefixWord ++ tailWord_394626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394714 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_394714 : Nat := 118140960795 + 394714 * 2 ^ 59
def prefixEnd_394714 : Nat := 4983230072969 + 3 ^ 40 * 394714 * 2
def baseEnd_394714 : Nat := 135118668705915942239833

theorem tailTrace_394714 : CollatzResearch.WordTrace tailWord_394714 prefixEnd_394714 135118668705915942239833 := by
  unfold tailWord_394714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599100573006516157345799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9597601528017376419588797 3599100573006516157345799)
  ·
    refine ⟨5398650859509774236018699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599100573006516157345799 5398650859509774236018699)
    ·
      refine ⟨8097976289264661354028049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5398650859509774236018699 8097976289264661354028049)
      ·
        refine ⟨6073482216948496015521037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8097976289264661354028049 6073482216948496015521037)
        ·
          refine ⟨2277555831355686005820389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6073482216948496015521037 2277555831355686005820389)
          ·
            refine ⟨427041718379191126091323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2277555831355686005820389 427041718379191126091323)
            ·
              refine ⟨640562577568786689136985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427041718379191126091323 640562577568786689136985)
              ·
                refine ⟨480421933176590016852739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640562577568786689136985 480421933176590016852739)
                ·
                  refine ⟨720632899764885025279109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480421933176590016852739 720632899764885025279109)
                  ·
                    refine ⟨135118668705915942239833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720632899764885025279109 135118668705915942239833)
                    ·
                      rfl

theorem cell22_394714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_394714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394714 prefixEnd_394714 := by exact prefixLift 394714
  have htrace : WordTrace (prefixWord ++ tailWord_394714) baseStart_394714 baseEnd_394714 := by
    simpa [prefixWord, tailWord_394714, baseEnd_394714] using wordTrace_append hprefix tailTrace_394714
  have hstable : (prefixWord ++ tailWord_394714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394714).length < 2 ^ (prefixWord ++ tailWord_394714).sum := by decide
  have hdescent : baseEnd_394714 < baseStart_394714 := by decide
  rcases family_descends (prefixWord ++ tailWord_394714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394727 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 1, 5]
def baseStart_394727 : Nat := 118140960795 + 394727 * 2 ^ 59
def prefixEnd_394727 : Nat := 4983230072969 + 3 ^ 40 * 394727 * 2
def baseEnd_394727 : Nat := 135123118871588241664793

theorem tailTrace_394727 : CollatzResearch.WordTrace tailWord_394727 prefixEnd_394727 135123118871588241664793 := by
  unfold tailWord_394727
  simp only [CollatzResearch.WordTrace]
  refine ⟨14396876440978967849606435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9597917627319311899737623 14396876440978967849606435)
  ·
    refine ⟨21595314661468451774409653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14396876440978967849606435 21595314661468451774409653)
    ·
      refine ⟨2024560749512667353850905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21595314661468451774409653 2024560749512667353850905)
      ·
        refine ⟨1518420562134500515388179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2024560749512667353850905 1518420562134500515388179)
        ·
          refine ⟨2277630843201750773082269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518420562134500515388179 2277630843201750773082269)
          ·
            refine ⟨854111566200656539905851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2277630843201750773082269 854111566200656539905851)
            ·
              refine ⟨1281167349300984809858777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854111566200656539905851 1281167349300984809858777)
              ·
                refine ⟨960875511975738607394083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281167349300984809858777 960875511975738607394083)
                ·
                  refine ⟨1441313267963607911091125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960875511975738607394083 1441313267963607911091125)
                  ·
                    refine ⟨135123118871588241664793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1441313267963607911091125 135123118871588241664793)
                    ·
                      rfl

theorem cell22_394727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_394727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394727 prefixEnd_394727 := by exact prefixLift 394727
  have htrace : WordTrace (prefixWord ++ tailWord_394727) baseStart_394727 baseEnd_394727 := by
    simpa [prefixWord, tailWord_394727, baseEnd_394727] using wordTrace_append hprefix tailTrace_394727
  have hstable : (prefixWord ++ tailWord_394727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394727).length < 2 ^ (prefixWord ++ tailWord_394727).sum := by decide
  have hdescent : baseEnd_394727 < baseStart_394727 := by decide
  rcases family_descends (prefixWord ++ tailWord_394727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394744 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_394744 : Nat := 118140960795 + 394744 * 2 ^ 59
def prefixEnd_394744 : Nat := 4983230072969 + 3 ^ 40 * 394744 * 2
def baseEnd_394744 : Nat := 135128938319005863989741

theorem tailTrace_394744 : CollatzResearch.WordTrace tailWord_394744 prefixEnd_394744 135128938319005863989741 := by
  unfold tailWord_394744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198748240958689876487643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9598330987944919835316857 7198748240958689876487643)
  ·
    refine ⟨10798122361438034814731465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7198748240958689876487643 10798122361438034814731465)
    ·
      refine ⟨8098591771078526111048599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10798122361438034814731465 8098591771078526111048599)
      ·
        refine ⟨12147887656617789166572899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098591771078526111048599 12147887656617789166572899)
        ·
          refine ⟨18221831484926683749859349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12147887656617789166572899 18221831484926683749859349)
          ·
            refine ⟨854148350855938300774657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18221831484926683749859349 854148350855938300774657)
            ·
              refine ⟨640611263141953725580993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854148350855938300774657 640611263141953725580993)
              ·
                refine ⟨480458447356465294185745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640611263141953725580993 480458447356465294185745)
                ·
                  refine ⟨360343835517348970639309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480458447356465294185745 360343835517348970639309)
                  ·
                    refine ⟨135128938319005863989741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360343835517348970639309 135128938319005863989741)
                    ·
                      rfl

theorem cell22_394744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_394744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394744 prefixEnd_394744 := by exact prefixLift 394744
  have htrace : WordTrace (prefixWord ++ tailWord_394744) baseStart_394744 baseEnd_394744 := by
    simpa [prefixWord, tailWord_394744, baseEnd_394744] using wordTrace_append hprefix tailTrace_394744
  have hstable : (prefixWord ++ tailWord_394744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394744).length < 2 ^ (prefixWord ++ tailWord_394744).sum := by decide
  have hdescent : baseEnd_394744 < baseStart_394744 := by decide
  rcases family_descends (prefixWord ++ tailWord_394744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394776 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 2, 4]
def baseStart_394776 : Nat := 118140960795 + 394776 * 2 ^ 59
def prefixEnd_394776 : Nat := 4983230072969 + 3 ^ 40 * 394776 * 2
def baseEnd_394776 : Nat := 135139892572968447189643

theorem tailTrace_394776 : CollatzResearch.WordTrace tailWord_394776 prefixEnd_394776 135139892572968447189643 := by
  unfold tailWord_394776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199331808900724609070091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9599109078534299478760121 7199331808900724609070091)
  ·
    refine ⟨10798997713351086913605137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199331808900724609070091 10798997713351086913605137)
    ·
      refine ⟨8099248285013315185203853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10798997713351086913605137 8099248285013315185203853)
      ·
        refine ⟨3037218106879993194451445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8099248285013315185203853 3037218106879993194451445)
        ·
          refine ⟨284739197519999361979823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3037218106879993194451445 284739197519999361979823)
          ·
            refine ⟨427108796279999042969735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284739197519999361979823 427108796279999042969735)
            ·
              refine ⟨640663194419998564454603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427108796279999042969735 640663194419998564454603)
              ·
                refine ⟨960994791629997846681905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640663194419998564454603 960994791629997846681905)
                ·
                  refine ⟨720746093722498385011429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 960994791629997846681905 720746093722498385011429)
                  ·
                    refine ⟨135139892572968447189643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720746093722498385011429 135139892572968447189643)
                    ·
                      rfl

theorem cell22_394776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_394776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394776 prefixEnd_394776 := by exact prefixLift 394776
  have htrace : WordTrace (prefixWord ++ tailWord_394776) baseStart_394776 baseEnd_394776 := by
    simpa [prefixWord, tailWord_394776, baseEnd_394776] using wordTrace_append hprefix tailTrace_394776
  have hstable : (prefixWord ++ tailWord_394776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394776).length < 2 ^ (prefixWord ++ tailWord_394776).sum := by decide
  have hdescent : baseEnd_394776 < baseStart_394776 := by decide
  rcases family_descends (prefixWord ++ tailWord_394776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394782 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_394782 : Nat := 118140960795 + 394782 * 2 ^ 59
def prefixEnd_394782 : Nat := 4983230072969 + 3 ^ 40 * 394782 * 2
def baseEnd_394782 : Nat := 135141946495586431539625

theorem tailTrace_394782 : CollatzResearch.WordTrace tailWord_394782 prefixEnd_394782 135141946495586431539625 := by
  unfold tailWord_394782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1799860306972464030357325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9599254970519808161905733 1799860306972464030357325)
  ·
    refine ⟨674947615114674011383997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1799860306972464030357325 674947615114674011383997)
    ·
      refine ⟨253105355668002754268999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 674947615114674011383997 253105355668002754268999)
      ·
        refine ⟨379658033502004131403499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253105355668002754268999 379658033502004131403499)
        ·
          refine ⟨569487050253006197105249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379658033502004131403499 569487050253006197105249)
          ·
            refine ⟨427115287689754647828937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569487050253006197105249 427115287689754647828937)
            ·
              refine ⟨320336465767315985871703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427115287689754647828937 320336465767315985871703)
              ·
                refine ⟨480504698650973978807555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320336465767315985871703 480504698650973978807555)
                ·
                  refine ⟨720757047976460968211333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480504698650973978807555 720757047976460968211333)
                  ·
                    refine ⟨135141946495586431539625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720757047976460968211333 135141946495586431539625)
                    ·
                      rfl

theorem cell22_394782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_394782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394782 prefixEnd_394782 := by exact prefixLift 394782
  have htrace : WordTrace (prefixWord ++ tailWord_394782) baseStart_394782 baseEnd_394782 := by
    simpa [prefixWord, tailWord_394782, baseEnd_394782] using wordTrace_append hprefix tailTrace_394782
  have hstable : (prefixWord ++ tailWord_394782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394782).length < 2 ^ (prefixWord ++ tailWord_394782).sum := by decide
  have hdescent : baseEnd_394782 < baseStart_394782 := by decide
  rcases family_descends (prefixWord ++ tailWord_394782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394817 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_394817 : Nat := 118140960795 + 394817 * 2 ^ 59
def prefixEnd_394817 : Nat := 4983230072969 + 3 ^ 40 * 394817 * 2
def baseEnd_394817 : Nat := 135153927710858006914517

theorem tailTrace_394817 : CollatzResearch.WordTrace tailWord_394817 prefixEnd_394817 135153927710858006914517 := by
  unfold tailWord_394817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400159010652913220382705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9600106007101942146921803 14400159010652913220382705)
  ·
    refine ⟨10800119257989684915287029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14400159010652913220382705 10800119257989684915287029)
    ·
      refine ⟨1012511180436532960808159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10800119257989684915287029 1012511180436532960808159)
      ·
        refine ⟨1518766770654799441212239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012511180436532960808159 1518766770654799441212239)
        ·
          refine ⟨2278150155982199161818359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518766770654799441212239 2278150155982199161818359)
          ·
            refine ⟨3417225233973298742727539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278150155982199161818359 3417225233973298742727539)
            ·
              refine ⟨5125837850959948114091309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417225233973298742727539 5125837850959948114091309)
              ·
                refine ⟨1922189194109980542784241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125837850959948114091309 1922189194109980542784241)
                ·
                  refine ⟨1441641895582485407088181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922189194109980542784241 1441641895582485407088181)
                  ·
                    refine ⟨135153927710858006914517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1441641895582485407088181 135153927710858006914517)
                    ·
                      rfl

theorem cell22_394817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_394817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394817 prefixEnd_394817 := by exact prefixLift 394817
  have htrace : WordTrace (prefixWord ++ tailWord_394817) baseStart_394817 baseEnd_394817 := by
    simpa [prefixWord, tailWord_394817, baseEnd_394817] using wordTrace_append hprefix tailTrace_394817
  have hstable : (prefixWord ++ tailWord_394817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394817).length < 2 ^ (prefixWord ++ tailWord_394817).sum := by decide
  have hdescent : baseEnd_394817 < baseStart_394817 := by decide
  rcases family_descends (prefixWord ++ tailWord_394817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394864 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 6]
def baseStart_394864 : Nat := 118140960795 + 394864 * 2 ^ 59
def prefixEnd_394864 : Nat := 4983230072969 + 3 ^ 40 * 394864 * 2
def baseEnd_394864 : Nat := 45056672257121850329791

theorem tailTrace_394864 : CollatzResearch.WordTrace tailWord_394864 prefixEnd_394864 45056672257121850329791 := by
  unfold tailWord_394864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200936620741320123671823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9601248827655093498229097 7200936620741320123671823)
  ·
    refine ⟨10801404931111980185507735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7200936620741320123671823 10801404931111980185507735)
    ·
      refine ⟨16202107396667970278261603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10801404931111980185507735 16202107396667970278261603)
      ·
        refine ⟨24303161095001955417392405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16202107396667970278261603 24303161095001955417392405)
        ·
          refine ⟨1139210676328216660190269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24303161095001955417392405 1139210676328216660190269)
          ·
            refine ⟨427204003623081247571351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1139210676328216660190269 427204003623081247571351)
            ·
              refine ⟨640806005434621871357027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427204003623081247571351 640806005434621871357027)
              ·
                refine ⟨961209008151932807035541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640806005434621871357027 961209008151932807035541)
                ·
                  refine ⟨45056672257121850329791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 961209008151932807035541 45056672257121850329791)
                  ·
                    rfl

theorem cell22_394864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_394864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394864 prefixEnd_394864 := by exact prefixLift 394864
  have htrace : WordTrace (prefixWord ++ tailWord_394864) baseStart_394864 baseEnd_394864 := by
    simpa [prefixWord, tailWord_394864, baseEnd_394864] using wordTrace_append hprefix tailTrace_394864
  have hstable : (prefixWord ++ tailWord_394864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394864).length < 2 ^ (prefixWord ++ tailWord_394864).sum := by decide
  have hdescent : baseEnd_394864 < baseStart_394864 := by decide
  rcases family_descends (prefixWord ++ tailWord_394864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394894 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_394894 : Nat := 118140960795 + 394894 * 2 ^ 59
def prefixEnd_394894 : Nat := 4983230072969 + 3 ^ 40 * 394894 * 2
def baseEnd_394894 : Nat := 135180286384455472739281

theorem tailTrace_394894 : CollatzResearch.WordTrace tailWord_394894 prefixEnd_394894 135180286384455472739281 := by
  unfold tailWord_394894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800370928921744421366967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9601978287582636913957157 1800370928921744421366967)
  ·
    refine ⟨2700556393382616632050451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800370928921744421366967 2700556393382616632050451)
    ·
      refine ⟨4050834590073924948075677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700556393382616632050451 4050834590073924948075677)
      ·
        refine ⟨1519062971277721855528379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4050834590073924948075677 1519062971277721855528379)
        ·
          refine ⟨2278594456916582783292569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519062971277721855528379 2278594456916582783292569)
          ·
            refine ⟨1708945842687437087469427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278594456916582783292569 1708945842687437087469427)
            ·
              refine ⟨2563418764031155631204141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708945842687437087469427 2563418764031155631204141)
              ·
                refine ⟨961282036511683361701553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2563418764031155631204141 961282036511683361701553)
                ·
                  refine ⟨720961527383762521276165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961282036511683361701553 720961527383762521276165)
                  ·
                    refine ⟨135180286384455472739281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720961527383762521276165 135180286384455472739281)
                    ·
                      rfl

theorem cell22_394894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_394894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394894 prefixEnd_394894 := by exact prefixLift 394894
  have htrace : WordTrace (prefixWord ++ tailWord_394894) baseStart_394894 baseEnd_394894 := by
    simpa [prefixWord, tailWord_394894, baseEnd_394894] using wordTrace_append hprefix tailTrace_394894
  have hstable : (prefixWord ++ tailWord_394894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394894).length < 2 ^ (prefixWord ++ tailWord_394894).sum := by decide
  have hdescent : baseEnd_394894 < baseStart_394894 := by decide
  rcases family_descends (prefixWord ++ tailWord_394894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394952 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_394952 : Nat := 118140960795 + 394952 * 2 ^ 59
def prefixEnd_394952 : Nat := 4983230072969 + 3 ^ 40 * 394952 * 2
def baseEnd_394952 : Nat := 135200140969762654789103

theorem tailTrace_394952 : CollatzResearch.WordTrace tailWord_394952 prefixEnd_394952 135200140969762654789103 := by
  unfold tailWord_394952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202541432581915638273555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9603388576775887517698073 7202541432581915638273555)
  ·
    refine ⟨10803812148872873457410333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7202541432581915638273555 10803812148872873457410333)
    ·
      refine ⟨4051429555827327546528875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10803812148872873457410333 4051429555827327546528875)
      ·
        refine ⟨6077144333740991319793313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051429555827327546528875 6077144333740991319793313)
        ·
          refine ⟨4557858250305743489844985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6077144333740991319793313 4557858250305743489844985)
          ·
            refine ⟨3418393687729307617383739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4557858250305743489844985 3418393687729307617383739)
            ·
              refine ⟨5127590531593961426075609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418393687729307617383739 5127590531593961426075609)
              ·
                refine ⟨3845692898695471069556707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5127590531593961426075609 3845692898695471069556707)
                ·
                  refine ⟨5768539348043206604335061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845692898695471069556707 5768539348043206604335061)
                  ·
                    refine ⟨135200140969762654789103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5768539348043206604335061 135200140969762654789103)
                    ·
                      rfl

theorem cell22_394952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_394952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394952 prefixEnd_394952 := by exact prefixLift 394952
  have htrace : WordTrace (prefixWord ++ tailWord_394952) baseStart_394952 baseEnd_394952 := by
    simpa [prefixWord, tailWord_394952, baseEnd_394952] using wordTrace_append hprefix tailTrace_394952
  have hstable : (prefixWord ++ tailWord_394952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394952).length < 2 ^ (prefixWord ++ tailWord_394952).sum := by decide
  have hdescent : baseEnd_394952 < baseStart_394952 := by decide
  rcases family_descends (prefixWord ++ tailWord_394952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394958 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_394958 : Nat := 118140960795 + 394958 * 2 ^ 59
def prefixEnd_394958 : Nat := 4983230072969 + 3 ^ 40 * 394958 * 2
def baseEnd_394958 : Nat := 135202194892380639139085

theorem tailTrace_394958 : CollatzResearch.WordTrace tailWord_394958 prefixEnd_394958 135202194892380639139085 := by
  unfold tailWord_394958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800662712892761787658191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9603534468761396200843685 1800662712892761787658191)
  ·
    refine ⟨2700994069339142681487287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800662712892761787658191 2700994069339142681487287)
    ·
      refine ⟨4051491104008714022230931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700994069339142681487287 4051491104008714022230931)
      ·
        refine ⟨6077236656013071033346397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051491104008714022230931 6077236656013071033346397)
        ·
          refine ⟨2278963746004901637504899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6077236656013071033346397 2278963746004901637504899)
          ·
            refine ⟨3418445619007352456257349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278963746004901637504899 3418445619007352456257349)
            ·
              refine ⟨640958553563878585548253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3418445619007352456257349 640958553563878585548253)
              ·
                refine ⟨240359457586454469580595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640958553563878585548253 240359457586454469580595)
                ·
                  refine ⟨360539186379681704370893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240359457586454469580595 360539186379681704370893)
                  ·
                    refine ⟨135202194892380639139085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360539186379681704370893 135202194892380639139085)
                    ·
                      rfl

theorem cell22_394958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_394958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_394958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_394958 prefixEnd_394958 := by exact prefixLift 394958
  have htrace : WordTrace (prefixWord ++ tailWord_394958) baseStart_394958 baseEnd_394958 := by
    simpa [prefixWord, tailWord_394958, baseEnd_394958] using wordTrace_append hprefix tailTrace_394958
  have hstable : (prefixWord ++ tailWord_394958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394958).length < 2 ^ (prefixWord ++ tailWord_394958).sum := by decide
  have hdescent : baseEnd_394958 < baseStart_394958 := by decide
  rcases family_descends (prefixWord ++ tailWord_394958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395029 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_395029 : Nat := 118140960795 + 395029 * 2 ^ 59
def prefixEnd_395029 : Nat := 4983230072969 + 3 ^ 40 * 395029 * 2
def baseEnd_395029 : Nat := 135226499643360120613867

theorem tailTrace_395029 : CollatzResearch.WordTrace tailWord_395029 prefixEnd_395029 135226499643360120613867 := by
  unfold tailWord_395029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407891285884873427100141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9605260857256582284733427 14407891285884873427100141)
  ·
    refine ⟨5402959232206827535162553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14407891285884873427100141 5402959232206827535162553)
    ·
      refine ⟨4052219424155120651371915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5402959232206827535162553 4052219424155120651371915)
      ·
        refine ⟨6078329136232680977057873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052219424155120651371915 6078329136232680977057873)
        ·
          refine ⟨4558746852174510732793405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6078329136232680977057873 4558746852174510732793405)
          ·
            refine ⟨1709530069565441524797527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4558746852174510732793405 1709530069565441524797527)
            ·
              refine ⟨2564295104348162287196291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709530069565441524797527 2564295104348162287196291)
              ·
                refine ⟨3846442656522243430794437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564295104348162287196291 3846442656522243430794437)
                ·
                  refine ⟨721207998097920643273957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3846442656522243430794437 721207998097920643273957)
                  ·
                    refine ⟨135226499643360120613867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721207998097920643273957 135226499643360120613867)
                    ·
                      rfl

theorem cell22_395029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_395029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395029 prefixEnd_395029 := by exact prefixLift 395029
  have htrace : WordTrace (prefixWord ++ tailWord_395029) baseStart_395029 baseEnd_395029 := by
    simpa [prefixWord, tailWord_395029, baseEnd_395029] using wordTrace_append hprefix tailTrace_395029
  have hstable : (prefixWord ++ tailWord_395029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395029).length < 2 ^ (prefixWord ++ tailWord_395029).sum := by decide
  have hdescent : baseEnd_395029 < baseStart_395029 := by decide
  rcases family_descends (prefixWord ++ tailWord_395029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395031 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 4, 3]
def baseStart_395031 : Nat := 118140960795 + 395031 * 2 ^ 59
def prefixEnd_395031 : Nat := 4983230072969 + 3 ^ 40 * 395031 * 2
def baseEnd_395031 : Nat := 135227184284232782063861

theorem tailTrace_395031 : CollatzResearch.WordTrace tailWord_395031 prefixEnd_395031 135227184284232782063861 := by
  unfold tailWord_395031
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407964231877627768672947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9605309487918418512448631 14407964231877627768672947)
  ·
    refine ⟨21611946347816441653009421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14407964231877627768672947 21611946347816441653009421)
    ·
      refine ⟨8104479880431165619878533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21611946347816441653009421 8104479880431165619878533)
      ·
        refine ⟨1519589977580843553727225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8104479880431165619878533 1519589977580843553727225)
        ·
          refine ⟨1139692483185632665295419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519589977580843553727225 1139692483185632665295419)
          ·
            refine ⟨1709538724778448997943129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139692483185632665295419 1709538724778448997943129)
            ·
              refine ⟨1282154043583836748457347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709538724778448997943129 1282154043583836748457347)
              ·
                refine ⟨1923231065375755122686021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282154043583836748457347 1923231065375755122686021)
                ·
                  refine ⟨360605824757954085503629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923231065375755122686021 360605824757954085503629)
                  ·
                    refine ⟨135227184284232782063861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360605824757954085503629 135227184284232782063861)
                    ·
                      rfl

theorem cell22_395031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_395031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395031 prefixEnd_395031 := by exact prefixLift 395031
  have htrace : WordTrace (prefixWord ++ tailWord_395031) baseStart_395031 baseEnd_395031 := by
    simpa [prefixWord, tailWord_395031, baseEnd_395031] using wordTrace_append hprefix tailTrace_395031
  have hstable : (prefixWord ++ tailWord_395031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395031).length < 2 ^ (prefixWord ++ tailWord_395031).sum := by decide
  have hdescent : baseEnd_395031 < baseStart_395031 := by decide
  rcases family_descends (prefixWord ++ tailWord_395031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395044 : List Nat := [2, 3, 1, 3, 2, 1, 1, 9]
def baseStart_395044 : Nat := 118140960795 + 395044 * 2 ^ 59
def prefixEnd_395044 : Nat := 4983230072969 + 3 ^ 40 * 395044 * 2
def baseEnd_395044 : Nat := 15025737161100564609869

theorem tailTrace_395044 : CollatzResearch.WordTrace tailWord_395044 prefixEnd_395044 15025737161100564609869 := by
  unfold tailWord_395044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204219190415265494448093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9605625587220353992597457 7204219190415265494448093)
  ·
    refine ⟨2701582196405724560418035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7204219190415265494448093 2701582196405724560418035)
    ·
      refine ⟨4052373294608586840627053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701582196405724560418035 4052373294608586840627053)
      ·
        refine ⟨1519639985478220065235145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4052373294608586840627053 1519639985478220065235145)
        ·
          refine ⟨1139729989108665048926359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519639985478220065235145 1139729989108665048926359)
          ·
            refine ⟨1709594983662997573389539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139729989108665048926359 1709594983662997573389539)
            ·
              refine ⟨2564392475494496360084309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709594983662997573389539 2564392475494496360084309)
              ·
                refine ⟨15025737161100564609869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2564392475494496360084309 15025737161100564609869)
                ·
                  rfl

theorem cell22_395044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_395044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395044 prefixEnd_395044 := by exact prefixLift 395044
  have htrace : WordTrace (prefixWord ++ tailWord_395044) baseStart_395044 baseEnd_395044 := by
    simpa [prefixWord, tailWord_395044, baseEnd_395044] using wordTrace_append hprefix tailTrace_395044
  have hstable : (prefixWord ++ tailWord_395044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395044).length < 2 ^ (prefixWord ++ tailWord_395044).sum := by decide
  have hdescent : baseEnd_395044 < baseStart_395044 := by decide
  rcases family_descends (prefixWord ++ tailWord_395044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395048 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_395048 : Nat := 118140960795 + 395048 * 2 ^ 59
def prefixEnd_395048 : Nat := 4983230072969 + 3 ^ 40 * 395048 * 2
def baseEnd_395048 : Nat := 135233003731650404388809

theorem tailTrace_395048 : CollatzResearch.WordTrace tailWord_395048 prefixEnd_395048 135233003731650404388809 := by
  unfold tailWord_395048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204292136408019836020899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9605722848544026448027865 7204292136408019836020899)
  ·
    refine ⟨10806438204612029754031349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7204292136408019836020899 10806438204612029754031349)
    ·
      refine ⟨1013103581682377789440439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10806438204612029754031349 1013103581682377789440439)
      ·
        refine ⟨1519655372523566684160659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013103581682377789440439 1519655372523566684160659)
        ·
          refine ⟨2279483058785350026240989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519655372523566684160659 2279483058785350026240989)
          ·
            refine ⟨854806147044506259840371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2279483058785350026240989 854806147044506259840371)
            ·
              refine ⟨1282209220566759389760557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854806147044506259840371 1282209220566759389760557)
              ·
                refine ⟨480828457712534771160209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282209220566759389760557 480828457712534771160209)
                ·
                  refine ⟨360621343284401078370157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480828457712534771160209 360621343284401078370157)
                  ·
                    refine ⟨135233003731650404388809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360621343284401078370157 135233003731650404388809)
                    ·
                      rfl

theorem cell22_395048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_395048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395048 prefixEnd_395048 := by exact prefixLift 395048
  have htrace : WordTrace (prefixWord ++ tailWord_395048) baseStart_395048 baseEnd_395048 := by
    simpa [prefixWord, tailWord_395048, baseEnd_395048] using wordTrace_append hprefix tailTrace_395048
  have hstable : (prefixWord ++ tailWord_395048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395048).length < 2 ^ (prefixWord ++ tailWord_395048).sum := by decide
  have hdescent : baseEnd_395048 < baseStart_395048 := by decide
  rcases family_descends (prefixWord ++ tailWord_395048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395104 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_395104 : Nat := 118140960795 + 395104 * 2 ^ 59
def prefixEnd_395104 : Nat := 4983230072969 + 3 ^ 40 * 395104 * 2
def baseEnd_395104 : Nat := 135252173676084924988637

theorem tailTrace_395104 : CollatzResearch.WordTrace tailWord_395104 prefixEnd_395104 135252173676084924988637 := by
  unfold tailWord_395104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205313380306580618040183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9607084507075440824053577 7205313380306580618040183)
  ·
    refine ⟨10807970070459870927060275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205313380306580618040183 10807970070459870927060275)
    ·
      refine ⟨16211955105689806390590413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807970070459870927060275 16211955105689806390590413)
      ·
        refine ⟨6079483164633677396471405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16211955105689806390590413 6079483164633677396471405)
        ·
          refine ⟨2279806186737629023676777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6079483164633677396471405 2279806186737629023676777)
          ·
            refine ⟨1709854640053221767757583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2279806186737629023676777 1709854640053221767757583)
            ·
              refine ⟨2564781960079832651636375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709854640053221767757583 2564781960079832651636375)
              ·
                refine ⟨3847172940119748977454563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564781960079832651636375 3847172940119748977454563)
                ·
                  refine ⟨5770759410179623466181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847172940119748977454563 5770759410179623466181845)
                  ·
                    refine ⟨135252173676084924988637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5770759410179623466181845 135252173676084924988637)
                    ·
                      rfl

theorem cell22_395104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_395104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395104 prefixEnd_395104 := by exact prefixLift 395104
  have htrace : WordTrace (prefixWord ++ tailWord_395104) baseStart_395104 baseEnd_395104 := by
    simpa [prefixWord, tailWord_395104, baseEnd_395104] using wordTrace_append hprefix tailTrace_395104
  have hstable : (prefixWord ++ tailWord_395104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395104).length < 2 ^ (prefixWord ++ tailWord_395104).sum := by decide
  have hdescent : baseEnd_395104 < baseStart_395104 := by decide
  rcases family_descends (prefixWord ++ tailWord_395104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395136 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_395136 : Nat := 118140960795 + 395136 * 2 ^ 59
def prefixEnd_395136 : Nat := 4983230072969 + 3 ^ 40 * 395136 * 2
def baseEnd_395136 : Nat := 135263127930047508188539

theorem tailTrace_395136 : CollatzResearch.WordTrace tailWord_395136 prefixEnd_395136 135263127930047508188539 := by
  unfold tailWord_395136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205896948248615350622631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9607862597664820467496841 7205896948248615350622631)
  ·
    refine ⟨10808845422372923025933947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205896948248615350622631 10808845422372923025933947)
    ·
      refine ⟨16213268133559384538900921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808845422372923025933947 16213268133559384538900921)
      ·
        refine ⟨12159951100169538404175691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16213268133559384538900921 12159951100169538404175691)
        ·
          refine ⟨18239926650254307606263537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12159951100169538404175691 18239926650254307606263537)
          ·
            refine ⟨13679944987690730704697653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18239926650254307606263537 13679944987690730704697653)
            ·
              refine ⟨1282494842596006003565405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13679944987690730704697653 1282494842596006003565405)
              ·
                refine ⟨480935565973502251337027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282494842596006003565405 480935565973502251337027)
                ·
                  refine ⟨721403348960253377005541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480935565973502251337027 721403348960253377005541)
                  ·
                    refine ⟨135263127930047508188539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721403348960253377005541 135263127930047508188539)
                    ·
                      rfl

theorem cell22_395136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_395136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395136 prefixEnd_395136 := by exact prefixLift 395136
  have htrace : WordTrace (prefixWord ++ tailWord_395136) baseStart_395136 baseEnd_395136 := by
    simpa [prefixWord, tailWord_395136, baseEnd_395136] using wordTrace_append hprefix tailTrace_395136
  have hstable : (prefixWord ++ tailWord_395136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395136).length < 2 ^ (prefixWord ++ tailWord_395136).sum := by decide
  have hdescent : baseEnd_395136 < baseStart_395136 := by decide
  rcases family_descends (prefixWord ++ tailWord_395136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395170 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_395170 : Nat := 118140960795 + 395170 * 2 ^ 59
def prefixEnd_395170 : Nat := 4983230072969 + 3 ^ 40 * 395170 * 2
def baseEnd_395170 : Nat := 135274766824882752838435

theorem tailTrace_395170 : CollatzResearch.WordTrace tailWord_395170 prefixEnd_395170 135274766824882752838435 := by
  unfold tailWord_395170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603258494593513626995741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9608689318916036338655309 3603258494593513626995741)
  ·
    refine ⟨1351221935472567610123403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3603258494593513626995741 1351221935472567610123403)
    ·
      refine ⟨2026832903208851415185105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351221935472567610123403 2026832903208851415185105)
      ·
        refine ⟨1520124677406638561388829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2026832903208851415185105 1520124677406638561388829)
        ·
          refine ⟨570046754027489460520811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1520124677406638561388829 570046754027489460520811)
          ·
            refine ⟨855070131041234190781217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570046754027489460520811 855070131041234190781217)
            ·
              refine ⟨641302598280925643085913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855070131041234190781217 641302598280925643085913)
              ·
                refine ⟨480976948710694232314435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641302598280925643085913 480976948710694232314435)
                ·
                  refine ⟨721465423066041348471653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480976948710694232314435 721465423066041348471653)
                  ·
                    refine ⟨135274766824882752838435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721465423066041348471653 135274766824882752838435)
                    ·
                      rfl

theorem cell22_395170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_395170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395170 prefixEnd_395170 := by exact prefixLift 395170
  have htrace : WordTrace (prefixWord ++ tailWord_395170) baseStart_395170 baseEnd_395170 := by
    simpa [prefixWord, tailWord_395170, baseEnd_395170] using wordTrace_append hprefix tailTrace_395170
  have hstable : (prefixWord ++ tailWord_395170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395170).length < 2 ^ (prefixWord ++ tailWord_395170).sum := by decide
  have hdescent : baseEnd_395170 < baseStart_395170 := by decide
  rcases family_descends (prefixWord ++ tailWord_395170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
