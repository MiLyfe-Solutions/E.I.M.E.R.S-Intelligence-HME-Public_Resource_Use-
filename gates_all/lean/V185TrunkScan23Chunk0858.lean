import V185TrunkScan23Chunk0857

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5077599 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5077599 : Nat := 118140960795 + 5077599 * 2 ^ 59
def prefixEnd_5077599 : Nat := 4983230072969 + 3 ^ 40 * 5077599 * 2
def baseEnd_5077599 : Nat := 2607248857788784604261053

theorem tailTrace_5077599 : CollatzResearch.WordTrace tailWord_5077599 prefixEnd_5077599 2607248857788784604261053 := by
  unfold tailWord_5077599
  simp only [CollatzResearch.WordTrace]
  refine ⟨185195249931733482714195851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123463499954488988476130567 185195249931733482714195851)
  ·
    refine ⟨277792874897600224071293777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185195249931733482714195851 277792874897600224071293777)
    ·
      refine ⟨208344656173200168053470333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277792874897600224071293777 208344656173200168053470333)
      ·
        refine ⟨78129246064950063020051375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208344656173200168053470333 78129246064950063020051375)
        ·
          refine ⟨117193869097425094530077063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78129246064950063020051375 117193869097425094530077063)
          ·
            refine ⟨175790803646137641795115595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117193869097425094530077063 175790803646137641795115595)
            ·
              refine ⟨263686205469206462692673393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175790803646137641795115595 263686205469206462692673393)
              ·
                refine ⟨197764654101904847019505045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263686205469206462692673393 197764654101904847019505045)
                ·
                  refine ⟨9270218161026789704039299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 197764654101904847019505045 9270218161026789704039299)
                  ·
                    refine ⟨13905327241540184556058949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9270218161026789704039299 13905327241540184556058949)
                    ·
                      refine ⟨2607248857788784604261053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13905327241540184556058949 2607248857788784604261053)
                      ·
                        rfl

theorem cell23_5077599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5077599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077599 prefixEnd_5077599 := by exact prefixLift 5077599
  have htrace : WordTrace (prefixWord ++ tailWord_5077599) baseStart_5077599 baseEnd_5077599 := by
    simpa [prefixWord, tailWord_5077599, baseEnd_5077599] using wordTrace_append hprefix tailTrace_5077599
  have hstable : (prefixWord ++ tailWord_5077599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077599).length < 2 ^ (prefixWord ++ tailWord_5077599).sum := by decide
  have hdescent : baseEnd_5077599 < baseStart_5077599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077619 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 3]
def baseStart_5077619 : Nat := 118140960795 + 5077619 * 2 ^ 59
def prefixEnd_5077619 : Nat := 4983230072969 + 3 ^ 40 * 5077619 * 2
def baseEnd_5077619 : Nat := 2607259127401874526010961

theorem tailTrace_5077619 : CollatzResearch.WordTrace tailWord_5077619 prefixEnd_5077619 2607259127401874526010961 := by
  unfold tailWord_5077619
  simp only [CollatzResearch.WordTrace]
  refine ⟨185195979391661026129923911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123463986261107350753282607 185195979391661026129923911)
  ·
    refine ⟨277793969087491539194885867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185195979391661026129923911 277793969087491539194885867)
    ·
      refine ⟨416690953631237308792328801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277793969087491539194885867 416690953631237308792328801)
      ·
        refine ⟨312518215223427981594246601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416690953631237308792328801 312518215223427981594246601)
        ·
          refine ⟨234388661417570986195684951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312518215223427981594246601 234388661417570986195684951)
          ·
            refine ⟨351582992126356479293527427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234388661417570986195684951 351582992126356479293527427)
            ·
              refine ⟨527374488189534718940291141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351582992126356479293527427 527374488189534718940291141)
              ·
                refine ⟨98882716535537759801304589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527374488189534718940291141 98882716535537759801304589)
                ·
                  refine ⟨37081018700826659925489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98882716535537759801304589 37081018700826659925489221)
                  ·
                    refine ⟨6952691006404998736029229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37081018700826659925489221 6952691006404998736029229)
                    ·
                      refine ⟨2607259127401874526010961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6952691006404998736029229 2607259127401874526010961)
                      ·
                        rfl

theorem cell23_5077619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_5077619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077619 prefixEnd_5077619 := by exact prefixLift 5077619
  have htrace : WordTrace (prefixWord ++ tailWord_5077619) baseStart_5077619 baseEnd_5077619 := by
    simpa [prefixWord, tailWord_5077619, baseEnd_5077619] using wordTrace_append hprefix tailTrace_5077619
  have hstable : (prefixWord ++ tailWord_5077619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077619).length < 2 ^ (prefixWord ++ tailWord_5077619).sum := by decide
  have hdescent : baseEnd_5077619 < baseStart_5077619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077677 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5077677 : Nat := 118140960795 + 5077677 * 2 ^ 59
def prefixEnd_5077677 : Nat := 4983230072969 + 3 ^ 40 * 5077677 * 2
def baseEnd_5077677 : Nat := 869096303093278433028565

theorem tailTrace_5077677 : CollatzResearch.WordTrace tailWord_5077677 prefixEnd_5077677 869096303093278433028565 := by
  unfold tailWord_5077677
  simp only [CollatzResearch.WordTrace]
  refine ⟨185198094825450902035535285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123465396550300601357023523 185198094825450902035535285)
  ·
    refine ⟨17362321389886022065831433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185198094825450902035535285 17362321389886022065831433)
    ·
      refine ⟨13021741042414516549373575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17362321389886022065831433 13021741042414516549373575)
      ·
        refine ⟨19532611563621774824060363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13021741042414516549373575 19532611563621774824060363)
        ·
          refine ⟨29298917345432662236090545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532611563621774824060363 29298917345432662236090545)
          ·
            refine ⟨21974188009074496677067909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29298917345432662236090545 21974188009074496677067909)
            ·
              refine ⟨4120160251701468126950233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21974188009074496677067909 4120160251701468126950233)
              ·
                refine ⟨3090120188776101095212675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4120160251701468126950233 3090120188776101095212675)
                ·
                  refine ⟨4635180283164151642819013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090120188776101095212675 4635180283164151642819013)
                  ·
                    refine ⟨869096303093278433028565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4635180283164151642819013 869096303093278433028565)
                    ·
                      rfl

theorem cell23_5077677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5077677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077677 prefixEnd_5077677 := by exact prefixLift 5077677
  have htrace : WordTrace (prefixWord ++ tailWord_5077677) baseStart_5077677 baseEnd_5077677 := by
    simpa [prefixWord, tailWord_5077677, baseEnd_5077677] using wordTrace_append hprefix tailTrace_5077677
  have hstable : (prefixWord ++ tailWord_5077677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077677).length < 2 ^ (prefixWord ++ tailWord_5077677).sum := by decide
  have hdescent : baseEnd_5077677 < baseStart_5077677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077700 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5077700 : Nat := 118140960795 + 5077700 * 2 ^ 59
def prefixEnd_5077700 : Nat := 4983230072969 + 3 ^ 40 * 5077700 * 2
def baseEnd_5077700 : Nat := 2607300719334888709098089

theorem tailTrace_5077700 : CollatzResearch.WordTrace tailWord_5077700 prefixEnd_5077700 2607300719334888709098089 := by
  unfold tailWord_5077700
  simp only [CollatzResearch.WordTrace]
  refine ⟨92599466852183788481811277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123465955802911717975748369 92599466852183788481811277)
  ·
    refine ⟨34724800069568920680679229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92599466852183788481811277 34724800069568920680679229)
    ·
      refine ⟨13021800026088345255254711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34724800069568920680679229 13021800026088345255254711)
      ·
        refine ⟨19532700039132517882882067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13021800026088345255254711 19532700039132517882882067)
        ·
          refine ⟨29299050058698776824323101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532700039132517882882067 29299050058698776824323101)
          ·
            refine ⟨10987143772012041309121163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29299050058698776824323101 10987143772012041309121163)
            ·
              refine ⟨16480715658018061963681745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10987143772012041309121163 16480715658018061963681745)
              ·
                refine ⟨12360536743513546472761309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16480715658018061963681745 12360536743513546472761309)
                ·
                  refine ⟨4635201278817579927285491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12360536743513546472761309 4635201278817579927285491)
                  ·
                    refine ⟨6952801918226369890928237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4635201278817579927285491 6952801918226369890928237)
                    ·
                      refine ⟨2607300719334888709098089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6952801918226369890928237 2607300719334888709098089)
                      ·
                        rfl

theorem cell23_5077700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5077700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077700 prefixEnd_5077700 := by exact prefixLift 5077700
  have htrace : WordTrace (prefixWord ++ tailWord_5077700) baseStart_5077700 baseEnd_5077700 := by
    simpa [prefixWord, tailWord_5077700, baseEnd_5077700] using wordTrace_append hprefix tailTrace_5077700
  have hstable : (prefixWord ++ tailWord_5077700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077700).length < 2 ^ (prefixWord ++ tailWord_5077700).sum := by decide
  have hdescent : baseEnd_5077700 < baseStart_5077700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077710 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_5077710 : Nat := 118140960795 + 5077710 * 2 ^ 59
def prefixEnd_5077710 : Nat := 4983230072969 + 3 ^ 40 * 5077710 * 2
def baseEnd_5077710 : Nat := 2607305854141433669973043

theorem tailTrace_5077710 : CollatzResearch.WordTrace tailWord_5077710 prefixEnd_5077710 2607305854141433669973043 := by
  unfold tailWord_5077710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23149912304291418583935823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123466198956220899114324389 23149912304291418583935823)
  ·
    refine ⟨34724868456437127875903735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23149912304291418583935823 34724868456437127875903735)
    ·
      refine ⟨52087302684655691813855603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34724868456437127875903735 52087302684655691813855603)
      ·
        refine ⟨78130954026983537720783405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52087302684655691813855603 78130954026983537720783405)
        ·
          refine ⟨29299107760118826645293777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78130954026983537720783405 29299107760118826645293777)
          ·
            refine ⟨21974330820089119983970333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29299107760118826645293777 21974330820089119983970333)
            ·
              refine ⟨8240374057533419993988875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21974330820089119983970333 8240374057533419993988875)
              ·
                refine ⟨12360561086300129990983313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8240374057533419993988875 12360561086300129990983313)
                ·
                  refine ⟨9270420814725097493237485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12360561086300129990983313 9270420814725097493237485)
                  ·
                    refine ⟨3476407805521911559964057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9270420814725097493237485 3476407805521911559964057)
                    ·
                      refine ⟨2607305854141433669973043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476407805521911559964057 2607305854141433669973043)
                      ·
                        rfl

theorem cell23_5077710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_5077710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077710 prefixEnd_5077710 := by exact prefixLift 5077710
  have htrace : WordTrace (prefixWord ++ tailWord_5077710) baseStart_5077710 baseEnd_5077710 := by
    simpa [prefixWord, tailWord_5077710, baseEnd_5077710] using wordTrace_append hprefix tailTrace_5077710
  have hstable : (prefixWord ++ tailWord_5077710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077710).length < 2 ^ (prefixWord ++ tailWord_5077710).sum := by decide
  have hdescent : baseEnd_5077710 < baseStart_5077710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077720 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 1, 5]
def baseStart_5077720 : Nat := 118140960795 + 5077720 * 2 ^ 59
def prefixEnd_5077720 : Nat := 4983230072969 + 3 ^ 40 * 5077720 * 2
def baseEnd_5077720 : Nat := 869103662982659543615999

theorem tailTrace_5077720 : CollatzResearch.WordTrace tailWord_5077720 prefixEnd_5077720 869103662982659543615999 := by
  unfold tailWord_5077720
  simp only [CollatzResearch.WordTrace]
  refine ⟨92599831582147560189675307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123466442109530080252900409 92599831582147560189675307)
  ·
    refine ⟨138899747373221340284512961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92599831582147560189675307 138899747373221340284512961)
    ·
      refine ⟨104174810529916005213384721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138899747373221340284512961 104174810529916005213384721)
      ·
        refine ⟨78131107897437003910038541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104174810529916005213384721 78131107897437003910038541)
        ·
          refine ⟨29299165461538876466264453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78131107897437003910038541 29299165461538876466264453)
          ·
            refine ⟨5493593524038539337424585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29299165461538876466264453 5493593524038539337424585)
            ·
              refine ⟨4120195143028904503068439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5493593524038539337424585 4120195143028904503068439)
              ·
                refine ⟨6180292714543356754602659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120195143028904503068439 6180292714543356754602659)
                ·
                  refine ⟨9270439071815035131903989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180292714543356754602659 9270439071815035131903989)
                  ·
                    refine ⟨869103662982659543615999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9270439071815035131903989 869103662982659543615999)
                    ·
                      rfl

theorem cell23_5077720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_5077720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077720 prefixEnd_5077720 := by exact prefixLift 5077720
  have htrace : WordTrace (prefixWord ++ tailWord_5077720) baseStart_5077720 baseEnd_5077720 := by
    simpa [prefixWord, tailWord_5077720, baseEnd_5077720] using wordTrace_append hprefix tailTrace_5077720
  have hstable : (prefixWord ++ tailWord_5077720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077720).length < 2 ^ (prefixWord ++ tailWord_5077720).sum := by decide
  have hdescent : baseEnd_5077720 < baseStart_5077720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077733 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_5077733 : Nat := 118140960795 + 5077733 * 2 ^ 59
def prefixEnd_5077733 : Nat := 4983230072969 + 3 ^ 40 * 5077733 * 2
def baseEnd_5077733 : Nat := 869105888065495693328479

theorem tailTrace_5077733 : CollatzResearch.WordTrace tailWord_5077733 prefixEnd_5077733 869105888065495693328479 := by
  unfold tailWord_5077733
  simp only [CollatzResearch.WordTrace]
  refine ⟨185200137313248023599573853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123466758208832015733049235 185200137313248023599573853)
  ·
    refine ⟨69450051492468008849840195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185200137313248023599573853 69450051492468008849840195)
    ·
      refine ⟨104175077238702013274760293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69450051492468008849840195 104175077238702013274760293)
      ·
        refine ⟨19532826982256627489017555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104175077238702013274760293 19532826982256627489017555)
        ·
          refine ⟨29299240473384941233526333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532826982256627489017555 29299240473384941233526333)
          ·
            refine ⟨10987215177519352962572375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29299240473384941233526333 10987215177519352962572375)
            ·
              refine ⟨16480822766279029443858563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10987215177519352962572375 16480822766279029443858563)
              ·
                refine ⟨24721234149418544165787845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16480822766279029443858563 24721234149418544165787845)
                ·
                  refine ⟨4635231403015977031085221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24721234149418544165787845 4635231403015977031085221)
                  ·
                    refine ⟨869105888065495693328479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4635231403015977031085221 869105888065495693328479)
                    ·
                      rfl

theorem cell23_5077733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_5077733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077733 prefixEnd_5077733 := by exact prefixLift 5077733
  have htrace : WordTrace (prefixWord ++ tailWord_5077733) baseStart_5077733 baseEnd_5077733 := by
    simpa [prefixWord, tailWord_5077733, baseEnd_5077733] using wordTrace_append hprefix tailTrace_5077733
  have hstable : (prefixWord ++ tailWord_5077733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077733).length < 2 ^ (prefixWord ++ tailWord_5077733).sum := by decide
  have hdescent : baseEnd_5077733 < baseStart_5077733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077739 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_5077739 : Nat := 118140960795 + 5077739 * 2 ^ 59
def prefixEnd_5077739 : Nat := 4983230072969 + 3 ^ 40 * 5077739 * 2
def baseEnd_5077739 : Nat := 2607320745080414056510409

theorem tailTrace_5077739 : CollatzResearch.WordTrace tailWord_5077739 prefixEnd_5077739 2607320745080414056510409 := by
  unfold tailWord_5077739
  simp only [CollatzResearch.WordTrace]
  refine ⟨185200356151226286624292271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123466904100817524416194847 185200356151226286624292271)
  ·
    refine ⟨277800534226839429936438407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185200356151226286624292271 277800534226839429936438407)
    ·
      refine ⟨416700801340259144904657611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277800534226839429936438407 416700801340259144904657611)
      ·
        refine ⟨625051202010388717356986417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416700801340259144904657611 625051202010388717356986417)
        ·
          refine ⟨468788401507791538017739813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625051202010388717356986417 468788401507791538017739813)
          ·
            refine ⟨87897825282710913378326215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 468788401507791538017739813 87897825282710913378326215)
            ·
              refine ⟨131846737924066370067489323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87897825282710913378326215 131846737924066370067489323)
              ·
                refine ⟨197770106886099555101233985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131846737924066370067489323 197770106886099555101233985)
                ·
                  refine ⟨148327580164574666325925489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197770106886099555101233985 148327580164574666325925489)
                  ·
                    refine ⟨111245685123430999744444117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148327580164574666325925489 111245685123430999744444117)
                    ·
                      refine ⟨2607320745080414056510409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111245685123430999744444117 2607320745080414056510409)
                      ·
                        rfl

theorem cell23_5077739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_5077739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077739 prefixEnd_5077739 := by exact prefixLift 5077739
  have htrace : WordTrace (prefixWord ++ tailWord_5077739) baseStart_5077739 baseEnd_5077739 := by
    simpa [prefixWord, tailWord_5077739, baseEnd_5077739] using wordTrace_append hprefix tailTrace_5077739
  have hstable : (prefixWord ++ tailWord_5077739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077739).length < 2 ^ (prefixWord ++ tailWord_5077739).sum := by decide
  have hdescent : baseEnd_5077739 < baseStart_5077739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077786 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_5077786 : Nat := 118140960795 + 5077786 * 2 ^ 59
def prefixEnd_5077786 : Nat := 4983230072969 + 3 ^ 40 * 5077786 * 2
def baseEnd_5077786 : Nat := 2607344878671175372622693

theorem tailTrace_5077786 : CollatzResearch.WordTrace tailWord_5077786 prefixEnd_5077786 2607344878671175372622693 := by
  unfold tailWord_5077786
  simp only [CollatzResearch.WordTrace]
  refine ⟨46300517595514003412813303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123468046921370675767502141 46300517595514003412813303)
  ·
    refine ⟨69450776393271005119219955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46300517595514003412813303 69450776393271005119219955)
    ·
      refine ⟨104176164589906507678829933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69450776393271005119219955 104176164589906507678829933)
      ·
        refine ⟨39066061721214940379561225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104176164589906507678829933 39066061721214940379561225)
        ·
          refine ⟨29299546290911205284670919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39066061721214940379561225 29299546290911205284670919)
          ·
            refine ⟨43949319436366807927006379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29299546290911205284670919 43949319436366807927006379)
            ·
              refine ⟨65923979154550211890509569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43949319436366807927006379 65923979154550211890509569)
              ·
                refine ⟨49442984365912658917882177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65923979154550211890509569 49442984365912658917882177)
                ·
                  refine ⟨37082238274434494188411633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49442984365912658917882177 37082238274434494188411633)
                  ·
                    refine ⟨27811678705825870641308725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37082238274434494188411633 27811678705825870641308725)
                    ·
                      refine ⟨2607344878671175372622693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27811678705825870641308725 2607344878671175372622693)
                      ·
                        rfl

theorem cell23_5077786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_5077786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077786 prefixEnd_5077786 := by exact prefixLift 5077786
  have htrace : WordTrace (prefixWord ++ tailWord_5077786) baseStart_5077786 baseEnd_5077786 := by
    simpa [prefixWord, tailWord_5077786, baseEnd_5077786] using wordTrace_append hprefix tailTrace_5077786
  have hstable : (prefixWord ++ tailWord_5077786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077786).length < 2 ^ (prefixWord ++ tailWord_5077786).sum := by decide
  have hdescent : baseEnd_5077786 < baseStart_5077786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077800 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_5077800 : Nat := 118140960795 + 5077800 * 2 ^ 59
def prefixEnd_5077800 : Nat := 4983230072969 + 3 ^ 40 * 5077800 * 2
def baseEnd_5077800 : Nat := 2607352067400338317847629

theorem tailTrace_5077800 : CollatzResearch.WordTrace tailWord_5077800 prefixEnd_5077800 2607352067400338317847629 := by
  unfold tailWord_5077800
  simp only [CollatzResearch.WordTrace]
  refine ⟨92601290502002647021131427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123468387336003529361508569 92601290502002647021131427)
  ·
    refine ⟨138901935753003970531697141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92601290502002647021131427 138901935753003970531697141)
    ·
      refine ⟨13022056476844122237346607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138901935753003970531697141 13022056476844122237346607)
      ·
        refine ⟨19533084715266183356019911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13022056476844122237346607 19533084715266183356019911)
        ·
          refine ⟨29299627072899275034029867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19533084715266183356019911 29299627072899275034029867)
          ·
            refine ⟨43949440609348912551044801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29299627072899275034029867 43949440609348912551044801)
            ·
              refine ⟨32962080457011684413283601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43949440609348912551044801 32962080457011684413283601)
              ·
                refine ⟨24721560342758763309962701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32962080457011684413283601 24721560342758763309962701)
                ·
                  refine ⟨9270585128534536241236013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24721560342758763309962701 9270585128534536241236013)
                  ·
                    refine ⟨3476469423200451090463505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9270585128534536241236013 3476469423200451090463505)
                    ·
                      refine ⟨2607352067400338317847629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476469423200451090463505 2607352067400338317847629)
                      ·
                        rfl

theorem cell23_5077800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_5077800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077800 prefixEnd_5077800 := by exact prefixLift 5077800
  have htrace : WordTrace (prefixWord ++ tailWord_5077800) baseStart_5077800 baseEnd_5077800 := by
    simpa [prefixWord, tailWord_5077800, baseEnd_5077800] using wordTrace_append hprefix tailTrace_5077800
  have hstable : (prefixWord ++ tailWord_5077800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077800).length < 2 ^ (prefixWord ++ tailWord_5077800).sum := by decide
  have hdescent : baseEnd_5077800 < baseStart_5077800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077816 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_5077816 : Nat := 118140960795 + 5077816 * 2 ^ 59
def prefixEnd_5077816 : Nat := 4983230072969 + 3 ^ 40 * 5077816 * 2
def baseEnd_5077816 : Nat := 2607360283090810255247555

theorem tailTrace_5077816 : CollatzResearch.WordTrace tailWord_5077816 prefixEnd_5077816 2607360283090810255247555 := by
  unfold tailWord_5077816
  simp only [CollatzResearch.WordTrace]
  refine ⟨92601582285973664387422651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123468776381298219183230201 92601582285973664387422651)
  ·
    refine ⟨138902373428960496581133977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92601582285973664387422651 138902373428960496581133977)
    ·
      refine ⟨104176780071720372435850483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138902373428960496581133977 104176780071720372435850483)
      ·
        refine ⟨156265170107580558653775725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104176780071720372435850483 156265170107580558653775725)
        ·
          refine ⟨58599438790342709495165897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156265170107580558653775725 58599438790342709495165897)
          ·
            refine ⟨43949579092757032121374423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58599438790342709495165897 43949579092757032121374423)
            ·
              refine ⟨65924368639135548182061635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43949579092757032121374423 65924368639135548182061635)
              ·
                refine ⟨98886552958703322273092453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65924368639135548182061635 98886552958703322273092453)
                ·
                  refine ⟨18541228679756872926204835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98886552958703322273092453 18541228679756872926204835)
                  ·
                    refine ⟨27811843019635309389307253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18541228679756872926204835 27811843019635309389307253)
                    ·
                      refine ⟨2607360283090810255247555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27811843019635309389307253 2607360283090810255247555)
                      ·
                        rfl

theorem cell23_5077816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_5077816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077816 prefixEnd_5077816 := by exact prefixLift 5077816
  have htrace : WordTrace (prefixWord ++ tailWord_5077816) baseStart_5077816 baseEnd_5077816 := by
    simpa [prefixWord, tailWord_5077816, baseEnd_5077816] using wordTrace_append hprefix tailTrace_5077816
  have hstable : (prefixWord ++ tailWord_5077816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077816).length < 2 ^ (prefixWord ++ tailWord_5077816).sum := by decide
  have hdescent : baseEnd_5077816 < baseStart_5077816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077847 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 2, 2, 2]
def baseStart_5077847 : Nat := 118140960795 + 5077847 * 2 ^ 59
def prefixEnd_5077847 : Nat := 4983230072969 + 3 ^ 40 * 5077847 * 2
def baseEnd_5077847 : Nat := 2607376200991099633959913

theorem tailTrace_5077847 : CollatzResearch.WordTrace tailWord_5077847 prefixEnd_5077847 2607376200991099633959913 := by
  unfold tailWord_5077847
  simp only [CollatzResearch.WordTrace]
  refine ⟨185204295234835021069223795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123469530156556680712815863 185204295234835021069223795)
  ·
    refine ⟨277806442852252531603835693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185204295234835021069223795 277806442852252531603835693)
    ·
      refine ⟨104177416069594699351438385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277806442852252531603835693 104177416069594699351438385)
      ·
        refine ⟨78133062052196024513578789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104177416069594699351438385 78133062052196024513578789)
        ·
          refine ⟨14649949134786754596296023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78133062052196024513578789 14649949134786754596296023)
          ·
            refine ⟨21974923702180131894444035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14649949134786754596296023 21974923702180131894444035)
            ·
              refine ⟨32962385553270197841666053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21974923702180131894444035 32962385553270197841666053)
              ·
                refine ⟨6180447291238162095312385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32962385553270197841666053 6180447291238162095312385)
                ·
                  refine ⟨4635335468428621571484289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6180447291238162095312385 4635335468428621571484289)
                  ·
                    refine ⟨3476501601321466178613217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4635335468428621571484289 3476501601321466178613217)
                    ·
                      refine ⟨2607376200991099633959913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476501601321466178613217 2607376200991099633959913)
                      ·
                        rfl

theorem cell23_5077847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_5077847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077847 prefixEnd_5077847 := by exact prefixLift 5077847
  have htrace : WordTrace (prefixWord ++ tailWord_5077847) baseStart_5077847 baseEnd_5077847 := by
    simpa [prefixWord, tailWord_5077847, baseEnd_5077847] using wordTrace_append hprefix tailTrace_5077847
  have hstable : (prefixWord ++ tailWord_5077847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077847).length < 2 ^ (prefixWord ++ tailWord_5077847).sum := by decide
  have hdescent : baseEnd_5077847 < baseStart_5077847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077863 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_5077863 : Nat := 118140960795 + 5077863 * 2 ^ 59
def prefixEnd_5077863 : Nat := 4983230072969 + 3 ^ 40 * 5077863 * 2
def baseEnd_5077863 : Nat := 2607384416681571571359839

theorem tailTrace_5077863 : CollatzResearch.WordTrace tailWord_5077863 prefixEnd_5077863 2607384416681571571359839 := by
  unfold tailWord_5077863
  simp only [CollatzResearch.WordTrace]
  refine ⟨185204878802777055801806243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123469919201851370534537495 185204878802777055801806243)
  ·
    refine ⟨277807318204165583702709365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185204878802777055801806243 277807318204165583702709365)
    ·
      refine ⟨26044436081640523472129003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277807318204165583702709365 26044436081640523472129003)
      ·
        refine ⟨39066654122460785208193505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26044436081640523472129003 39066654122460785208193505)
        ·
          refine ⟨29299990591845588906145129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39066654122460785208193505 29299990591845588906145129)
          ·
            refine ⟨21974992943884191679608847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29299990591845588906145129 21974992943884191679608847)
            ·
              refine ⟨32962489415826287519413271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21974992943884191679608847 32962489415826287519413271)
              ·
                refine ⟨49443734123739431279119907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32962489415826287519413271 49443734123739431279119907)
                ·
                  refine ⟨74165601185609146918679861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49443734123739431279119907 74165601185609146918679861)
                  ·
                    refine ⟨6953025111150857523626237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74165601185609146918679861 6953025111150857523626237)
                    ·
                      refine ⟨2607384416681571571359839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6953025111150857523626237 2607384416681571571359839)
                      ·
                        rfl

theorem cell23_5077863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_5077863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077863 prefixEnd_5077863 := by exact prefixLift 5077863
  have htrace : WordTrace (prefixWord ++ tailWord_5077863) baseStart_5077863 baseEnd_5077863 := by
    simpa [prefixWord, tailWord_5077863, baseEnd_5077863] using wordTrace_append hprefix tailTrace_5077863
  have hstable : (prefixWord ++ tailWord_5077863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077863).length < 2 ^ (prefixWord ++ tailWord_5077863).sum := by decide
  have hdescent : baseEnd_5077863 < baseStart_5077863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077870 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_5077870 : Nat := 118140960795 + 5077870 * 2 ^ 59
def prefixEnd_5077870 : Nat := 4983230072969 + 3 ^ 40 * 5077870 * 2
def baseEnd_5077870 : Nat := 289709779005128115996923

theorem tailTrace_5077870 : CollatzResearch.WordTrace tailWord_5077870 prefixEnd_5077870 289709779005128115996923 := by
  unfold tailWord_5077870
  simp only [CollatzResearch.WordTrace]
  refine ⟨23150641764218961999663883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123470089409167797331540709 23150641764218961999663883)
  ·
    refine ⟨34725962646328442999495825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23150641764218961999663883 34725962646328442999495825)
    ·
      refine ⟨26044471984746332249621869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34725962646328442999495825 26044471984746332249621869)
      ·
        refine ⟨9766676994279874593608201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26044471984746332249621869 9766676994279874593608201)
        ·
          refine ⟨7325007745709905945206151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9766676994279874593608201 7325007745709905945206151)
          ·
            refine ⟨10987511618564858917809227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325007745709905945206151 10987511618564858917809227)
            ·
              refine ⟨16481267427847288376713841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10987511618564858917809227 16481267427847288376713841)
              ·
                refine ⟨12360950570885466282535381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16481267427847288376713841 12360950570885466282535381)
                ·
                  refine ⟨289709779005128115996923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12360950570885466282535381 289709779005128115996923)
                  ·
                    rfl

theorem cell23_5077870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_5077870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077870 prefixEnd_5077870 := by exact prefixLift 5077870
  have htrace : WordTrace (prefixWord ++ tailWord_5077870) baseStart_5077870 baseEnd_5077870 := by
    simpa [prefixWord, tailWord_5077870, baseEnd_5077870] using wordTrace_append hprefix tailTrace_5077870
  have hstable : (prefixWord ++ tailWord_5077870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077870).length < 2 ^ (prefixWord ++ tailWord_5077870).sum := by decide
  have hdescent : baseEnd_5077870 < baseStart_5077870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077883 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 2, 5]
def baseStart_5077883 : Nat := 118140960795 + 5077883 * 2 ^ 59
def prefixEnd_5077883 : Nat := 4983230072969 + 3 ^ 40 * 5077883 * 2
def baseEnd_5077883 : Nat := 869131562098220497703249

theorem tailTrace_5077883 : CollatzResearch.WordTrace tailWord_5077883 prefixEnd_5077883 869131562098220497703249 := by
  unfold tailWord_5077883
  simp only [CollatzResearch.WordTrace]
  refine ⟨185205608262704599217534303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123470405508469732811689535 185205608262704599217534303)
  ·
    refine ⟨277808412394056898826301455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185205608262704599217534303 277808412394056898826301455)
    ·
      refine ⟨416712618591085348239452183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277808412394056898826301455 416712618591085348239452183)
      ·
        refine ⟨625068927886628022359178275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416712618591085348239452183 625068927886628022359178275)
        ·
          refine ⟨937603391829942033538767413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625068927886628022359178275 937603391829942033538767413)
          ·
            refine ⟨87900317984057065644259445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 937603391829942033538767413 87900317984057065644259445)
            ·
              refine ⟨8240654811005349904149323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87900317984057065644259445 8240654811005349904149323)
              ·
                refine ⟨12360982216508024856223985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8240654811005349904149323 12360982216508024856223985)
                ·
                  refine ⟨9270736662381018642167989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12360982216508024856223985 9270736662381018642167989)
                  ·
                    refine ⟨869131562098220497703249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9270736662381018642167989 869131562098220497703249)
                    ·
                      rfl

theorem cell23_5077883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 5].length) (baseStart_5077883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077883 prefixEnd_5077883 := by exact prefixLift 5077883
  have htrace : WordTrace (prefixWord ++ tailWord_5077883) baseStart_5077883 baseEnd_5077883 := by
    simpa [prefixWord, tailWord_5077883, baseEnd_5077883] using wordTrace_append hprefix tailTrace_5077883
  have hstable : (prefixWord ++ tailWord_5077883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077883).length < 2 ^ (prefixWord ++ tailWord_5077883).sum := by decide
  have hdescent : baseEnd_5077883 < baseStart_5077883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077903 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 10, 2]
def baseStart_5077903 : Nat := 118140960795 + 5077903 * 2 ^ 59
def prefixEnd_5077903 : Nat := 4983230072969 + 3 ^ 40 * 5077903 * 2
def baseEnd_5077903 : Nat := 2607404955907751414859655

theorem tailTrace_5077903 : CollatzResearch.WordTrace tailWord_5077903 prefixEnd_5077903 2607404955907751414859655 := by
  unfold tailWord_5077903
  simp only [CollatzResearch.WordTrace]
  refine ⟨185206337722632142633262363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123470891815088095088841575 185206337722632142633262363)
  ·
    refine ⟨277809506583948213949893545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185206337722632142633262363 277809506583948213949893545)
    ·
      refine ⟨208357129937961160462420159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277809506583948213949893545 208357129937961160462420159)
      ·
        refine ⟨312535694906941740693630239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208357129937961160462420159 312535694906941740693630239)
        ·
          refine ⟨468803542360412611040445359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312535694906941740693630239 468803542360412611040445359)
          ·
            refine ⟨703205313540618916560668039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468803542360412611040445359 703205313540618916560668039)
            ·
              refine ⟨1054807970310928374841002059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703205313540618916560668039 1054807970310928374841002059)
              ·
                refine ⟨1582211955466392562261503089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054807970310928374841002059 1582211955466392562261503089)
                ·
                  refine ⟨1186658966599794421696127317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582211955466392562261503089 1186658966599794421696127317)
                  ·
                    refine ⟨3476539941210335219812873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1186658966599794421696127317 3476539941210335219812873)
                    ·
                      refine ⟨2607404955907751414859655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476539941210335219812873 2607404955907751414859655)
                      ·
                        rfl

theorem cell23_5077903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10, 2].length) (baseStart_5077903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077903 prefixEnd_5077903 := by exact prefixLift 5077903
  have htrace : WordTrace (prefixWord ++ tailWord_5077903) baseStart_5077903 baseEnd_5077903 := by
    simpa [prefixWord, tailWord_5077903, baseEnd_5077903] using wordTrace_append hprefix tailTrace_5077903
  have hstable : (prefixWord ++ tailWord_5077903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077903).length < 2 ^ (prefixWord ++ tailWord_5077903).sum := by decide
  have hdescent : baseEnd_5077903 < baseStart_5077903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077920 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 2, 4, 2]
def baseStart_5077920 : Nat := 118140960795 + 5077920 * 2 ^ 59
def prefixEnd_5077920 : Nat := 4983230072969 + 3 ^ 40 * 5077920 * 2
def baseEnd_5077920 : Nat := 2607413685078877848347077

theorem tailTrace_5077920 : CollatzResearch.WordTrace tailWord_5077920 prefixEnd_5077920 2607413685078877848347077 := by
  unfold tailWord_5077920
  simp only [CollatzResearch.WordTrace]
  refine ⟨92603478881785277268315607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123471305175713703024420809 92603478881785277268315607)
  ·
    refine ⟨138905218322677915902473411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92603478881785277268315607 138905218322677915902473411)
    ·
      refine ⟨208357827484016873853710117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138905218322677915902473411 208357827484016873853710117)
      ·
        refine ⟨39067092653253163847570647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208357827484016873853710117 39067092653253163847570647)
        ·
          refine ⟨58600638979879745771355971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39067092653253163847570647 58600638979879745771355971)
          ·
            refine ⟨87900958469819618657033957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58600638979879745771355971 87900958469819618657033957)
            ·
              refine ⟨16481429713091178498193867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87900958469819618657033957 16481429713091178498193867)
              ·
                refine ⟨24722144569636767747290801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16481429713091178498193867 24722144569636767747290801)
                ·
                  refine ⟨18541608427227575810468101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24722144569636767747290801 18541608427227575810468101)
                  ·
                    refine ⟨3476551580105170464462769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18541608427227575810468101 3476551580105170464462769)
                    ·
                      refine ⟨2607413685078877848347077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476551580105170464462769 2607413685078877848347077)
                      ·
                        rfl

theorem cell23_5077920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_5077920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077920 prefixEnd_5077920 := by exact prefixLift 5077920
  have htrace : WordTrace (prefixWord ++ tailWord_5077920) baseStart_5077920 baseEnd_5077920 := by
    simpa [prefixWord, tailWord_5077920, baseEnd_5077920] using wordTrace_append hprefix tailTrace_5077920
  have hstable : (prefixWord ++ tailWord_5077920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077920).length < 2 ^ (prefixWord ++ tailWord_5077920).sum := by decide
  have hdescent : baseEnd_5077920 < baseStart_5077920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077923 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 3]
def baseStart_5077923 : Nat := 118140960795 + 5077923 * 2 ^ 59
def prefixEnd_5077923 : Nat := 4983230072969 + 3 ^ 40 * 5077923 * 2
def baseEnd_5077923 : Nat := 2607415225520841336609563

theorem tailTrace_5077923 : CollatzResearch.WordTrace tailWord_5077923 prefixEnd_5077923 2607415225520841336609563 := by
  unfold tailWord_5077923
  simp only [CollatzResearch.WordTrace]
  refine ⟨185207067182559686048990423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123471378121706457365993615 185207067182559686048990423)
  ·
    refine ⟨277810600773839529073485635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185207067182559686048990423 277810600773839529073485635)
    ·
      refine ⟨416715901160759293610228453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277810600773839529073485635 416715901160759293610228453)
      ·
        refine ⟨78134231467642367551917835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416715901160759293610228453 78134231467642367551917835)
        ·
          refine ⟨117201347201463551327876753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78134231467642367551917835 117201347201463551327876753)
          ·
            refine ⟨87901010401097663495907565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117201347201463551327876753 87901010401097663495907565)
            ·
              refine ⟨32962878900411623810965337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87901010401097663495907565 32962878900411623810965337)
              ·
                refine ⟨24722159175308717858224003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32962878900411623810965337 24722159175308717858224003)
                ·
                  refine ⟨37083238762963076787336005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24722159175308717858224003 37083238762963076787336005)
                  ·
                    refine ⟨6953107268055576897625501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37083238762963076787336005 6953107268055576897625501)
                    ·
                      refine ⟨2607415225520841336609563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6953107268055576897625501 2607415225520841336609563)
                      ·
                        rfl

theorem cell23_5077923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_5077923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077923 prefixEnd_5077923 := by exact prefixLift 5077923
  have htrace : WordTrace (prefixWord ++ tailWord_5077923) baseStart_5077923 baseEnd_5077923 := by
    simpa [prefixWord, tailWord_5077923, baseEnd_5077923] using wordTrace_append hprefix tailTrace_5077923
  have hstable : (prefixWord ++ tailWord_5077923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077923).length < 2 ^ (prefixWord ++ tailWord_5077923).sum := by decide
  have hdescent : baseEnd_5077923 < baseStart_5077923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077936 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_5077936 : Nat := 118140960795 + 5077936 * 2 ^ 59
def prefixEnd_5077936 : Nat := 4983230072969 + 3 ^ 40 * 5077936 * 2
def baseEnd_5077936 : Nat := 2607421900769349785747003

theorem tailTrace_5077936 : CollatzResearch.WordTrace tailWord_5077936 prefixEnd_5077936 2607421900769349785747003 := by
  unfold tailWord_5077936
  simp only [CollatzResearch.WordTrace]
  refine ⟨92603770665756294634606831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123471694221008392846142441 92603770665756294634606831)
  ·
    refine ⟨138905655998634441951910247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92603770665756294634606831 138905655998634441951910247)
    ·
      refine ⟨208358483997951662927865371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138905655998634441951910247 208358483997951662927865371)
      ·
        refine ⟨312537725996927494391798057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208358483997951662927865371 312537725996927494391798057)
        ·
          refine ⟨234403294497695620793848543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312537725996927494391798057 234403294497695620793848543)
          ·
            refine ⟨351604941746543431190772815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234403294497695620793848543 351604941746543431190772815)
            ·
              refine ⟨527407412619815146786159223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351604941746543431190772815 527407412619815146786159223)
              ·
                refine ⟨791111118929722720179238835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527407412619815146786159223 791111118929722720179238835)
                ·
                  refine ⟨1186666678394584080268858253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791111118929722720179238835 1186666678394584080268858253)
                  ·
                    refine ⟨445000004397969030100821845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186666678394584080268858253 445000004397969030100821845)
                    ·
                      refine ⟨2607421900769349785747003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 445000004397969030100821845 2607421900769349785747003)
                      ·
                        rfl

theorem cell23_5077936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_5077936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077936 prefixEnd_5077936 := by exact prefixLift 5077936
  have htrace : WordTrace (prefixWord ++ tailWord_5077936) baseStart_5077936 baseEnd_5077936 := by
    simpa [prefixWord, tailWord_5077936, baseEnd_5077936] using wordTrace_append hprefix tailTrace_5077936
  have hstable : (prefixWord ++ tailWord_5077936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077936).length < 2 ^ (prefixWord ++ tailWord_5077936).sum := by decide
  have hdescent : baseEnd_5077936 < baseStart_5077936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077964 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_5077964 : Nat := 118140960795 + 5077964 * 2 ^ 59
def prefixEnd_5077964 : Nat := 4983230072969 + 3 ^ 40 * 5077964 * 2
def baseEnd_5077964 : Nat := 869145426075891892065625

theorem tailTrace_5077964 : CollatzResearch.WordTrace tailWord_5077964 prefixEnd_5077964 869145426075891892065625 := by
  unfold tailWord_5077964
  simp only [CollatzResearch.WordTrace]
  refine ⟨92604281287705575025616473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123472375050274100034155297 92604281287705575025616473)
  ·
    refine ⟨69453210965779181269212355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92604281287705575025616473 69453210965779181269212355)
    ·
      refine ⟨104179816448668771903818533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69453210965779181269212355 104179816448668771903818533)
      ·
        refine ⟨19533715584125394731965975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104179816448668771903818533 19533715584125394731965975)
        ·
          refine ⟨29300573376188092097948963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19533715584125394731965975 29300573376188092097948963)
          ·
            refine ⟨43950860064282138146923445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29300573376188092097948963 43950860064282138146923445)
            ·
              refine ⟨4120393131026450451274073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43950860064282138146923445 4120393131026450451274073)
              ·
                refine ⟨3090294848269837838455555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4120393131026450451274073 3090294848269837838455555)
                ·
                  refine ⟨4635442272404756757683333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090294848269837838455555 4635442272404756757683333)
                  ·
                    refine ⟨869145426075891892065625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4635442272404756757683333 869145426075891892065625)
                    ·
                      rfl

theorem cell23_5077964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_5077964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077964 prefixEnd_5077964 := by exact prefixLift 5077964
  have htrace : WordTrace (prefixWord ++ tailWord_5077964) baseStart_5077964 baseEnd_5077964 := by
    simpa [prefixWord, tailWord_5077964, baseEnd_5077964] using wordTrace_append hprefix tailTrace_5077964
  have hstable : (prefixWord ++ tailWord_5077964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077964).length < 2 ^ (prefixWord ++ tailWord_5077964).sum := by decide
  have hdescent : baseEnd_5077964 < baseStart_5077964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5077977 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 6]
def baseStart_5077977 : Nat := 118140960795 + 5077977 * 2 ^ 59
def prefixEnd_5077977 : Nat := 4983230072969 + 3 ^ 40 * 5077977 * 2
def baseEnd_5077977 : Nat := 289715883719576013926035

theorem tailTrace_5077977 : CollatzResearch.WordTrace tailWord_5077977 prefixEnd_5077977 289715883719576013926035 := by
  unfold tailWord_5077977
  simp only [CollatzResearch.WordTrace]
  refine ⟨185209036724364053271456185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123472691149576035514304123 185209036724364053271456185)
  ·
    refine ⟨138906777543273039953592139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185209036724364053271456185 138906777543273039953592139)
    ·
      refine ⟨208360166314909559930388209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138906777543273039953592139 208360166314909559930388209)
      ·
        refine ⟨156270124736182169947791157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208360166314909559930388209 156270124736182169947791157)
        ·
          refine ⟨14650324194017078432605421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156270124736182169947791157 14650324194017078432605421)
          ·
            refine ⟨5493871572756404412227033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14650324194017078432605421 5493871572756404412227033)
            ·
              refine ⟨4120403679567303309170275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5493871572756404412227033 4120403679567303309170275)
              ·
                refine ⟨6180605519350954963755413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120403679567303309170275 6180605519350954963755413)
                ·
                  refine ⟨289715883719576013926035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6180605519350954963755413 289715883719576013926035)
                  ·
                    rfl

theorem cell23_5077977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 6].length) (baseStart_5077977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5077977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5077977 prefixEnd_5077977 := by exact prefixLift 5077977
  have htrace : WordTrace (prefixWord ++ tailWord_5077977) baseStart_5077977 baseEnd_5077977 := by
    simpa [prefixWord, tailWord_5077977, baseEnd_5077977] using wordTrace_append hprefix tailTrace_5077977
  have hstable : (prefixWord ++ tailWord_5077977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5077977).length < 2 ^ (prefixWord ++ tailWord_5077977).sum := by decide
  have hdescent : baseEnd_5077977 < baseStart_5077977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5077977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078010 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_5078010 : Nat := 118140960795 + 5078010 * 2 ^ 59
def prefixEnd_5078010 : Nat := 4983230072969 + 3 ^ 40 * 5078010 * 2
def baseEnd_5078010 : Nat := 2607459898337782496221663

theorem tailTrace_5078010 : CollatzResearch.WordTrace tailWord_5078010 prefixEnd_5078010 2607459898337782496221663 := by
  unfold tailWord_5078010
  simp only [CollatzResearch.WordTrace]
  refine ⟨46302560083311124976851871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123473493555496333271604989 46302560083311124976851871)
  ·
    refine ⟨69453840124966687465277807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46302560083311124976851871 69453840124966687465277807)
    ·
      refine ⟨104180760187450031197916711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69453840124966687465277807 104180760187450031197916711)
      ·
        refine ⟨156271140281175046796875067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104180760187450031197916711 156271140281175046796875067)
        ·
          refine ⟨234406710421762570195312601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156271140281175046796875067 234406710421762570195312601)
          ·
            refine ⟨175805032816321927646484451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234406710421762570195312601 175805032816321927646484451)
            ·
              refine ⟨263707549224482891469726677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175805032816321927646484451 263707549224482891469726677)
              ·
                refine ⟨6180645684948817768821719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 263707549224482891469726677 6180645684948817768821719)
                ·
                  refine ⟨9270968527423226653232579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180645684948817768821719 9270968527423226653232579)
                  ·
                    refine ⟨13906452791134839979848869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9270968527423226653232579 13906452791134839979848869)
                    ·
                      refine ⟨2607459898337782496221663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13906452791134839979848869 2607459898337782496221663)
                      ·
                        rfl

theorem cell23_5078010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_5078010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078010 prefixEnd_5078010 := by exact prefixLift 5078010
  have htrace : WordTrace (prefixWord ++ tailWord_5078010) baseStart_5078010 baseEnd_5078010 := by
    simpa [prefixWord, tailWord_5078010, baseEnd_5078010] using wordTrace_append hprefix tailTrace_5078010
  have hstable : (prefixWord ++ tailWord_5078010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078010).length < 2 ^ (prefixWord ++ tailWord_5078010).sum := by decide
  have hdescent : baseEnd_5078010 < baseStart_5078010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078037 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_5078037 : Nat := 118140960795 + 5078037 * 2 ^ 59
def prefixEnd_5078037 : Nat := 4983230072969 + 3 ^ 40 * 5078037 * 2
def baseEnd_5078037 : Nat := 869157920771817963528013

theorem tailTrace_5078037 : CollatzResearch.WordTrace tailWord_5078037 prefixEnd_5078037 869157920771817963528013 := by
  unfold tailWord_5078037
  simp only [CollatzResearch.WordTrace]
  refine ⟨185211225104146683518640365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123474150069431122345760243 185211225104146683518640365)
  ·
    refine ⟨69454209414055006319490137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185211225104146683518640365 69454209414055006319490137)
    ·
      refine ⟨52090657060541254739617603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69454209414055006319490137 52090657060541254739617603)
      ·
        refine ⟨78135985590811882109426405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52090657060541254739617603 78135985590811882109426405)
        ·
          refine ⟨14650497298277227895517451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78135985590811882109426405 14650497298277227895517451)
          ·
            refine ⟨21975745947415841843276177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14650497298277227895517451 21975745947415841843276177)
            ·
              refine ⟨16481809460561881382457133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21975745947415841843276177 16481809460561881382457133)
              ·
                refine ⟨6180678547710705518421425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16481809460561881382457133 6180678547710705518421425)
                ·
                  refine ⟨4635508910783029138816069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6180678547710705518421425 4635508910783029138816069)
                  ·
                    refine ⟨869157920771817963528013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4635508910783029138816069 869157920771817963528013)
                    ·
                      rfl

theorem cell23_5078037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_5078037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078037 prefixEnd_5078037 := by exact prefixLift 5078037
  have htrace : WordTrace (prefixWord ++ tailWord_5078037) baseStart_5078037 baseEnd_5078037 := by
    simpa [prefixWord, tailWord_5078037, baseEnd_5078037] using wordTrace_append hprefix tailTrace_5078037
  have hstable : (prefixWord ++ tailWord_5078037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078037).length < 2 ^ (prefixWord ++ tailWord_5078037).sum := by decide
  have hdescent : baseEnd_5078037 < baseStart_5078037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078040 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5078040 : Nat := 118140960795 + 5078040 * 2 ^ 59
def prefixEnd_5078040 : Nat := 4983230072969 + 3 ^ 40 * 5078040 * 2
def baseEnd_5078040 : Nat := 2607475302757417378846525

theorem tailTrace_5078040 : CollatzResearch.WordTrace tailWord_5078040 prefixEnd_5078040 2607475302757417378846525 := by
  unfold tailWord_5078040
  simp only [CollatzResearch.WordTrace]
  refine ⟨92605667261567907515499787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123474223015423876687333049 92605667261567907515499787)
  ·
    refine ⟨138908500892351861273249681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92605667261567907515499787 138908500892351861273249681)
    ·
      refine ⟨104181375669263895954937261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138908500892351861273249681 104181375669263895954937261)
      ·
        refine ⟨39068015875973960983101473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104181375669263895954937261 39068015875973960983101473)
        ·
          refine ⟨29301011906980470737326105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39068015875973960983101473 29301011906980470737326105)
          ·
            refine ⟨21975758930235353052994579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29301011906980470737326105 21975758930235353052994579)
            ·
              refine ⟨32963638395353029579491869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21975758930235353052994579 32963638395353029579491869)
              ·
                refine ⟨12361364398257386092309451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32963638395353029579491869 12361364398257386092309451)
                ·
                  refine ⟨18542046597386079138464177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12361364398257386092309451 18542046597386079138464177)
                  ·
                    refine ⟨13906534948039559353848133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18542046597386079138464177 13906534948039559353848133)
                    ·
                      refine ⟨2607475302757417378846525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13906534948039559353848133 2607475302757417378846525)
                      ·
                        rfl

theorem cell23_5078040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5078040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078040 prefixEnd_5078040 := by exact prefixLift 5078040
  have htrace : WordTrace (prefixWord ++ tailWord_5078040) baseStart_5078040 baseEnd_5078040 := by
    simpa [prefixWord, tailWord_5078040, baseEnd_5078040] using wordTrace_append hprefix tailTrace_5078040
  have hstable : (prefixWord ++ tailWord_5078040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078040).length < 2 ^ (prefixWord ++ tailWord_5078040).sum := by decide
  have hdescent : baseEnd_5078040 < baseStart_5078040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078048 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5078048 : Nat := 118140960795 + 5078048 * 2 ^ 59
def prefixEnd_5078048 : Nat := 4983230072969 + 3 ^ 40 * 5078048 * 2
def baseEnd_5078048 : Nat := 2607479410602653347546489

theorem tailTrace_5078048 : CollatzResearch.WordTrace tailWord_5078048 prefixEnd_5078048 2607479410602653347546489 := by
  unfold tailWord_5078048
  simp only [CollatzResearch.WordTrace]
  refine ⟨92605813153553416198645399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123474417538071221598193865 92605813153553416198645399)
  ·
    refine ⟨138908719730330124297968099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92605813153553416198645399 138908719730330124297968099)
    ·
      refine ⟨208363079595495186446952149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138908719730330124297968099 208363079595495186446952149)
      ·
        refine ⟨4883509678019418432350441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 208363079595495186446952149 4883509678019418432350441)
        ·
          refine ⟨3662632258514563824262831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4883509678019418432350441 3662632258514563824262831)
          ·
            refine ⟨5493948387771845736394247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662632258514563824262831 5493948387771845736394247)
            ·
              refine ⟨8240922581657768604591371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5493948387771845736394247 8240922581657768604591371)
              ·
                refine ⟨12361383872486652906887057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8240922581657768604591371 12361383872486652906887057)
                ·
                  refine ⟨9271037904364989680165293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12361383872486652906887057 9271037904364989680165293)
                  ·
                    refine ⟨3476639214136871130061985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9271037904364989680165293 3476639214136871130061985)
                    ·
                      refine ⟨2607479410602653347546489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476639214136871130061985 2607479410602653347546489)
                      ·
                        rfl

theorem cell23_5078048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5078048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078048 prefixEnd_5078048 := by exact prefixLift 5078048
  have htrace : WordTrace (prefixWord ++ tailWord_5078048) baseStart_5078048 baseEnd_5078048 := by
    simpa [prefixWord, tailWord_5078048, baseEnd_5078048] using wordTrace_append hprefix tailTrace_5078048
  have hstable : (prefixWord ++ tailWord_5078048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078048).length < 2 ^ (prefixWord ++ tailWord_5078048).sum := by decide
  have hdescent : baseEnd_5078048 < baseStart_5078048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078060 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_5078060 : Nat := 118140960795 + 5078060 * 2 ^ 59
def prefixEnd_5078060 : Nat := 4983230072969 + 3 ^ 40 * 5078060 * 2
def baseEnd_5078060 : Nat := 2607485572370507300596433

theorem tailTrace_5078060 : CollatzResearch.WordTrace tailWord_5078060 prefixEnd_5078060 2607485572370507300596433 := by
  unfold tailWord_5078060
  simp only [CollatzResearch.WordTrace]
  refine ⟨92606031991531679223363817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123474709322042238964485089 92606031991531679223363817)
  ·
    refine ⟨69454523993648759417522863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92606031991531679223363817 69454523993648759417522863)
    ·
      refine ⟨104181785990473139126284295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69454523993648759417522863 104181785990473139126284295)
      ·
        refine ⟨156272678985709708689426443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104181785990473139126284295 156272678985709708689426443)
        ·
          refine ⟨234409018478564563034139665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156272678985709708689426443 234409018478564563034139665)
          ·
            refine ⟨175806763858923422275604749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234409018478564563034139665 175806763858923422275604749)
            ·
              refine ⟨65927536447096283353351781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175806763858923422275604749 65927536447096283353351781)
              ·
                refine ⟨12361413083830553128753459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65927536447096283353351781 12361413083830553128753459)
                ·
                  refine ⟨18542119625745829693130189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12361413083830553128753459 18542119625745829693130189)
                  ·
                    refine ⟨6953294859654686134923821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18542119625745829693130189 6953294859654686134923821)
                    ·
                      refine ⟨2607485572370507300596433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6953294859654686134923821 2607485572370507300596433)
                      ·
                        rfl

theorem cell23_5078060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_5078060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078060 prefixEnd_5078060 := by exact prefixLift 5078060
  have htrace : WordTrace (prefixWord ++ tailWord_5078060) baseStart_5078060 baseEnd_5078060 := by
    simpa [prefixWord, tailWord_5078060, baseEnd_5078060] using wordTrace_append hprefix tailTrace_5078060
  have hstable : (prefixWord ++ tailWord_5078060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078060).length < 2 ^ (prefixWord ++ tailWord_5078060).sum := by decide
  have hdescent : baseEnd_5078060 < baseStart_5078060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078078 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5078078 : Nat := 118140960795 + 5078078 * 2 ^ 59
def prefixEnd_5078078 : Nat := 4983230072969 + 3 ^ 40 * 5078078 * 2
def baseEnd_5078078 : Nat := 2607494815022288230171351

theorem tailTrace_5078078 : CollatzResearch.WordTrace tailWord_5078078 prefixEnd_5078078 2607494815022288230171351 := by
  unfold tailWord_5078078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23151590062124768440110361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123475146997998765013921925 23151590062124768440110361)
  ·
    refine ⟨17363692546593576330082771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23151590062124768440110361 17363692546593576330082771)
    ·
      refine ⟨26045538819890364495124157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17363692546593576330082771 26045538819890364495124157)
      ·
        refine ⟨9767077057458886685671559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26045538819890364495124157 9767077057458886685671559)
        ·
          refine ⟨14650615586188330028507339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767077057458886685671559 14650615586188330028507339)
          ·
            refine ⟨21975923379282495042761009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14650615586188330028507339 21975923379282495042761009)
            ·
              refine ⟨16481942534461871282070757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21975923379282495042761009 16481942534461871282070757)
              ·
                refine ⟨3090364225211600865388267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16481942534461871282070757 3090364225211600865388267)
                ·
                  refine ⟨4635546337817401298082401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090364225211600865388267 4635546337817401298082401)
                  ·
                    refine ⟨3476659753363050973561801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4635546337817401298082401 3476659753363050973561801)
                    ·
                      refine ⟨2607494815022288230171351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476659753363050973561801 2607494815022288230171351)
                      ·
                        rfl

theorem cell23_5078078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5078078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078078 prefixEnd_5078078 := by exact prefixLift 5078078
  have htrace : WordTrace (prefixWord ++ tailWord_5078078) baseStart_5078078 baseEnd_5078078 := by
    simpa [prefixWord, tailWord_5078078, baseEnd_5078078] using wordTrace_append hprefix tailTrace_5078078
  have hstable : (prefixWord ++ tailWord_5078078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078078).length < 2 ^ (prefixWord ++ tailWord_5078078).sum := by decide
  have hdescent : baseEnd_5078078 < baseStart_5078078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078100 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5078100 : Nat := 118140960795 + 5078100 * 2 ^ 59
def prefixEnd_5078100 : Nat := 4983230072969 + 3 ^ 40 * 5078100 * 2
def baseEnd_5078100 : Nat := 2607506111596687144096249

theorem tailTrace_5078100 : CollatzResearch.WordTrace tailWord_5078100 prefixEnd_5078100 2607506111596687144096249 := by
  unfold tailWord_5078100
  simp only [CollatzResearch.WordTrace]
  refine ⟨92606761451459222639091877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123475681935278963518789169 92606761451459222639091877)
  ·
    refine ⟨17363767772148604244829727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92606761451459222639091877 17363767772148604244829727)
    ·
      refine ⟨26045651658222906367244591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17363767772148604244829727 26045651658222906367244591)
      ·
        refine ⟨39068477487334359550866887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26045651658222906367244591 39068477487334359550866887)
        ·
          refine ⟨58602716231001539326300331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39068477487334359550866887 58602716231001539326300331)
          ·
            refine ⟨87904074346502308989450497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58602716231001539326300331 87904074346502308989450497)
            ·
              refine ⟨65928055759876731742087873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87904074346502308989450497 65928055759876731742087873)
              ·
                refine ⟨49446041819907548806565905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65928055759876731742087873 49446041819907548806565905)
                ·
                  refine ⟨37084531364930661604924429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49446041819907548806565905 37084531364930661604924429)
                  ·
                    refine ⟨13906699261848998101846661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37084531364930661604924429 13906699261848998101846661)
                    ·
                      refine ⟨2607506111596687144096249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13906699261848998101846661 2607506111596687144096249)
                      ·
                        rfl

theorem cell23_5078100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5078100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078100 prefixEnd_5078100 := by exact prefixLift 5078100
  have htrace : WordTrace (prefixWord ++ tailWord_5078100) baseStart_5078100 baseEnd_5078100 := by
    simpa [prefixWord, tailWord_5078100, baseEnd_5078100] using wordTrace_append hprefix tailTrace_5078100
  have hstable : (prefixWord ++ tailWord_5078100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078100).length < 2 ^ (prefixWord ++ tailWord_5078100).sum := by decide
  have hdescent : baseEnd_5078100 < baseStart_5078100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078104 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 1, 3, 2]
def baseStart_5078104 : Nat := 118140960795 + 5078104 * 2 ^ 59
def prefixEnd_5078104 : Nat := 4983230072969 + 3 ^ 40 * 5078104 * 2
def baseEnd_5078104 : Nat := 2607508165519305128446231

theorem tailTrace_5078104 : CollatzResearch.WordTrace tailWord_5078104 prefixEnd_5078104 2607508165519305128446231 := by
  unfold tailWord_5078104
  simp only [CollatzResearch.WordTrace]
  refine ⟨92606834397451976980664683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123475779196602635974219577 92606834397451976980664683)
  ·
    refine ⟨138910251596177965470997025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92606834397451976980664683 138910251596177965470997025)
    ·
      refine ⟨104182688697133474103247769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138910251596177965470997025 104182688697133474103247769)
      ·
        refine ⟨78137016522850105577435827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104182688697133474103247769 78137016522850105577435827)
        ·
          refine ⟨117205524784275158366153741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78137016522850105577435827 117205524784275158366153741)
          ·
            refine ⟨43952071794103184387307653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117205524784275158366153741 43952071794103184387307653)
            ·
              refine ⟨8241013461394347072620185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43952071794103184387307653 8241013461394347072620185)
              ·
                refine ⟨6180760096045760304465139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8241013461394347072620185 6180760096045760304465139)
                ·
                  refine ⟨9271140144068640456697709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180760096045760304465139 9271140144068640456697709)
                  ·
                    refine ⟨3476677554025740171261641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9271140144068640456697709 3476677554025740171261641)
                    ·
                      refine ⟨2607508165519305128446231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476677554025740171261641 2607508165519305128446231)
                      ·
                        rfl

theorem cell23_5078104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_5078104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078104 prefixEnd_5078104 := by exact prefixLift 5078104
  have htrace : WordTrace (prefixWord ++ tailWord_5078104) baseStart_5078104 baseEnd_5078104 := by
    simpa [prefixWord, tailWord_5078104, baseEnd_5078104] using wordTrace_append hprefix tailTrace_5078104
  have hstable : (prefixWord ++ tailWord_5078104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078104).length < 2 ^ (prefixWord ++ tailWord_5078104).sum := by decide
  have hdescent : baseEnd_5078104 < baseStart_5078104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078117 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 3, 4, 2]
def baseStart_5078117 : Nat := 118140960795 + 5078117 * 2 ^ 59
def prefixEnd_5078117 : Nat := 4983230072969 + 3 ^ 40 * 5078117 * 2
def baseEnd_5078117 : Nat := 2607514840767813577583671

theorem tailTrace_5078117 : CollatzResearch.WordTrace tailWord_5078117 prefixEnd_5078117 2607514840767813577583671 := by
  unfold tailWord_5078117
  simp only [CollatzResearch.WordTrace]
  refine ⟨185214142943856857181552605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123476095295904571454368403 185214142943856857181552605)
  ·
    refine ⟨69455303603946321443082227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185214142943856857181552605 69455303603946321443082227)
    ·
      refine ⟨104182955405919482164623341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69455303603946321443082227 104182955405919482164623341)
      ·
        refine ⟨39068608277219805811733753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104182955405919482164623341 39068608277219805811733753)
        ·
          refine ⟨29301456207914854358800315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39068608277219805811733753 29301456207914854358800315)
          ·
            refine ⟨43952184311872281538200473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29301456207914854358800315 43952184311872281538200473)
            ·
              refine ⟨32964138233904211153650355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43952184311872281538200473 32964138233904211153650355)
              ·
                refine ⟨49446207350856316730475533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32964138233904211153650355 49446207350856316730475533)
                ·
                  refine ⟨18542327756571118773928325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49446207350856316730475533 18542327756571118773928325)
                  ·
                    refine ⟨3476686454357084770111561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18542327756571118773928325 3476686454357084770111561)
                    ·
                      refine ⟨2607514840767813577583671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476686454357084770111561 2607514840767813577583671)
                      ·
                        rfl

theorem cell23_5078117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_5078117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078117 prefixEnd_5078117 := by exact prefixLift 5078117
  have htrace : WordTrace (prefixWord ++ tailWord_5078117) baseStart_5078117 baseEnd_5078117 := by
    simpa [prefixWord, tailWord_5078117, baseEnd_5078117] using wordTrace_append hprefix tailTrace_5078117
  have hstable : (prefixWord ++ tailWord_5078117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078117).length < 2 ^ (prefixWord ++ tailWord_5078117).sum := by decide
  have hdescent : baseEnd_5078117 < baseStart_5078117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078207 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 6, 2]
def baseStart_5078207 : Nat := 118140960795 + 5078207 * 2 ^ 59
def prefixEnd_5078207 : Nat := 4983230072969 + 3 ^ 40 * 5078207 * 2
def baseEnd_5078207 : Nat := 2607561054026718225458257

theorem tailTrace_5078207 : CollatzResearch.WordTrace tailWord_5078207 prefixEnd_5078207 2607561054026718225458257 := by
  unfold tailWord_5078207
  simp only [CollatzResearch.WordTrace]
  refine ⟨185217425513530802552328875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123478283675687201701552583 185217425513530802552328875)
  ·
    refine ⟨277826138270296203828493313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185217425513530802552328875 277826138270296203828493313)
    ·
      refine ⟨208369603702722152871369985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277826138270296203828493313 208369603702722152871369985)
      ·
        refine ⟨156277202777041614653527489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208369603702722152871369985 156277202777041614653527489)
        ·
          refine ⟨117207902082781210990145617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156277202777041614653527489 117207902082781210990145617)
          ·
            refine ⟨87905926562085908242609213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117207902082781210990145617 87905926562085908242609213)
            ·
              refine ⟨32964722460782215590978455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87905926562085908242609213 32964722460782215590978455)
              ·
                refine ⟨49447083691173323386467683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32964722460782215590978455 49447083691173323386467683)
                ·
                  refine ⟨74170625536759985079701525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49447083691173323386467683 74170625536759985079701525)
                  ·
                    refine ⟨3476748072035624300611009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74170625536759985079701525 3476748072035624300611009)
                    ·
                      refine ⟨2607561054026718225458257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476748072035624300611009 2607561054026718225458257)
                      ·
                        rfl

theorem cell23_5078207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_5078207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078207 prefixEnd_5078207 := by exact prefixLift 5078207
  have htrace : WordTrace (prefixWord ++ tailWord_5078207) baseStart_5078207 baseEnd_5078207 := by
    simpa [prefixWord, tailWord_5078207, baseEnd_5078207] using wordTrace_append hprefix tailTrace_5078207
  have hstable : (prefixWord ++ tailWord_5078207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078207).length < 2 ^ (prefixWord ++ tailWord_5078207).sum := by decide
  have hdescent : baseEnd_5078207 < baseStart_5078207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078221 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5078221 : Nat := 118140960795 + 5078221 * 2 ^ 59
def prefixEnd_5078221 : Nat := 4983230072969 + 3 ^ 40 * 5078221 * 2
def baseEnd_5078221 : Nat := 869189414251960390227731

theorem tailTrace_5078221 : CollatzResearch.WordTrace tailWord_5078221 prefixEnd_5078221 869189414251960390227731 := by
  unfold tailWord_5078221
  simp only [CollatzResearch.WordTrace]
  refine ⟨185217936135480082943338517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123478624090320055295559011 185217936135480082943338517)
  ·
    refine ⟨8682090756350628887968993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 185217936135480082943338517 8682090756350628887968993)
    ·
      refine ⟨6511568067262971665976745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8682090756350628887968993 6511568067262971665976745)
      ·
        refine ⟨4883676050447228749482559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511568067262971665976745 4883676050447228749482559)
        ·
          refine ⟨7325514075670843124223839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883676050447228749482559 7325514075670843124223839)
          ·
            refine ⟨10988271113506264686335759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325514075670843124223839 10988271113506264686335759)
            ·
              refine ⟨16482406670259397029503639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10988271113506264686335759 16482406670259397029503639)
              ·
                refine ⟨24723610005389095544255459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16482406670259397029503639 24723610005389095544255459)
                ·
                  refine ⟨37085415008083643316383189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24723610005389095544255459 37085415008083643316383189)
                  ·
                    refine ⟨869189414251960390227731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37085415008083643316383189 869189414251960390227731)
                    ·
                      rfl

theorem cell23_5078221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5078221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078221 prefixEnd_5078221 := by exact prefixLift 5078221
  have htrace : WordTrace (prefixWord ++ tailWord_5078221) baseStart_5078221 baseEnd_5078221 := by
    simpa [prefixWord, tailWord_5078221, baseEnd_5078221] using wordTrace_append hprefix tailTrace_5078221
  have hstable : (prefixWord ++ tailWord_5078221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078221).length < 2 ^ (prefixWord ++ tailWord_5078221).sum := by decide
  have hdescent : baseEnd_5078221 < baseStart_5078221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078284 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 1, 5, 2]
def baseStart_5078284 : Nat := 118140960795 + 5078284 * 2 ^ 59
def prefixEnd_5078284 : Nat := 4983230072969 + 3 ^ 40 * 5078284 * 2
def baseEnd_5078284 : Nat := 2607600592037114424195403

theorem tailTrace_5078284 : CollatzResearch.WordTrace tailWord_5078284 prefixEnd_5078284 2607600592037114424195403 := by
  unfold tailWord_5078284
  simp only [CollatzResearch.WordTrace]
  refine ⟨92610116967125922351440953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123480155956167896468587937 92610116967125922351440953)
  ·
    refine ⟨69457587725344441763580715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92610116967125922351440953 69457587725344441763580715)
    ·
      refine ⟨104186381588016662645371073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69457587725344441763580715 104186381588016662645371073)
      ·
        refine ⟨78139786191012496984028305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104186381588016662645371073 78139786191012496984028305)
        ·
          refine ⟨58604839643259372738021229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78139786191012496984028305 58604839643259372738021229)
          ·
            refine ⟨21976814866222264776757961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58604839643259372738021229 21976814866222264776757961)
            ·
              refine ⟨16482611149666698582568471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21976814866222264776757961 16482611149666698582568471)
              ·
                refine ⟨24723916724500047873852707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16482611149666698582568471 24723916724500047873852707)
                ·
                  refine ⟨37085875086750071810779061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24723916724500047873852707 37085875086750071810779061)
                  ·
                    refine ⟨3476800789382819232260537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37085875086750071810779061 3476800789382819232260537)
                    ·
                      refine ⟨2607600592037114424195403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476800789382819232260537 2607600592037114424195403)
                      ·
                        rfl

theorem cell23_5078284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_5078284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078284 prefixEnd_5078284 := by exact prefixLift 5078284
  have htrace : WordTrace (prefixWord ++ tailWord_5078284) baseStart_5078284 baseEnd_5078284 := by
    simpa [prefixWord, tailWord_5078284, baseEnd_5078284] using wordTrace_append hprefix tailTrace_5078284
  have hstable : (prefixWord ++ tailWord_5078284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078284).length < 2 ^ (prefixWord ++ tailWord_5078284).sum := by decide
  have hdescent : baseEnd_5078284 < baseStart_5078284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078301 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5078301 : Nat := 118140960795 + 5078301 * 2 ^ 59
def prefixEnd_5078301 : Nat := 4983230072969 + 3 ^ 40 * 5078301 * 2
def baseEnd_5078301 : Nat := 2607609321208240857682825

theorem tailTrace_5078301 : CollatzResearch.WordTrace tailWord_5078301 prefixEnd_5078301 2607609321208240857682825 := by
  unfold tailWord_5078301
  simp only [CollatzResearch.WordTrace]
  refine ⟨185220853975190256606250757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123480569316793504404167171 185220853975190256606250757)
  ·
    refine ⟨34728910120348173113672017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185220853975190256606250757 34728910120348173113672017)
    ·
      refine ⟨26046682590261129835254013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34728910120348173113672017 26046682590261129835254013)
      ·
        refine ⟨9767505971347923688220255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26046682590261129835254013 9767505971347923688220255)
        ·
          refine ⟨14651258957021885532330383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767505971347923688220255 14651258957021885532330383)
          ·
            refine ⟨21976888435532828298495575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14651258957021885532330383 21976888435532828298495575)
            ·
              refine ⟨32965332653299242447743363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21976888435532828298495575 32965332653299242447743363)
              ·
                refine ⟨49447998979948863671615045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32965332653299242447743363 49447998979948863671615045)
                ·
                  refine ⟨9271499808740411938427821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49447998979948863671615045 9271499808740411938427821)
                  ·
                    refine ⟨3476812428277654476910433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9271499808740411938427821 3476812428277654476910433)
                    ·
                      refine ⟨2607609321208240857682825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476812428277654476910433 2607609321208240857682825)
                      ·
                        rfl

theorem cell23_5078301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5078301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078301 prefixEnd_5078301 := by exact prefixLift 5078301
  have htrace : WordTrace (prefixWord ++ tailWord_5078301) baseStart_5078301 baseEnd_5078301 := by
    simpa [prefixWord, tailWord_5078301, baseEnd_5078301] using wordTrace_append hprefix tailTrace_5078301
  have hstable : (prefixWord ++ tailWord_5078301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078301).length < 2 ^ (prefixWord ++ tailWord_5078301).sum := by decide
  have hdescent : baseEnd_5078301 < baseStart_5078301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078302 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5078302 : Nat := 118140960795 + 5078302 * 2 ^ 59
def prefixEnd_5078302 : Nat := 4983230072969 + 3 ^ 40 * 5078302 * 2
def baseEnd_5078302 : Nat := 869203278229631784590107

theorem tailTrace_5078302 : CollatzResearch.WordTrace tailWord_5078302 prefixEnd_5078302 869203278229631784590107 := by
  unfold tailWord_5078302
  simp only [CollatzResearch.WordTrace]
  refine ⟨23152611306023329222129645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123480593632124422518024773 23152611306023329222129645)
  ·
    refine ⟨8682229239758748458298617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23152611306023329222129645 8682229239758748458298617)
    ·
      refine ⟨6511671929819061343723963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8682229239758748458298617 6511671929819061343723963)
      ·
        refine ⟨9767507894728592015585945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6511671929819061343723963 9767507894728592015585945)
        ·
          refine ⟨7325630921046444011689459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9767507894728592015585945 7325630921046444011689459)
          ·
            refine ⟨10988446381569666017534189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325630921046444011689459 10988446381569666017534189)
            ·
              refine ⟨4120667393088624756575321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10988446381569666017534189 4120667393088624756575321)
              ·
                refine ⟨3090500544816468567431491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4120667393088624756575321 3090500544816468567431491)
                ·
                  refine ⟨4635750817224702851147237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090500544816468567431491 4635750817224702851147237)
                  ·
                    refine ⟨869203278229631784590107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4635750817224702851147237 869203278229631784590107)
                    ·
                      rfl

theorem cell23_5078302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5078302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078302 prefixEnd_5078302 := by exact prefixLift 5078302
  have htrace : WordTrace (prefixWord ++ tailWord_5078302) baseStart_5078302 baseEnd_5078302 := by
    simpa [prefixWord, tailWord_5078302, baseEnd_5078302] using wordTrace_append hprefix tailTrace_5078302
  have hstable : (prefixWord ++ tailWord_5078302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078302).length < 2 ^ (prefixWord ++ tailWord_5078302).sum := by decide
  have hdescent : baseEnd_5078302 < baseStart_5078302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078324 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5078324 : Nat := 118140960795 + 5078324 * 2 ^ 59
def prefixEnd_5078324 : Nat := 4983230072969 + 3 ^ 40 * 5078324 * 2
def baseEnd_5078324 : Nat := 869207043754431422565073

theorem tailTrace_5078324 : CollatzResearch.WordTrace tailWord_5078324 prefixEnd_5078324 869207043754431422565073 := by
  unfold tailWord_5078324
  simp only [CollatzResearch.WordTrace]
  refine ⟨92610846427053465767169013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123481128569404621022892017 92610846427053465767169013)
  ·
    refine ⟨8682266852536262415672095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92610846427053465767169013 8682266852536262415672095)
    ·
      refine ⟨13023400278804393623508143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8682266852536262415672095 13023400278804393623508143)
      ·
        refine ⟨19535100418206590435262215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13023400278804393623508143 19535100418206590435262215)
        ·
          refine ⟨29302650627309885652893323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19535100418206590435262215 29302650627309885652893323)
          ·
            refine ⟨43953975940964828479339985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29302650627309885652893323 43953975940964828479339985)
            ·
              refine ⟨32965481955723621359504989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43953975940964828479339985 32965481955723621359504989)
              ·
                refine ⟨12362055733396358009814371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32965481955723621359504989 12362055733396358009814371)
                ·
                  refine ⟨18543083600094537014721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12362055733396358009814371 18543083600094537014721557)
                  ·
                    refine ⟨869207043754431422565073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18543083600094537014721557 869207043754431422565073)
                    ·
                      rfl

theorem cell23_5078324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5078324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078324 prefixEnd_5078324 := by exact prefixLift 5078324
  have htrace : WordTrace (prefixWord ++ tailWord_5078324) baseStart_5078324 baseEnd_5078324 := by
    simpa [prefixWord, tailWord_5078324, baseEnd_5078324] using wordTrace_append hprefix tailTrace_5078324
  have hstable : (prefixWord ++ tailWord_5078324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078324).length < 2 ^ (prefixWord ++ tailWord_5078324).sum := by decide
  have hdescent : baseEnd_5078324 < baseStart_5078324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078381 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5078381 : Nat := 118140960795 + 5078381 * 2 ^ 59
def prefixEnd_5078381 : Nat := 4983230072969 + 3 ^ 40 * 5078381 * 2
def baseEnd_5078381 : Nat := 2607650399660600544682457

theorem tailTrace_5078381 : CollatzResearch.WordTrace tailWord_5078381 prefixEnd_5078381 2607650399660600544682457 := by
  unfold tailWord_5078381
  simp only [CollatzResearch.WordTrace]
  refine ⟨185223771814900430269162997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123482514543266953512775331 185223771814900430269162997)
  ·
    refine ⟨17364728607646915337734031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185223771814900430269162997 17364728607646915337734031)
    ·
      refine ⟨26047092911470373006601047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17364728607646915337734031 26047092911470373006601047)
      ·
        refine ⟨39070639367205559509901571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26047092911470373006601047 39070639367205559509901571)
        ·
          refine ⟨58605959050808339264852357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39070639367205559509901571 58605959050808339264852357)
          ·
            refine ⟨10988617322026563612159817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58605959050808339264852357 10988617322026563612159817)
            ·
              refine ⟨8241462991519922709119863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10988617322026563612159817 8241462991519922709119863)
              ·
                refine ⟨12362194487279884063679795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8241462991519922709119863 12362194487279884063679795)
                ·
                  refine ⟨18543291730919826095519693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12362194487279884063679795 18543291730919826095519693)
                  ·
                    refine ⟨6953734399094934785819885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18543291730919826095519693 6953734399094934785819885)
                    ·
                      refine ⟨2607650399660600544682457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6953734399094934785819885 2607650399660600544682457)
                      ·
                        rfl

theorem cell23_5078381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5078381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078381 prefixEnd_5078381 := by exact prefixLift 5078381
  have htrace : WordTrace (prefixWord ++ tailWord_5078381) baseStart_5078381 baseEnd_5078381 := by
    simpa [prefixWord, tailWord_5078381, baseEnd_5078381] using wordTrace_append hprefix tailTrace_5078381
  have hstable : (prefixWord ++ tailWord_5078381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078381).length < 2 ^ (prefixWord ++ tailWord_5078381).sum := by decide
  have hdescent : baseEnd_5078381 < baseStart_5078381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078391 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 1, 3, 2]
def baseStart_5078391 : Nat := 118140960795 + 5078391 * 2 ^ 59
def prefixEnd_5078391 : Nat := 4983230072969 + 3 ^ 40 * 5078391 * 2
def baseEnd_5078391 : Nat := 2607655534467145505557411

theorem tailTrace_5078391 : CollatzResearch.WordTrace tailWord_5078391 prefixEnd_5078391 2607655534467145505557411 := by
  unfold tailWord_5078391
  simp only [CollatzResearch.WordTrace]
  refine ⟨185224136544864201977027027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123482757696576134651351351 185224136544864201977027027)
  ·
    refine ⟨277836204817296302965540541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185224136544864201977027027 277836204817296302965540541)
    ·
      refine ⟨104188576806486113612077703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277836204817296302965540541 104188576806486113612077703)
      ·
        refine ⟨156282865209729170418116555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104188576806486113612077703 156282865209729170418116555)
        ·
          refine ⟨234424297814593755627174833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156282865209729170418116555 234424297814593755627174833)
          ·
            refine ⟨175818223360945316720381125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234424297814593755627174833 175818223360945316720381125)
            ·
              refine ⟨32965916880177246885071461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175818223360945316720381125 32965916880177246885071461)
              ·
                refine ⟨6181109415033233790950899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32965916880177246885071461 6181109415033233790950899)
                ·
                  refine ⟨9271664122549850686426349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181109415033233790950899 9271664122549850686426349)
                  ·
                    refine ⟨3476874045956194007409881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9271664122549850686426349 3476874045956194007409881)
                    ·
                      refine ⟨2607655534467145505557411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476874045956194007409881 2607655534467145505557411)
                      ·
                        rfl

theorem cell23_5078391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_5078391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078391 prefixEnd_5078391 := by exact prefixLift 5078391
  have htrace : WordTrace (prefixWord ++ tailWord_5078391) baseStart_5078391 baseEnd_5078391 := by
    simpa [prefixWord, tailWord_5078391, baseEnd_5078391] using wordTrace_append hprefix tailTrace_5078391
  have hstable : (prefixWord ++ tailWord_5078391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078391).length < 2 ^ (prefixWord ++ tailWord_5078391).sum := by decide
  have hdescent : baseEnd_5078391 < baseStart_5078391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078397 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_5078397 : Nat := 118140960795 + 5078397 * 2 ^ 59
def prefixEnd_5078397 : Nat := 4983230072969 + 3 ^ 40 * 5078397 * 2
def baseEnd_5078397 : Nat := 869219538450357494027461

theorem tailTrace_5078397 : CollatzResearch.WordTrace tailWord_5078397 prefixEnd_5078397 869219538450357494027461 := by
  unfold tailWord_5078397
  simp only [CollatzResearch.WordTrace]
  refine ⟨185224355382842465001745445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123482903588561643334496963 185224355382842465001745445)
  ·
    refine ⟨34729566634282962187827271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185224355382842465001745445 34729566634282962187827271)
    ·
      refine ⟨52094349951424443281740907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34729566634282962187827271 52094349951424443281740907)
      ·
        refine ⟨78141524927136664922611361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52094349951424443281740907 78141524927136664922611361)
        ·
          refine ⟨58606143695352498691958521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78141524927136664922611361 58606143695352498691958521)
          ·
            refine ⟨43954607771514374018968891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58606143695352498691958521 43954607771514374018968891)
            ·
              refine ⟨65931911657271561028453337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43954607771514374018968891 65931911657271561028453337)
              ·
                refine ⟨49448933742953670771340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65931911657271561028453337 49448933742953670771340003)
                ·
                  refine ⟨74173400614430506157010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49448933742953670771340003 74173400614430506157010005)
                  ·
                    refine ⟨869219538450357494027461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74173400614430506157010005 869219538450357494027461)
                    ·
                      rfl

theorem cell23_5078397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_5078397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078397 prefixEnd_5078397 := by exact prefixLift 5078397
  have htrace : WordTrace (prefixWord ++ tailWord_5078397) baseStart_5078397 baseEnd_5078397 := by
    simpa [prefixWord, tailWord_5078397, baseEnd_5078397] using wordTrace_append hprefix tailTrace_5078397
  have hstable : (prefixWord ++ tailWord_5078397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078397).length < 2 ^ (prefixWord ++ tailWord_5078397).sum := by decide
  have hdescent : baseEnd_5078397 < baseStart_5078397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078402 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5078402 : Nat := 118140960795 + 5078402 * 2 ^ 59
def prefixEnd_5078402 : Nat := 4983230072969 + 3 ^ 40 * 5078402 * 2
def baseEnd_5078402 : Nat := 2607661182754344962519861

theorem tailTrace_5078402 : CollatzResearch.WordTrace tailWord_5078402 prefixEnd_5078402 2607661182754344962519861 := by
  unfold tailWord_5078402
  simp only [CollatzResearch.WordTrace]
  refine ⟨46306134436956087713919365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123483025165216233903784973 46306134436956087713919365)
  ·
    refine ⟨8682400206929266446359881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46306134436956087713919365 8682400206929266446359881)
    ·
      refine ⟨6511800155196949834769911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8682400206929266446359881 6511800155196949834769911)
      ·
        refine ⟨9767700232795424752154867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6511800155196949834769911 9767700232795424752154867)
        ·
          refine ⟨14651550349193137128232301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767700232795424752154867 14651550349193137128232301)
          ·
            refine ⟨5494331380947426423087113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14651550349193137128232301 5494331380947426423087113)
            ·
              refine ⟨4120748535710569817315335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5494331380947426423087113 4120748535710569817315335)
              ·
                refine ⟨6181122803565854725973003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120748535710569817315335 6181122803565854725973003)
                ·
                  refine ⟨9271684205348782088959505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181122803565854725973003 9271684205348782088959505)
                  ·
                    refine ⟨6953763154011586566719629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9271684205348782088959505 6953763154011586566719629)
                    ·
                      refine ⟨2607661182754344962519861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6953763154011586566719629 2607661182754344962519861)
                      ·
                        rfl

theorem cell23_5078402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5078402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078402 prefixEnd_5078402 := by exact prefixLift 5078402
  have htrace : WordTrace (prefixWord ++ tailWord_5078402) baseStart_5078402 baseEnd_5078402 := by
    simpa [prefixWord, tailWord_5078402, baseEnd_5078402] using wordTrace_append hprefix tailTrace_5078402
  have hstable : (prefixWord ++ tailWord_5078402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078402).length < 2 ^ (prefixWord ++ tailWord_5078402).sum := by decide
  have hdescent : baseEnd_5078402 < baseStart_5078402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078408 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_5078408 : Nat := 118140960795 + 5078408 * 2 ^ 59
def prefixEnd_5078408 : Nat := 4983230072969 + 3 ^ 40 * 5078408 * 2
def baseEnd_5078408 : Nat := 2607664263638271939044833

theorem tailTrace_5078408 : CollatzResearch.WordTrace tailWord_5078408 prefixEnd_5078408 2607664263638271939044833 := by
  unfold tailWord_5078408
  simp only [CollatzResearch.WordTrace]
  refine ⟨92612378292901306940197939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123483171057201742586930585 92612378292901306940197939)
  ·
    refine ⟨138918567439351960410296909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92612378292901306940197939 138918567439351960410296909)
    ·
      refine ⟨52094462789756985153861341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138918567439351960410296909 52094462789756985153861341)
      ·
        refine ⟨19535423546158869432698003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52094462789756985153861341 19535423546158869432698003)
        ·
          refine ⟨29303135319238304149047005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19535423546158869432698003 29303135319238304149047005)
          ·
            refine ⟨10988675744714364055892627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29303135319238304149047005 10988675744714364055892627)
            ·
              refine ⟨16483013617071546083838941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10988675744714364055892627 16483013617071546083838941)
              ·
                refine ⟨6181130106401829781439603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16483013617071546083838941 6181130106401829781439603)
                ·
                  refine ⟨9271695159602744672159405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181130106401829781439603 9271695159602744672159405)
                  ·
                    refine ⟨3476885684851029252059777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9271695159602744672159405 3476885684851029252059777)
                    ·
                      refine ⟨2607664263638271939044833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3476885684851029252059777 2607664263638271939044833)
                      ·
                        rfl

theorem cell23_5078408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_5078408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078408 prefixEnd_5078408 := by exact prefixLift 5078408
  have htrace : WordTrace (prefixWord ++ tailWord_5078408) baseStart_5078408 baseEnd_5078408 := by
    simpa [prefixWord, tailWord_5078408, baseEnd_5078408] using wordTrace_append hprefix tailTrace_5078408
  have hstable : (prefixWord ++ tailWord_5078408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078408).length < 2 ^ (prefixWord ++ tailWord_5078408).sum := by decide
  have hdescent : baseEnd_5078408 < baseStart_5078408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078417 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_5078417 : Nat := 118140960795 + 5078417 * 2 ^ 59
def prefixEnd_5078417 : Nat := 4983230072969 + 3 ^ 40 * 5078417 * 2
def baseEnd_5078417 : Nat := 2607668884964162403832291

theorem tailTrace_5078417 : CollatzResearch.WordTrace tailWord_5078417 prefixEnd_5078417 2607668884964162403832291 := by
  unfold tailWord_5078417
  simp only [CollatzResearch.WordTrace]
  refine ⟨185225084842770008417473505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123483389895180005611649003 185225084842770008417473505)
  ·
    refine ⟨138918813632077506313105129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185225084842770008417473505 138918813632077506313105129)
    ·
      refine ⟨104189110224058129734828847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138918813632077506313105129 104189110224058129734828847)
      ·
        refine ⟨156283665336087194602243271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104189110224058129734828847 156283665336087194602243271)
        ·
          refine ⟨234425498004130791903364907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156283665336087194602243271 234425498004130791903364907)
          ·
            refine ⟨351638247006196187855047361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234425498004130791903364907 351638247006196187855047361)
            ·
              refine ⟨263728685254647140891285521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351638247006196187855047361 263728685254647140891285521)
              ·
                refine ⟨197796513940985355668464141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263728685254647140891285521 197796513940985355668464141)
                ·
                  refine ⟨74173692727869508375674053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197796513940985355668464141 74173692727869508375674053)
                  ·
                    refine ⟨13907567386475532820438885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74173692727869508375674053 13907567386475532820438885)
                    ·
                      refine ⟨2607668884964162403832291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13907567386475532820438885 2607668884964162403832291)
                      ·
                        rfl

theorem cell23_5078417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_5078417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078417 prefixEnd_5078417 := by exact prefixLift 5078417
  have htrace : WordTrace (prefixWord ++ tailWord_5078417) baseStart_5078417 baseEnd_5078417 := by
    simpa [prefixWord, tailWord_5078417, baseEnd_5078417] using wordTrace_append hprefix tailTrace_5078417
  have hstable : (prefixWord ++ tailWord_5078417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078417).length < 2 ^ (prefixWord ++ tailWord_5078417).sum := by decide
  have hdescent : baseEnd_5078417 < baseStart_5078417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078474 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_5078474 : Nat := 118140960795 + 5078474 * 2 ^ 59
def prefixEnd_5078474 : Nat := 4983230072969 + 3 ^ 40 * 5078474 * 2
def baseEnd_5078474 : Nat := 869232717787156226939843

theorem tailTrace_5078474 : CollatzResearch.WordTrace tailWord_5078474 prefixEnd_5078474 869232717787156226939843 := by
  unfold tailWord_5078474
  simp only [CollatzResearch.WordTrace]
  refine ⟨46306790950890876788074619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123484775869042338101532317 46306790950890876788074619)
  ·
    refine ⟨69460186426336315182111929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46306790950890876788074619 69460186426336315182111929)
    ·
      refine ⟨52095139819752236386583947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69460186426336315182111929 52095139819752236386583947)
      ·
        refine ⟨78142709729628354579875921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52095139819752236386583947 78142709729628354579875921)
        ·
          refine ⟨58607032297221265934906941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78142709729628354579875921 58607032297221265934906941)
          ·
            refine ⟨21977637111457974725590103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58607032297221265934906941 21977637111457974725590103)
            ·
              refine ⟨32966455667186962088385155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21977637111457974725590103 32966455667186962088385155)
              ·
                refine ⟨49449683500780443132577733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32966455667186962088385155 49449683500780443132577733)
                ·
                  refine ⟨9271815656396333087358325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49449683500780443132577733 9271815656396333087358325)
                  ·
                    refine ⟨869232717787156226939843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9271815656396333087358325 869232717787156226939843)
                    ·
                      rfl

theorem cell23_5078474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_5078474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078474 prefixEnd_5078474 := by exact prefixLift 5078474
  have htrace : WordTrace (prefixWord ++ tailWord_5078474) baseStart_5078474 baseEnd_5078474 := by
    simpa [prefixWord, tailWord_5078474, baseEnd_5078474] using wordTrace_append hprefix tailTrace_5078474
  have hstable : (prefixWord ++ tailWord_5078474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078474).length < 2 ^ (prefixWord ++ tailWord_5078474).sum := by decide
  have hdescent : baseEnd_5078474 < baseStart_5078474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078631 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5078631 : Nat := 118140960795 + 5078631 * 2 ^ 59
def prefixEnd_5078631 : Nat := 4983230072969 + 3 ^ 40 * 5078631 * 2
def baseEnd_5078631 : Nat := 2607778769824224566556307

theorem tailTrace_5078631 : CollatzResearch.WordTrace tailWord_5078631 prefixEnd_5078631 2607778769824224566556307 := by
  unfold tailWord_5078631
  simp only [CollatzResearch.WordTrace]
  refine ⟨185232890063994722965763747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123488593375996481977175831 185232890063994722965763747)
  ·
    refine ⟨277849335095992084448645621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185232890063994722965763747 277849335095992084448645621)
    ·
      refine ⟨26048375165249257917060527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277849335095992084448645621 26048375165249257917060527)
      ·
        refine ⟨39072562747873886875590791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26048375165249257917060527 39072562747873886875590791)
        ·
          refine ⟨58608844121810830313386187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39072562747873886875590791 58608844121810830313386187)
          ·
            refine ⟨87913266182716245470079281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58608844121810830313386187 87913266182716245470079281)
            ·
              refine ⟨65934949637037184102559461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87913266182716245470079281 65934949637037184102559461)
              ·
                refine ⟨12362803056944472019229899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65934949637037184102559461 12362803056944472019229899)
                ·
                  refine ⟨18544204585416708028844849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12362803056944472019229899 18544204585416708028844849)
                  ·
                    refine ⟨13908153439062531021633637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18544204585416708028844849 13908153439062531021633637)
                    ·
                      refine ⟨2607778769824224566556307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13908153439062531021633637 2607778769824224566556307)
                      ·
                        rfl

theorem cell23_5078631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5078631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078631 prefixEnd_5078631 := by exact prefixLift 5078631
  have htrace : WordTrace (prefixWord ++ tailWord_5078631) baseStart_5078631 baseEnd_5078631 := by
    simpa [prefixWord, tailWord_5078631, baseEnd_5078631] using wordTrace_append hprefix tailTrace_5078631
  have hstable : (prefixWord ++ tailWord_5078631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078631).length < 2 ^ (prefixWord ++ tailWord_5078631).sum := by decide
  have hdescent : baseEnd_5078631 < baseStart_5078631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078718 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_5078718 : Nat := 118140960795 + 5078718 * 2 ^ 59
def prefixEnd_5078718 : Nat := 4983230072969 + 3 ^ 40 * 5078718 * 2
def baseEnd_5078718 : Nat := 869274480880388575389469

theorem tailTrace_5078718 : CollatzResearch.WordTrace tailWord_5078718 prefixEnd_5078718 869274480880388575389469 := by
  unfold tailWord_5078718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23154507901834942103022601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123490708809786357882787205 23154507901834942103022601)
  ·
    refine ⟨17365880926376206577266951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23154507901834942103022601 17365880926376206577266951)
    ·
      refine ⟨26048821389564309865900427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17365880926376206577266951 26048821389564309865900427)
      ·
        refine ⟨39073232084346464798850641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26048821389564309865900427 39073232084346464798850641)
        ·
          refine ⟨29304924063259848599137981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39073232084346464798850641 29304924063259848599137981)
          ·
            refine ⟨10989346523722443224676743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29304924063259848599137981 10989346523722443224676743)
            ·
              refine ⟨16484019785583664837015115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10989346523722443224676743 16484019785583664837015115)
              ·
                refine ⟨24726029678375497255522673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484019785583664837015115 24726029678375497255522673)
                ·
                  refine ⟨18544522258781622941642005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24726029678375497255522673 18544522258781622941642005)
                  ·
                    refine ⟨869274480880388575389469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18544522258781622941642005 869274480880388575389469)
                    ·
                      rfl

theorem cell23_5078718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_5078718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078718 prefixEnd_5078718 := by exact prefixLift 5078718
  have htrace : WordTrace (prefixWord ++ tailWord_5078718) baseStart_5078718 baseEnd_5078718 := by
    simpa [prefixWord, tailWord_5078718, baseEnd_5078718] using wordTrace_append hprefix tailTrace_5078718
  have hstable : (prefixWord ++ tailWord_5078718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078718).length < 2 ^ (prefixWord ++ tailWord_5078718).sum := by decide
  have hdescent : baseEnd_5078718 < baseStart_5078718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078759 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5078759 : Nat := 118140960795 + 5078759 * 2 ^ 59
def prefixEnd_5078759 : Nat := 4983230072969 + 3 ^ 40 * 5078759 * 2
def baseEnd_5078759 : Nat := 2607844495348000065755719

theorem tailTrace_5078759 : CollatzResearch.WordTrace tailWord_5078759 prefixEnd_5078759 2607844495348000065755719 := by
  unfold tailWord_5078759
  simp only [CollatzResearch.WordTrace]
  refine ⟨185237558607531000826423331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123491705738354000550948887 185237558607531000826423331)
  ·
    refine ⟨277856337911296501239634997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185237558607531000826423331 277856337911296501239634997)
    ·
      refine ⟨26049031679184046991215781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277856337911296501239634997 26049031679184046991215781)
      ·
        refine ⟨4884193439847008810852959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26049031679184046991215781 4884193439847008810852959)
        ·
          refine ⟨7326290159770513216279439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4884193439847008810852959 7326290159770513216279439)
          ·
            refine ⟨10989435239655769824419159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7326290159770513216279439 10989435239655769824419159)
            ·
              refine ⟨16484152859483654736628739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10989435239655769824419159 16484152859483654736628739)
              ·
                refine ⟨24726229289225482104943109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484152859483654736628739 24726229289225482104943109)
                ·
                  refine ⟨4636167991729777894676833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24726229289225482104943109 4636167991729777894676833)
                  ·
                    refine ⟨3477125993797333421007625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4636167991729777894676833 3477125993797333421007625)
                    ·
                      refine ⟨2607844495348000065755719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477125993797333421007625 2607844495348000065755719)
                      ·
                        rfl

theorem cell23_5078759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5078759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078759 prefixEnd_5078759 := by exact prefixLift 5078759
  have htrace : WordTrace (prefixWord ++ tailWord_5078759) baseStart_5078759 baseEnd_5078759 := by
    simpa [prefixWord, tailWord_5078759, baseEnd_5078759] using wordTrace_append hprefix tailTrace_5078759
  have hstable : (prefixWord ++ tailWord_5078759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078759).length < 2 ^ (prefixWord ++ tailWord_5078759).sum := by decide
  have hdescent : baseEnd_5078759 < baseStart_5078759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078761 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_5078761 : Nat := 118140960795 + 5078761 * 2 ^ 59
def prefixEnd_5078761 : Nat := 4983230072969 + 3 ^ 40 * 5078761 * 2
def baseEnd_5078761 : Nat := 869281840769769685976903

theorem tailTrace_5078761 : CollatzResearch.WordTrace tailWord_5078761 prefixEnd_5078761 869281840769769685976903 := by
  unfold tailWord_5078761
  simp only [CollatzResearch.WordTrace]
  refine ⟨185237631553523755167996137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123491754369015836778664091 185237631553523755167996137)
  ·
    refine ⟨138928223665142816375997103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185237631553523755167996137 138928223665142816375997103)
    ·
      refine ⟨208392335497714224563995655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138928223665142816375997103 208392335497714224563995655)
      ·
        refine ⟨312588503246571336845993483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208392335497714224563995655 312588503246571336845993483)
        ·
          refine ⟨468882754869857005268990225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312588503246571336845993483 468882754869857005268990225)
          ·
            refine ⟨351662066152392753951742669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468882754869857005268990225 351662066152392753951742669)
            ·
              refine ⟨131873274807147282731903501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351662066152392753951742669 131873274807147282731903501)
              ·
                refine ⟨49452478052680231024463813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131873274807147282731903501 49452478052680231024463813)
                ·
                  refine ⟨9272339634877543317086965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49452478052680231024463813 9272339634877543317086965)
                  ·
                    refine ⟨869281840769769685976903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9272339634877543317086965 869281840769769685976903)
                    ·
                      rfl

theorem cell23_5078761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_5078761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078761 prefixEnd_5078761 := by exact prefixLift 5078761
  have htrace : WordTrace (prefixWord ++ tailWord_5078761) baseStart_5078761 baseEnd_5078761 := by
    simpa [prefixWord, tailWord_5078761, baseEnd_5078761] using wordTrace_append hprefix tailTrace_5078761
  have hstable : (prefixWord ++ tailWord_5078761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078761).length < 2 ^ (prefixWord ++ tailWord_5078761).sum := by decide
  have hdescent : baseEnd_5078761 < baseStart_5078761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078765 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 5]
def baseStart_5078765 : Nat := 118140960795 + 5078765 * 2 ^ 59
def prefixEnd_5078765 : Nat := 4983230072969 + 3 ^ 40 * 5078765 * 2
def baseEnd_5078765 : Nat := 289760841803547449142299

theorem tailTrace_5078765 : CollatzResearch.WordTrace tailWord_5078765 prefixEnd_5078765 289760841803547449142299 := by
  unfold tailWord_5078765
  simp only [CollatzResearch.WordTrace]
  refine ⟨185237777445509263851141749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123491851630339509234094499 185237777445509263851141749)
  ·
    refine ⟨17366041635516493486044539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185237777445509263851141749 17366041635516493486044539)
    ·
      refine ⟨26049062453274740229066809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17366041635516493486044539 26049062453274740229066809)
      ·
        refine ⟨19536796839956055171800107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26049062453274740229066809 19536796839956055171800107)
        ·
          refine ⟨29305195259934082757700161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19536796839956055171800107 29305195259934082757700161)
          ·
            refine ⟨21978896444950562068275121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29305195259934082757700161 21978896444950562068275121)
            ·
              refine ⟨16484172333712921551206341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21978896444950562068275121 16484172333712921551206341)
              ·
                refine ⟨3090782312571172790851189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16484172333712921551206341 3090782312571172790851189)
                ·
                  refine ⟨289760841803547449142299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3090782312571172790851189 289760841803547449142299)
                  ·
                    rfl

theorem cell23_5078765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_5078765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078765 prefixEnd_5078765 := by exact prefixLift 5078765
  have htrace : WordTrace (prefixWord ++ tailWord_5078765) baseStart_5078765 baseEnd_5078765 := by
    simpa [prefixWord, tailWord_5078765, baseEnd_5078765] using wordTrace_append hprefix tailTrace_5078765
  have hstable : (prefixWord ++ tailWord_5078765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078765).length < 2 ^ (prefixWord ++ tailWord_5078765).sum := by decide
  have hdescent : baseEnd_5078765 < baseStart_5078765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078768 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 2, 5, 2]
def baseStart_5078768 : Nat := 118140960795 + 5078768 * 2 ^ 59
def prefixEnd_5078768 : Nat := 4983230072969 + 3 ^ 40 * 5078768 * 2
def baseEnd_5078768 : Nat := 2607849116673890530543177

theorem tailTrace_5078768 : CollatzResearch.WordTrace tailWord_5078768 prefixEnd_5078768 2607849116673890530543177 := by
  unfold tailWord_5078768
  simp only [CollatzResearch.WordTrace]
  refine ⟨92618943432249197681750479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123491924576332263575667305 92618943432249197681750479)
  ·
    refine ⟨138928415148373796522625719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92618943432249197681750479 138928415148373796522625719)
    ·
      refine ⟨208392622722560694783938579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138928415148373796522625719 208392622722560694783938579)
      ·
        refine ⟨312588934083841042175907869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208392622722560694783938579 312588934083841042175907869)
        ·
          refine ⟨117220850281440390815965451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312588934083841042175907869 117220850281440390815965451)
          ·
            refine ⟨175831275422160586223948177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117220850281440390815965451 175831275422160586223948177)
            ·
              refine ⟨131873456566620439667961133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175831275422160586223948177 131873456566620439667961133)
              ·
                refine ⟨49452546212482664875485425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131873456566620439667961133 49452546212482664875485425)
                ·
                  refine ⟨37089409659361998656614069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49452546212482664875485425 37089409659361998656614069)
                  ·
                    refine ⟨3477132155565187374057569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37089409659361998656614069 3477132155565187374057569)
                    ·
                      refine ⟨2607849116673890530543177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477132155565187374057569 2607849116673890530543177)
                      ·
                        rfl

theorem cell23_5078768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 5, 2].length) (baseStart_5078768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078768 prefixEnd_5078768 := by exact prefixLift 5078768
  have htrace : WordTrace (prefixWord ++ tailWord_5078768) baseStart_5078768 baseEnd_5078768 := by
    simpa [prefixWord, tailWord_5078768, baseEnd_5078768] using wordTrace_append hprefix tailTrace_5078768
  have hstable : (prefixWord ++ tailWord_5078768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078768).length < 2 ^ (prefixWord ++ tailWord_5078768).sum := by decide
  have hdescent : baseEnd_5078768 < baseStart_5078768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078771 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5]
def baseStart_5078771 : Nat := 118140960795 + 5078771 * 2 ^ 59
def prefixEnd_5078771 : Nat := 4983230072969 + 3 ^ 40 * 5078771 * 2
def baseEnd_5078771 : Nat := 2607850657115854018805663

theorem tailTrace_5078771 : CollatzResearch.WordTrace tailWord_5078771 prefixEnd_5078771 2607850657115854018805663 := by
  unfold tailWord_5078771
  simp only [CollatzResearch.WordTrace]
  refine ⟨185237996283487526875860167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123491997522325017917240111 185237996283487526875860167)
  ·
    refine ⟨277856994425231290313790251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185237996283487526875860167 277856994425231290313790251)
    ·
      refine ⟨416785491637846935470685377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277856994425231290313790251 416785491637846935470685377)
      ·
        refine ⟨312589118728385201603014033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416785491637846935470685377 312589118728385201603014033)
        ·
          refine ⟨234441839046288901202260525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312589118728385201603014033 234441839046288901202260525)
          ·
            refine ⟨87915689642358337950847697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234441839046288901202260525 87915689642358337950847697)
            ·
              refine ⟨65936767231768753463135773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87915689642358337950847697 65936767231768753463135773)
              ·
                refine ⟨24726287711913282548675915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65936767231768753463135773 24726287711913282548675915)
                ·
                  refine ⟨37089431567869923823013873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24726287711913282548675915 37089431567869923823013873)
                  ·
                    refine ⟨27817073675902442867260405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37089431567869923823013873 27817073675902442867260405)
                    ·
                      refine ⟨2607850657115854018805663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27817073675902442867260405 2607850657115854018805663)
                      ·
                        rfl

theorem cell23_5078771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_5078771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078771 prefixEnd_5078771 := by exact prefixLift 5078771
  have htrace : WordTrace (prefixWord ++ tailWord_5078771) baseStart_5078771 baseEnd_5078771 := by
    simpa [prefixWord, tailWord_5078771, baseEnd_5078771] using wordTrace_append hprefix tailTrace_5078771
  have hstable : (prefixWord ++ tailWord_5078771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078771).length < 2 ^ (prefixWord ++ tailWord_5078771).sum := by decide
  have hdescent : baseEnd_5078771 < baseStart_5078771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078772 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5078772 : Nat := 118140960795 + 5078772 * 2 ^ 59
def prefixEnd_5078772 : Nat := 4983230072969 + 3 ^ 40 * 5078772 * 2
def baseEnd_5078772 : Nat := 2607851170596508514893159

theorem tailTrace_5078772 : CollatzResearch.WordTrace tailWord_5078772 prefixEnd_5078772 2607851170596508514893159 := by
  unfold tailWord_5078772
  simp only [CollatzResearch.WordTrace]
  refine ⟨92619016378241952023323285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123492021837655936031097713 92619016378241952023323285)
  ·
    refine ⟨4341516392730091501093279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92619016378241952023323285 4341516392730091501093279)
    ·
      refine ⟨6512274589095137251639919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4341516392730091501093279 6512274589095137251639919)
      ·
        refine ⟨9768411883642705877459879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512274589095137251639919 9768411883642705877459879)
        ·
          refine ⟨14652617825464058816189819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9768411883642705877459879 14652617825464058816189819)
          ·
            refine ⟨21978926738196088224284729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14652617825464058816189819 21978926738196088224284729)
            ·
              refine ⟨16484195053647066168213547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21978926738196088224284729 16484195053647066168213547)
              ·
                refine ⟨24726292580470599252320321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484195053647066168213547 24726292580470599252320321)
                ·
                  refine ⟨18544719435352949439240241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24726292580470599252320321 18544719435352949439240241)
                  ·
                    refine ⟨13908539576514712079430181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18544719435352949439240241 13908539576514712079430181)
                    ·
                      refine ⟨2607851170596508514893159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13908539576514712079430181 2607851170596508514893159)
                      ·
                        rfl

theorem cell23_5078772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5078772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078772 prefixEnd_5078772 := by exact prefixLift 5078772
  have htrace : WordTrace (prefixWord ++ tailWord_5078772) baseStart_5078772 baseEnd_5078772 := by
    simpa [prefixWord, tailWord_5078772, baseEnd_5078772] using wordTrace_append hprefix tailTrace_5078772
  have hstable : (prefixWord ++ tailWord_5078772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078772).length < 2 ^ (prefixWord ++ tailWord_5078772).sum := by decide
  have hdescent : baseEnd_5078772 < baseStart_5078772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078798 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_5078798 : Nat := 118140960795 + 5078798 * 2 ^ 59
def prefixEnd_5078798 : Nat := 4983230072969 + 3 ^ 40 * 5078798 * 2
def baseEnd_5078798 : Nat := 2607864521093525413168039

theorem tailTrace_5078798 : CollatzResearch.WordTrace tailWord_5078798 prefixEnd_5078798 2607864521093525413168039 := by
  unfold tailWord_5078798
  simp only [CollatzResearch.WordTrace]
  refine ⟨23154872631798713810886631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123492654036259806991395365 23154872631798713810886631)
  ·
    refine ⟨34732308947698070716329947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23154872631798713810886631 34732308947698070716329947)
    ·
      refine ⟨52098463421547106074494921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34732308947698070716329947 52098463421547106074494921)
      ·
        refine ⟨39073847566160329555871191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52098463421547106074494921 39073847566160329555871191)
        ·
          refine ⟨58610771349240494333806787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39073847566160329555871191 58610771349240494333806787)
          ·
            refine ⟨87916157023860741500710181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58610771349240494333806787 87916157023860741500710181)
            ·
              refine ⟨16484279441973889031383159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87916157023860741500710181 16484279441973889031383159)
              ·
                refine ⟨24726419162960833547074739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484279441973889031383159 24726419162960833547074739)
                ·
                  refine ⟨37089628744441250320612109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24726419162960833547074739 37089628744441250320612109)
                  ·
                    refine ⟨13908610779165468870229541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37089628744441250320612109 13908610779165468870229541)
                    ·
                      refine ⟨2607864521093525413168039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13908610779165468870229541 2607864521093525413168039)
                      ·
                        rfl

theorem cell23_5078798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_5078798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078798 prefixEnd_5078798 := by exact prefixLift 5078798
  have htrace : WordTrace (prefixWord ++ tailWord_5078798) baseStart_5078798 baseEnd_5078798 := by
    simpa [prefixWord, tailWord_5078798, baseEnd_5078798] using wordTrace_append hprefix tailTrace_5078798
  have hstable : (prefixWord ++ tailWord_5078798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078798).length < 2 ^ (prefixWord ++ tailWord_5078798).sum := by decide
  have hdescent : baseEnd_5078798 < baseStart_5078798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078801 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_5078801 : Nat := 118140960795 + 5078801 * 2 ^ 59
def prefixEnd_5078801 : Nat := 4983230072969 + 3 ^ 40 * 5078801 * 2
def baseEnd_5078801 : Nat := 2607866061535488901430525

theorem tailTrace_5078801 : CollatzResearch.WordTrace tailWord_5078801 prefixEnd_5078801 2607866061535488901430525 := by
  unfold tailWord_5078801
  simp only [CollatzResearch.WordTrace]
  refine ⟨185239090473378841999452257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123492726982252561332968171 185239090473378841999452257)
  ·
    refine ⟨138929317855034131499589193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185239090473378841999452257 138929317855034131499589193)
    ·
      refine ⟨104196988391275598624691895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138929317855034131499589193 104196988391275598624691895)
      ·
        refine ⟨156295482586913397937037843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104196988391275598624691895 156295482586913397937037843)
        ·
          refine ⟨234443223880370096905556765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156295482586913397937037843 234443223880370096905556765)
          ·
            refine ⟨87916208955138786339583787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234443223880370096905556765 87916208955138786339583787)
            ·
              refine ⟨131874313432708179509375681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87916208955138786339583787 131874313432708179509375681)
              ·
                refine ⟨98905735074531134632031761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131874313432708179509375681 98905735074531134632031761)
                ·
                  refine ⟨74179301305898350974023821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98905735074531134632031761 74179301305898350974023821)
                  ·
                    refine ⟨27817237989711881615258933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74179301305898350974023821 27817237989711881615258933)
                    ·
                      refine ⟨2607866061535488901430525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27817237989711881615258933 2607866061535488901430525)
                      ·
                        rfl

theorem cell23_5078801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_5078801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078801 prefixEnd_5078801 := by exact prefixLift 5078801
  have htrace : WordTrace (prefixWord ++ tailWord_5078801) baseStart_5078801 baseEnd_5078801 := by
    simpa [prefixWord, tailWord_5078801, baseEnd_5078801] using wordTrace_append hprefix tailTrace_5078801
  have hstable : (prefixWord ++ tailWord_5078801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078801).length < 2 ^ (prefixWord ++ tailWord_5078801).sum := by decide
  have hdescent : baseEnd_5078801 < baseStart_5078801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078808 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 5, 4]
def baseStart_5078808 : Nat := 118140960795 + 5078808 * 2 ^ 59
def prefixEnd_5078808 : Nat := 4983230072969 + 3 ^ 40 * 5078808 * 2
def baseEnd_5078808 : Nat := 869289885300023458014331

theorem tailTrace_5078808 : CollatzResearch.WordTrace tailWord_5078808 prefixEnd_5078808 869289885300023458014331 := by
  unfold tailWord_5078808
  simp only [CollatzResearch.WordTrace]
  refine ⟨92619672892176741097478539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123492897189568988129971385 92619672892176741097478539)
  ·
    refine ⟨138929509338265111646217809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92619672892176741097478539 138929509338265111646217809)
    ·
      refine ⟨104197132003698833734663357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138929509338265111646217809 104197132003698833734663357)
      ·
        refine ⟨39073924501387062650498759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104197132003698833734663357 39073924501387062650498759)
        ·
          refine ⟨58610886752080593975748139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39073924501387062650498759 58610886752080593975748139)
          ·
            refine ⟨87916330128120890963622209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58610886752080593975748139 87916330128120890963622209)
            ·
              refine ⟨65937247596090668222716657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87916330128120890963622209 65937247596090668222716657)
              ·
                refine ⟨49452935697068001167037493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65937247596090668222716657 49452935697068001167037493)
                ·
                  refine ⟨4636212721600125109409765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49452935697068001167037493 4636212721600125109409765)
                  ·
                    refine ⟨869289885300023458014331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636212721600125109409765 869289885300023458014331)
                    ·
                      rfl

theorem cell23_5078808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_5078808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078808 prefixEnd_5078808 := by exact prefixLift 5078808
  have htrace : WordTrace (prefixWord ++ tailWord_5078808) baseStart_5078808 baseEnd_5078808 := by
    simpa [prefixWord, tailWord_5078808, baseEnd_5078808] using wordTrace_append hprefix tailTrace_5078808
  have hstable : (prefixWord ++ tailWord_5078808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078808).length < 2 ^ (prefixWord ++ tailWord_5078808).sum := by decide
  have hdescent : baseEnd_5078808 < baseStart_5078808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078811 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4]
def baseStart_5078811 : Nat := 118140960795 + 5078811 * 2 ^ 59
def prefixEnd_5078811 : Nat := 4983230072969 + 3 ^ 40 * 5078811 * 2
def baseEnd_5078811 : Nat := 2607871196342033862305479

theorem tailTrace_5078811 : CollatzResearch.WordTrace tailWord_5078811 prefixEnd_5078811 2607871196342033862305479 := by
  unfold tailWord_5078811
  simp only [CollatzResearch.WordTrace]
  refine ⟨185239455203342613707316287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123492970135561742471544191 185239455203342613707316287)
  ·
    refine ⟨277859182805013920560974431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185239455203342613707316287 277859182805013920560974431)
    ·
      refine ⟨416788774207520880841461647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277859182805013920560974431 416788774207520880841461647)
      ·
        refine ⟨625183161311281321262192471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416788774207520880841461647 625183161311281321262192471)
        ·
          refine ⟨937774741966921981893288707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625183161311281321262192471 937774741966921981893288707)
          ·
            refine ⟨1406662112950382972839933061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937774741966921981893288707 1406662112950382972839933061)
            ·
              refine ⟨263749146178196807407487449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1406662112950382972839933061 263749146178196807407487449)
              ·
                refine ⟨197811859633647605555615587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263749146178196807407487449 197811859633647605555615587)
                ·
                  refine ⟨296717789450471408333423381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197811859633647605555615587 296717789450471408333423381)
                  ·
                    refine ⟨13908646380490847265629221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 296717789450471408333423381 13908646380490847265629221)
                    ·
                      refine ⟨2607871196342033862305479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13908646380490847265629221 2607871196342033862305479)
                      ·
                        rfl

theorem cell23_5078811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_5078811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078811 prefixEnd_5078811 := by exact prefixLift 5078811
  have htrace : WordTrace (prefixWord ++ tailWord_5078811) baseStart_5078811 baseEnd_5078811 := by
    simpa [prefixWord, tailWord_5078811, baseEnd_5078811] using wordTrace_append hprefix tailTrace_5078811
  have hstable : (prefixWord ++ tailWord_5078811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078811).length < 2 ^ (prefixWord ++ tailWord_5078811).sum := by decide
  have hdescent : baseEnd_5078811 < baseStart_5078811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078905 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 4]
def baseStart_5078905 : Nat := 118140960795 + 5078905 * 2 ^ 59
def prefixEnd_5078905 : Nat := 4983230072969 + 3 ^ 40 * 5078905 * 2
def baseEnd_5078905 : Nat := 2607919463523556494530047

theorem tailTrace_5078905 : CollatzResearch.WordTrace tailWord_5078905 prefixEnd_5078905 2607919463523556494530047 := by
  unfold tailWord_5078905
  simp only [CollatzResearch.WordTrace]
  refine ⟨185242883665002067761238169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123495255776668045174158779 185242883665002067761238169)
  ·
    refine ⟨138932162748751550820928627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185242883665002067761238169 138932162748751550820928627)
    ·
      refine ⟨208398244123127326231392941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138932162748751550820928627 208398244123127326231392941)
      ·
        refine ⟨78149341546172747336772353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208398244123127326231392941 78149341546172747336772353)
        ·
          refine ⟨58612006159629560502579265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78149341546172747336772353 58612006159629560502579265)
          ·
            refine ⟨43959004619722170376934449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58612006159629560502579265 43959004619722170376934449)
            ·
              refine ⟨32969253464791627782700837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43959004619722170376934449 32969253464791627782700837)
              ·
                refine ⟨6181735024648430209256407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32969253464791627782700837 6181735024648430209256407)
                ·
                  refine ⟨9272602536972645313884611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181735024648430209256407 9272602536972645313884611)
                  ·
                    refine ⟨13908903805458967970826917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9272602536972645313884611 13908903805458967970826917)
                    ·
                      refine ⟨2607919463523556494530047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13908903805458967970826917 2607919463523556494530047)
                      ·
                        rfl

theorem cell23_5078905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_5078905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078905 prefixEnd_5078905 := by exact prefixLift 5078905
  have htrace : WordTrace (prefixWord ++ tailWord_5078905) baseStart_5078905 baseEnd_5078905 := by
    simpa [prefixWord, tailWord_5078905, baseEnd_5078905] using wordTrace_append hprefix tailTrace_5078905
  have hstable : (prefixWord ++ tailWord_5078905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078905).length < 2 ^ (prefixWord ++ tailWord_5078905).sum := by decide
  have hdescent : baseEnd_5078905 < baseStart_5078905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078919 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 1, 5]
def baseStart_5078919 : Nat := 118140960795 + 5078919 * 2 ^ 59
def prefixEnd_5078919 : Nat := 4983230072969 + 3 ^ 40 * 5078919 * 2
def baseEnd_5078919 : Nat := 869308884084239813251661

theorem tailTrace_5078919 : CollatzResearch.WordTrace tailWord_5078919 prefixEnd_5078919 869308884084239813251661 := by
  unfold tailWord_5078919
  simp only [CollatzResearch.WordTrace]
  refine ⟨185243394286951348152247811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123495596191300898768165207 185243394286951348152247811)
  ·
    refine ⟨277865091430427022228371717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185243394286951348152247811 277865091430427022228371717)
    ·
      refine ⟨52099704643205066667819697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277865091430427022228371717 52099704643205066667819697)
      ·
        refine ⟨39074778482403800000864773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52099704643205066667819697 39074778482403800000864773)
        ·
          refine ⟨7326520965450712500162145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39074778482403800000864773 7326520965450712500162145)
          ·
            refine ⟨5494890724088034375121609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7326520965450712500162145 5494890724088034375121609)
            ·
              refine ⟨4121168043066025781341207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5494890724088034375121609 4121168043066025781341207)
              ·
                refine ⟨6181752064599038672011811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121168043066025781341207 6181752064599038672011811)
                ·
                  refine ⟨9272628096898558008017717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181752064599038672011811 9272628096898558008017717)
                  ·
                    refine ⟨869308884084239813251661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9272628096898558008017717 869308884084239813251661)
                    ·
                      rfl

theorem cell23_5078919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_5078919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078919 prefixEnd_5078919 := by exact prefixLift 5078919
  have htrace : WordTrace (prefixWord ++ tailWord_5078919) baseStart_5078919 baseEnd_5078919 := by
    simpa [prefixWord, tailWord_5078919, baseEnd_5078919] using wordTrace_append hprefix tailTrace_5078919
  have hstable : (prefixWord ++ tailWord_5078919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078919).length < 2 ^ (prefixWord ++ tailWord_5078919).sum := by decide
  have hdescent : baseEnd_5078919 < baseStart_5078919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078932 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_5078932 : Nat := 118140960795 + 5078932 * 2 ^ 59
def prefixEnd_5078932 : Nat := 4983230072969 + 3 ^ 40 * 5078932 * 2
def baseEnd_5078932 : Nat := 869311109167075962964141

theorem tailTrace_5078932 : CollatzResearch.WordTrace tailWord_5078932 prefixEnd_5078932 869311109167075962964141 := by
  unfold tailWord_5078932
  simp only [CollatzResearch.WordTrace]
  refine ⟨92621934217952125686235525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123495912290602834248314033 92621934217952125686235525)
  ·
    refine ⟨17366612665866023566169161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92621934217952125686235525 17366612665866023566169161)
    ·
      refine ⟨13024959499399517674626871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17366612665866023566169161 13024959499399517674626871)
      ·
        refine ⟨19537439249099276511940307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13024959499399517674626871 19537439249099276511940307)
        ·
          refine ⟨29306158873648914767910461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19537439249099276511940307 29306158873648914767910461)
          ·
            refine ⟨10989809577618343037966423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29306158873648914767910461 10989809577618343037966423)
            ·
              refine ⟨16484714366427514556949635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10989809577618343037966423 16484714366427514556949635)
              ·
                refine ⟨24727071549641271835424453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484714366427514556949635 24727071549641271835424453)
                ·
                  refine ⟨4636325915557738469142085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24727071549641271835424453 4636325915557738469142085)
                  ·
                    refine ⟨869311109167075962964141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636325915557738469142085 869311109167075962964141)
                    ·
                      rfl

theorem cell23_5078932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_5078932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078932 prefixEnd_5078932 := by exact prefixLift 5078932
  have htrace : WordTrace (prefixWord ++ tailWord_5078932) baseStart_5078932 baseEnd_5078932 := by
    simpa [prefixWord, tailWord_5078932, baseEnd_5078932] using wordTrace_append hprefix tailTrace_5078932
  have hstable : (prefixWord ++ tailWord_5078932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078932).length < 2 ^ (prefixWord ++ tailWord_5078932).sum := by decide
  have hdescent : baseEnd_5078932 < baseStart_5078932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078955 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 3]
def baseStart_5078955 : Nat := 118140960795 + 5078955 * 2 ^ 59
def prefixEnd_5078955 : Nat := 4983230072969 + 3 ^ 40 * 5078955 * 2
def baseEnd_5078955 : Nat := 2607945137556281298904817

theorem tailTrace_5078955 : CollatzResearch.WordTrace tailWord_5078955 prefixEnd_5078955 2607945137556281298904817 := by
  unfold tailWord_5078955
  simp only [CollatzResearch.WordTrace]
  refine ⟨185244707314820926300558319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123496471543213950867038879 185244707314820926300558319)
  ·
    refine ⟨277867060972231389450837479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185244707314820926300558319 277867060972231389450837479)
    ·
      refine ⟨416800591458347084176256219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277867060972231389450837479 416800591458347084176256219)
      ·
        refine ⟨625200887187520626264384329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416800591458347084176256219 625200887187520626264384329)
        ·
          refine ⟨468900665390640469698288247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625200887187520626264384329 468900665390640469698288247)
          ·
            refine ⟨703350998085960704547432371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468900665390640469698288247 703350998085960704547432371)
            ·
              refine ⟨1055026497128941056821148557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703350998085960704547432371 1055026497128941056821148557)
              ·
                refine ⟨395634936423352896307930709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1055026497128941056821148557 395634936423352896307930709)
                ·
                  refine ⟨4636346911211166753608563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 395634936423352896307930709 4636346911211166753608563)
                  ·
                    refine ⟨6954520366816750130412845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4636346911211166753608563 6954520366816750130412845)
                    ·
                      refine ⟨2607945137556281298904817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6954520366816750130412845 2607945137556281298904817)
                      ·
                        rfl

theorem cell23_5078955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 3].length) (baseStart_5078955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078955 prefixEnd_5078955 := by exact prefixLift 5078955
  have htrace : WordTrace (prefixWord ++ tailWord_5078955) baseStart_5078955 baseEnd_5078955 := by
    simpa [prefixWord, tailWord_5078955, baseEnd_5078955] using wordTrace_append hprefix tailTrace_5078955
  have hstable : (prefixWord ++ tailWord_5078955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078955).length < 2 ^ (prefixWord ++ tailWord_5078955).sum := by decide
  have hdescent : baseEnd_5078955 < baseStart_5078955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078968 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_5078968 : Nat := 118140960795 + 5078968 * 2 ^ 59
def prefixEnd_5078968 : Nat := 4983230072969 + 3 ^ 40 * 5078968 * 2
def baseEnd_5078968 : Nat := 2607951812804789748042257

theorem tailTrace_5078968 : CollatzResearch.WordTrace tailWord_5078968 prefixEnd_5078968 2607951812804789748042257 := by
  unfold tailWord_5078968
  simp only [CollatzResearch.WordTrace]
  refine ⟨92622590731886914760390779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123496787642515886347187705 92622590731886914760390779)
  ·
    refine ⟨138933886097830372140586169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92622590731886914760390779 138933886097830372140586169)
    ·
      refine ⟨104200414573372779105439627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138933886097830372140586169 104200414573372779105439627)
      ·
        refine ⟨156300621860059168658159441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104200414573372779105439627 156300621860059168658159441)
        ·
          refine ⟨117225466395044376493619581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156300621860059168658159441 117225466395044376493619581)
          ·
            refine ⟨43959549898141641185107343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117225466395044376493619581 43959549898141641185107343)
            ·
              refine ⟨65939324847212461777661015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43959549898141641185107343 65939324847212461777661015)
              ·
                refine ⟨98908987270818692666491523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65939324847212461777661015 98908987270818692666491523)
                ·
                  refine ⟨148363480906228038999737285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98908987270818692666491523 148363480906228038999737285)
                  ·
                    refine ⟨27818152669917757312450741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148363480906228038999737285 27818152669917757312450741)
                    ·
                      refine ⟨2607951812804789748042257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27818152669917757312450741 2607951812804789748042257)
                      ·
                        rfl

theorem cell23_5078968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_5078968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078968 prefixEnd_5078968 := by exact prefixLift 5078968
  have htrace : WordTrace (prefixWord ++ tailWord_5078968) baseStart_5078968 baseEnd_5078968 := by
    simpa [prefixWord, tailWord_5078968, baseEnd_5078968] using wordTrace_append hprefix tailTrace_5078968
  have hstable : (prefixWord ++ tailWord_5078968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078968).length < 2 ^ (prefixWord ++ tailWord_5078968).sum := by decide
  have hdescent : baseEnd_5078968 < baseStart_5078968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5078973 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_5078973 : Nat := 118140960795 + 5078973 * 2 ^ 59
def prefixEnd_5078973 : Nat := 4983230072969 + 3 ^ 40 * 5078973 * 2
def baseEnd_5078973 : Nat := 2607954380208062228479735

theorem tailTrace_5078973 : CollatzResearch.WordTrace tailWord_5078973 prefixEnd_5078973 2607954380208062228479735 := by
  unfold tailWord_5078973
  simp only [CollatzResearch.WordTrace]
  refine ⟨185245363828755715374713573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123496909219170476916475715 185245363828755715374713573)
  ·
    refine ⟨34733505717891696632758795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185245363828755715374713573 34733505717891696632758795)
    ·
      refine ⟨52100258576837544949138193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34733505717891696632758795 52100258576837544949138193)
      ·
        refine ⟨39075193932628158711853645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52100258576837544949138193 39075193932628158711853645)
        ·
          refine ⟨14653197724735559516945117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39075193932628158711853645 14653197724735559516945117)
          ·
            refine ⟨5494949146775834818854419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14653197724735559516945117 5494949146775834818854419)
            ·
              refine ⟨8242423720163752228281629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494949146775834818854419 8242423720163752228281629)
              ·
                refine ⟨3090908895061407085605611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8242423720163752228281629 3090908895061407085605611)
                ·
                  refine ⟨4636363342592110628408417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090908895061407085605611 4636363342592110628408417)
                  ·
                    refine ⟨3477272506944082971306313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4636363342592110628408417 3477272506944082971306313)
                    ·
                      refine ⟨2607954380208062228479735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477272506944082971306313 2607954380208062228479735)
                      ·
                        rfl

theorem cell23_5078973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_5078973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5078973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5078973 prefixEnd_5078973 := by exact prefixLift 5078973
  have htrace : WordTrace (prefixWord ++ tailWord_5078973) baseStart_5078973 baseEnd_5078973 := by
    simpa [prefixWord, tailWord_5078973, baseEnd_5078973] using wordTrace_append hprefix tailTrace_5078973
  have hstable : (prefixWord ++ tailWord_5078973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5078973).length < 2 ^ (prefixWord ++ tailWord_5078973).sum := by decide
  have hdescent : baseEnd_5078973 < baseStart_5078973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5078973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079008 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_5079008 : Nat := 118140960795 + 5079008 * 2 ^ 59
def prefixEnd_5079008 : Nat := 4983230072969 + 3 ^ 40 * 5079008 * 2
def baseEnd_5079008 : Nat := 2607972352030969591542073

theorem tailTrace_5079008 : CollatzResearch.WordTrace tailWord_5079008 prefixEnd_5079008 2607972352030969591542073 := by
  unfold tailWord_5079008
  simp only [CollatzResearch.WordTrace]
  refine ⟨92623320191814458176118839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123497760255752610901491785 92623320191814458176118839)
  ·
    refine ⟨138934980287721687264178259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92623320191814458176118839 138934980287721687264178259)
    ·
      refine ⟨208402470431582530896267389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138934980287721687264178259 208402470431582530896267389)
      ·
        refine ⟨78150926411843449086100271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208402470431582530896267389 78150926411843449086100271)
        ·
          refine ⟨117226389617765173629150407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78150926411843449086100271 117226389617765173629150407)
          ·
            refine ⟨175839584426647760443725611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117226389617765173629150407 175839584426647760443725611)
            ·
              refine ⟨263759376639971640665588417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175839584426647760443725611 263759376639971640665588417)
              ·
                refine ⟨197819532479978730499191313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263759376639971640665588417 197819532479978730499191313)
                ·
                  refine ⟨148364649359984047874393485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197819532479978730499191313 148364649359984047874393485)
                  ·
                    refine ⟨55636743509994017952897557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148364649359984047874393485 55636743509994017952897557)
                    ·
                      refine ⟨2607972352030969591542073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55636743509994017952897557 2607972352030969591542073)
                      ·
                        rfl

theorem cell23_5079008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_5079008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079008 prefixEnd_5079008 := by exact prefixLift 5079008
  have htrace : WordTrace (prefixWord ++ tailWord_5079008) baseStart_5079008 baseEnd_5079008 := by
    simpa [prefixWord, tailWord_5079008, baseEnd_5079008] using wordTrace_append hprefix tailTrace_5079008
  have hstable : (prefixWord ++ tailWord_5079008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079008).length < 2 ^ (prefixWord ++ tailWord_5079008).sum := by decide
  have hdescent : baseEnd_5079008 < baseStart_5079008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079012 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_5079012 : Nat := 118140960795 + 5079012 * 2 ^ 59
def prefixEnd_5079012 : Nat := 4983230072969 + 3 ^ 40 * 5079012 * 2
def baseEnd_5079012 : Nat := 2607974405953587575892055

theorem tailTrace_5079012 : CollatzResearch.WordTrace tailWord_5079012 prefixEnd_5079012 2607974405953587575892055 := by
  unfold tailWord_5079012
  simp only [CollatzResearch.WordTrace]
  refine ⟨92623393137807212517691645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123497857517076283356922193 92623393137807212517691645)
  ·
    refine ⟨34733772426677704694134367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92623393137807212517691645 34733772426677704694134367)
    ·
      refine ⟨52100658640016557041201551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34733772426677704694134367 52100658640016557041201551)
      ·
        refine ⟨78150987960024835561802327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52100658640016557041201551 78150987960024835561802327)
        ·
          refine ⟨117226481940037253342703491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78150987960024835561802327 117226481940037253342703491)
          ·
            refine ⟨175839722910055880014055237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117226481940037253342703491 175839722910055880014055237)
            ·
              refine ⟨32969948045635477502635357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175839722910055880014055237 32969948045635477502635357)
              ·
                refine ⟨12363730517113304063488259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32969948045635477502635357 12363730517113304063488259)
                ·
                  refine ⟨18545595775669956095232389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12363730517113304063488259 18545595775669956095232389)
                  ·
                    refine ⟨3477299207938116767856073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18545595775669956095232389 3477299207938116767856073)
                    ·
                      refine ⟨2607974405953587575892055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477299207938116767856073 2607974405953587575892055)
                      ·
                        rfl

theorem cell23_5079012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_5079012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079012 prefixEnd_5079012 := by exact prefixLift 5079012
  have htrace : WordTrace (prefixWord ++ tailWord_5079012) baseStart_5079012 baseEnd_5079012 := by
    simpa [prefixWord, tailWord_5079012, baseEnd_5079012] using wordTrace_append hprefix tailTrace_5079012
  have hstable : (prefixWord ++ tailWord_5079012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079012).length < 2 ^ (prefixWord ++ tailWord_5079012).sum := by decide
  have hdescent : baseEnd_5079012 < baseStart_5079012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079052 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 5]
def baseStart_5079052 : Nat := 118140960795 + 5079052 * 2 ^ 59
def prefixEnd_5079052 : Nat := 4983230072969 + 3 ^ 40 * 5079052 * 2
def baseEnd_5079052 : Nat := 289777216131085268821319

theorem tailTrace_5079052 : CollatzResearch.WordTrace tailWord_5079052 prefixEnd_5079052 289777216131085268821319 := by
  unfold tailWord_5079052
  simp only [CollatzResearch.WordTrace]
  refine ⟨92624122597734755933419705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123498830130313007911226273 92624122597734755933419705)
  ·
    refine ⟨69468091948301066950064779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92624122597734755933419705 69468091948301066950064779)
    ·
      refine ⟨104202137922451600425097169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69468091948301066950064779 104202137922451600425097169)
      ·
        refine ⟨78151603441838700318822877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104202137922451600425097169 78151603441838700318822877)
        ·
          refine ⟨29306851290689512619558579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78151603441838700318822877 29306851290689512619558579)
          ·
            refine ⟨43960276936034268929337869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29306851290689512619558579 43960276936034268929337869)
            ·
              refine ⟨16485103851012850848501701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43960276936034268929337869 16485103851012850848501701)
              ·
                refine ⟨3090956972064909534094069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16485103851012850848501701 3090956972064909534094069)
                ·
                  refine ⟨289777216131085268821319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3090956972064909534094069 289777216131085268821319)
                  ·
                    rfl

theorem cell23_5079052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_5079052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079052 prefixEnd_5079052 := by exact prefixLift 5079052
  have htrace : WordTrace (prefixWord ++ tailWord_5079052) baseStart_5079052 baseEnd_5079052 := by
    simpa [prefixWord, tailWord_5079052, baseEnd_5079052] using wordTrace_append hprefix tailTrace_5079052
  have hstable : (prefixWord ++ tailWord_5079052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079052).length < 2 ^ (prefixWord ++ tailWord_5079052).sum := by decide
  have hdescent : baseEnd_5079052 < baseStart_5079052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079082 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_5079082 : Nat := 118140960795 + 5079082 * 2 ^ 59
def prefixEnd_5079082 : Nat := 4983230072969 + 3 ^ 40 * 5079082 * 2
def baseEnd_5079082 : Nat := 869336783199800767338911

theorem tailTrace_5079082 : CollatzResearch.WordTrace tailWord_5079082 prefixEnd_5079082 869336783199800767338911 := by
  unfold tailWord_5079082
  simp only [CollatzResearch.WordTrace]
  refine ⟨46312334846340206747607875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123499559590240551326954333 46312334846340206747607875)
  ·
    refine ⟨69468502269510310121411813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46312334846340206747607875 69468502269510310121411813)
    ·
      refine ⟨13025344175533183147764715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69468502269510310121411813 13025344175533183147764715)
      ·
        refine ⟨19538016263299774721647073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13025344175533183147764715 19538016263299774721647073)
        ·
          refine ⟨14653512197474831041235305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19538016263299774721647073 14653512197474831041235305)
          ·
            refine ⟨10990134148106123280926479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14653512197474831041235305 10990134148106123280926479)
            ·
              refine ⟨16485201222159184921389719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10990134148106123280926479 16485201222159184921389719)
              ·
                refine ⟨24727801833238777382084579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16485201222159184921389719 24727801833238777382084579)
                ·
                  refine ⟨37091702749858166073126869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24727801833238777382084579 37091702749858166073126869)
                  ·
                    refine ⟨869336783199800767338911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37091702749858166073126869 869336783199800767338911)
                    ·
                      rfl

theorem cell23_5079082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_5079082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079082 prefixEnd_5079082 := by exact prefixLift 5079082
  have htrace : WordTrace (prefixWord ++ tailWord_5079082) baseStart_5079082 baseEnd_5079082 := by
    simpa [prefixWord, tailWord_5079082, baseEnd_5079082] using wordTrace_append hprefix tailTrace_5079082
  have hstable : (prefixWord ++ tailWord_5079082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079082).length < 2 ^ (prefixWord ++ tailWord_5079082).sum := by decide
  have hdescent : baseEnd_5079082 < baseStart_5079082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2]
def baseStart_5079162 : Nat := 118140960795 + 5079162 * 2 ^ 59
def prefixEnd_5079162 : Nat := 4983230072969 + 3 ^ 40 * 5079162 * 2
def baseEnd_5079162 : Nat := 2608051428051761989016365

theorem tailTrace_5079162 : CollatzResearch.WordTrace tailWord_5079162 prefixEnd_5079162 2608051428051761989016365 := by
  unfold tailWord_5079162
  simp only [CollatzResearch.WordTrace]
  refine ⟨46313064306267750163335935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123501504816714000435562493 46313064306267750163335935)
  ·
    refine ⟨69469596459401625245003903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46313064306267750163335935 69469596459401625245003903)
    ·
      refine ⟨104204394689102437867505855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69469596459401625245003903 104204394689102437867505855)
      ·
        refine ⟨156306592033653656801258783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104204394689102437867505855 156306592033653656801258783)
        ·
          refine ⟨234459888050480485201888175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156306592033653656801258783 234459888050480485201888175)
          ·
            refine ⟨351689832075720727802832263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234459888050480485201888175 351689832075720727802832263)
            ·
              refine ⟨527534748113581091704248395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351689832075720727802832263 527534748113581091704248395)
              ·
                refine ⟨791302122170371637556372593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527534748113581091704248395 791302122170371637556372593)
                ·
                  refine ⟨593476591627778728167279445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791302122170371637556372593 593476591627778728167279445)
                  ·
                    refine ⟨3477401904069015985355153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 593476591627778728167279445 3477401904069015985355153)
                    ·
                      refine ⟨2608051428051761989016365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477401904069015985355153 2608051428051761989016365)
                      ·
                        rfl

theorem cell23_5079162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_5079162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079162 prefixEnd_5079162 := by exact prefixLift 5079162
  have htrace : WordTrace (prefixWord ++ tailWord_5079162) baseStart_5079162 baseEnd_5079162 := by
    simpa [prefixWord, tailWord_5079162, baseEnd_5079162] using wordTrace_append hprefix tailTrace_5079162
  have hstable : (prefixWord ++ tailWord_5079162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079162).length < 2 ^ (prefixWord ++ tailWord_5079162).sum := by decide
  have hdescent : baseEnd_5079162 < baseStart_5079162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079172 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_5079172 : Nat := 118140960795 + 5079172 * 2 ^ 59
def prefixEnd_5079172 : Nat := 4983230072969 + 3 ^ 40 * 5079172 * 2
def baseEnd_5079172 : Nat := 869352187619435649963773

theorem tailTrace_5079172 : CollatzResearch.WordTrace tailWord_5079172 prefixEnd_5079172 869352187619435649963773 := by
  unfold tailWord_5079172
  simp only [CollatzResearch.WordTrace]
  refine ⟨92626310977517386180603885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123501747970023181574138513 92626310977517386180603885)
  ·
    refine ⟨34734866616569019817726457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92626310977517386180603885 34734866616569019817726457)
    ·
      refine ⟨26051149962426764863294843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34734866616569019817726457 26051149962426764863294843)
      ·
        refine ⟨39076724943640147294942265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26051149962426764863294843 39076724943640147294942265)
        ·
          refine ⟨29307543707730110471206699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39076724943640147294942265 29307543707730110471206699)
          ·
            refine ⟨43961315561595165706810049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29307543707730110471206699 43961315561595165706810049)
            ·
              refine ⟨32970986671196374280107537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43961315561595165706810049 32970986671196374280107537)
              ·
                refine ⟨24728240003397280710080653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32970986671196374280107537 24728240003397280710080653)
                ·
                  refine ⟨9273090001273980266280245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24728240003397280710080653 9273090001273980266280245)
                  ·
                    refine ⟨869352187619435649963773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9273090001273980266280245 869352187619435649963773)
                    ·
                      rfl

theorem cell23_5079172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_5079172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079172 prefixEnd_5079172 := by exact prefixLift 5079172
  have htrace : WordTrace (prefixWord ++ tailWord_5079172) baseStart_5079172 baseEnd_5079172 := by
    simpa [prefixWord, tailWord_5079172, baseEnd_5079172] using wordTrace_append hprefix tailTrace_5079172
  have hstable : (prefixWord ++ tailWord_5079172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079172).length < 2 ^ (prefixWord ++ tailWord_5079172).sum := by decide
  have hdescent : baseEnd_5079172 < baseStart_5079172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079176 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 6]
def baseStart_5079176 : Nat := 118140960795 + 5079176 * 2 ^ 59
def prefixEnd_5079176 : Nat := 4983230072969 + 3 ^ 40 * 5079176 * 2
def baseEnd_5079176 : Nat := 289784290753436103804589

theorem tailTrace_5079176 : CollatzResearch.WordTrace tailWord_5079176 prefixEnd_5079176 289784290753436103804589 := by
  unfold tailWord_5079176
  simp only [CollatzResearch.WordTrace]
  refine ⟨92626383923510140522176691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123501845231346854029568921 92626383923510140522176691)
  ·
    refine ⟨138939575885265210783265037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92626383923510140522176691 138939575885265210783265037)
    ·
      refine ⟨52102340956974454043724389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138939575885265210783265037 52102340956974454043724389)
      ·
        refine ⟨9769188929432710133198323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52102340956974454043724389 9769188929432710133198323)
        ·
          refine ⟨14653783394149065199797485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9769188929432710133198323 14653783394149065199797485)
          ·
            refine ⟨5495168772805899449924057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14653783394149065199797485 5495168772805899449924057)
            ·
              refine ⟨4121376579604424587443043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495168772805899449924057 4121376579604424587443043)
              ·
                refine ⟨6182064869406636881164565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121376579604424587443043 6182064869406636881164565)
                ·
                  refine ⟨289784290753436103804589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6182064869406636881164565 289784290753436103804589)
                  ·
                    rfl

theorem cell23_5079176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 6].length) (baseStart_5079176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079176 prefixEnd_5079176 := by exact prefixLift 5079176
  have htrace : WordTrace (prefixWord ++ tailWord_5079176) baseStart_5079176 baseEnd_5079176 := by
    simpa [prefixWord, tailWord_5079176, baseEnd_5079176] using wordTrace_append hprefix tailTrace_5079176
  have hstable : (prefixWord ++ tailWord_5079176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079176).length < 2 ^ (prefixWord ++ tailWord_5079176).sum := by decide
  have hdescent : baseEnd_5079176 < baseStart_5079176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079185 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_5079185 : Nat := 118140960795 + 5079185 * 2 ^ 59
def prefixEnd_5079185 : Nat := 4983230072969 + 3 ^ 40 * 5079185 * 2
def baseEnd_5079185 : Nat := 869354412702271799676253

theorem tailTrace_5079185 : CollatzResearch.WordTrace tailWord_5079185 prefixEnd_5079185 869354412702271799676253 := by
  unfold tailWord_5079185
  simp only [CollatzResearch.WordTrace]
  refine ⟨185253096103987675581431009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123502064069325117054287339 185253096103987675581431009)
  ·
    refine ⟨138939822077990756686073257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185253096103987675581431009 138939822077990756686073257)
    ·
      refine ⟨104204866558493067514554943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138939822077990756686073257 104204866558493067514554943)
      ·
        refine ⟨156307299837739601271832415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104204866558493067514554943 156307299837739601271832415)
        ·
          refine ⟨234460949756609401907748623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156307299837739601271832415 234460949756609401907748623)
          ·
            refine ⟨351691424634914102861622935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234460949756609401907748623 351691424634914102861622935)
            ·
              refine ⟨527537136952371154292434403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351691424634914102861622935 527537136952371154292434403)
              ·
                refine ⟨791305705428556731438651605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527537136952371154292434403 791305705428556731438651605)
                ·
                  refine ⟨18546227470981798393093397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 791305705428556731438651605 18546227470981798393093397)
                  ·
                    refine ⟨869354412702271799676253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18546227470981798393093397 869354412702271799676253)
                    ·
                      rfl

theorem cell23_5079185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_5079185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079185 prefixEnd_5079185 := by exact prefixLift 5079185
  have htrace : WordTrace (prefixWord ++ tailWord_5079185) baseStart_5079185 baseEnd_5079185 := by
    simpa [prefixWord, tailWord_5079185, baseEnd_5079185] using wordTrace_append hprefix tailTrace_5079185
  have hstable : (prefixWord ++ tailWord_5079185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079185).length < 2 ^ (prefixWord ++ tailWord_5079185).sum := by decide
  have hdescent : baseEnd_5079185 < baseStart_5079185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079196 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5079196 : Nat := 118140960795 + 5079196 * 2 ^ 59
def prefixEnd_5079196 : Nat := 4983230072969 + 3 ^ 40 * 5079196 * 2
def baseEnd_5079196 : Nat := 2608068886394014855991209

theorem tailTrace_5079196 : CollatzResearch.WordTrace tailWord_5079196 prefixEnd_5079196 2608068886394014855991209 := by
  unfold tailWord_5079196
  simp only [CollatzResearch.WordTrace]
  refine ⟨92626748653473912230040721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123502331537965216306720961 92626748653473912230040721)
  ·
    refine ⟨69470061490105434172530541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92626748653473912230040721 69470061490105434172530541)
    ·
      refine ⟨26051273058789537814698953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69470061490105434172530541 26051273058789537814698953)
      ·
        refine ⟨19538454794092153361024215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26051273058789537814698953 19538454794092153361024215)
        ·
          refine ⟨29307682191138230041536323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19538454794092153361024215 29307682191138230041536323)
          ·
            refine ⟨43961523286707345062304485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29307682191138230041536323 43961523286707345062304485)
            ·
              refine ⟨8242785616257627199182091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43961523286707345062304485 8242785616257627199182091)
              ·
                refine ⟨12364178424386440798773137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8242785616257627199182091 12364178424386440798773137)
                ·
                  refine ⟨9273133818289830599079853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12364178424386440798773137 9273133818289830599079853)
                  ·
                    refine ⟨3477425181858686474654945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9273133818289830599079853 3477425181858686474654945)
                    ·
                      refine ⟨2608068886394014855991209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477425181858686474654945 2608068886394014855991209)
                      ·
                        rfl

theorem cell23_5079196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5079196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079196 prefixEnd_5079196 := by exact prefixLift 5079196
  have htrace : WordTrace (prefixWord ++ tailWord_5079196) baseStart_5079196 baseEnd_5079196 := by
    simpa [prefixWord, tailWord_5079196, baseEnd_5079196] using wordTrace_append hprefix tailTrace_5079196
  have hstable : (prefixWord ++ tailWord_5079196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079196).length < 2 ^ (prefixWord ++ tailWord_5079196).sum := by decide
  have hdescent : baseEnd_5079196 < baseStart_5079196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079214 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5079214 : Nat := 118140960795 + 5079214 * 2 ^ 59
def prefixEnd_5079214 : Nat := 4983230072969 + 3 ^ 40 * 5079214 * 2
def baseEnd_5079214 : Nat := 869359376348598595188709

theorem tailTrace_5079214 : CollatzResearch.WordTrace tailWord_5079214 prefixEnd_5079214 869359376348598595188709 := by
  unfold tailWord_5079214
  simp only [CollatzResearch.WordTrace]
  refine ⟨23156769227610326691779587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123502769213921742356157797 23156769227610326691779587)
  ·
    refine ⟨34735153841415490037669381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23156769227610326691779587 34735153841415490037669381)
    ·
      refine ⟨6512841345265404382063009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34735153841415490037669381 6512841345265404382063009)
      ·
        refine ⟨4884631008949053286547257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6512841345265404382063009 4884631008949053286547257)
        ·
          refine ⟨3663473256711789964910443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4884631008949053286547257 3663473256711789964910443)
          ·
            refine ⟨5495209885067684947365665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663473256711789964910443 5495209885067684947365665)
            ·
              refine ⟨4121407413800763710524249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495209885067684947365665 4121407413800763710524249)
              ·
                refine ⟨3091055560350572782893187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121407413800763710524249 3091055560350572782893187)
                ·
                  refine ⟨4636583340525859174339781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091055560350572782893187 4636583340525859174339781)
                  ·
                    refine ⟨869359376348598595188709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636583340525859174339781 869359376348598595188709)
                    ·
                      rfl

theorem cell23_5079214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5079214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079214 prefixEnd_5079214 := by exact prefixLift 5079214
  have htrace : WordTrace (prefixWord ++ tailWord_5079214) baseStart_5079214 baseEnd_5079214 := by
    simpa [prefixWord, tailWord_5079214, baseEnd_5079214] using wordTrace_append hprefix tailTrace_5079214
  have hstable : (prefixWord ++ tailWord_5079214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079214).length < 2 ^ (prefixWord ++ tailWord_5079214).sum := by decide
  have hdescent : baseEnd_5079214 < baseStart_5079214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079232 : List Nat := [2, 1, 1, 2, 5, 1, 3, 8]
def baseStart_5079232 : Nat := 118140960795 + 5079232 * 2 ^ 59
def prefixEnd_5079232 : Nat := 4983230072969 + 3 ^ 40 * 5079232 * 2
def baseEnd_5079232 : Nat := 96595828581391730190409

theorem tailTrace_5079232 : CollatzResearch.WordTrace tailWord_5079232 prefixEnd_5079232 96595828581391730190409 := by
  unfold tailWord_5079232
  simp only [CollatzResearch.WordTrace]
  refine ⟨92627405167408701304195975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123503206889878268405594633 92627405167408701304195975)
  ·
    refine ⟨138941107751113051956293963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92627405167408701304195975 138941107751113051956293963)
    ·
      refine ⟨208411661626669577934440945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138941107751113051956293963 208411661626669577934440945)
      ·
        refine ⟨156308746220002183450830709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208411661626669577934440945 156308746220002183450830709)
        ·
          refine ⟨14653944958125204698515379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156308746220002183450830709 14653944958125204698515379)
          ·
            refine ⟨21980917437187807047773069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14653944958125204698515379 21980917437187807047773069)
            ·
              refine ⟨8242844038945427642914901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21980917437187807047773069 8242844038945427642914901)
              ·
                refine ⟨96595828581391730190409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8242844038945427642914901 96595828581391730190409)
                ·
                  rfl

theorem cell23_5079232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 8].length) (baseStart_5079232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079232 prefixEnd_5079232 := by exact prefixLift 5079232
  have htrace : WordTrace (prefixWord ++ tailWord_5079232) baseStart_5079232 baseEnd_5079232 := by
    simpa [prefixWord, tailWord_5079232, baseEnd_5079232] using wordTrace_append hprefix tailTrace_5079232
  have hstable : (prefixWord ++ tailWord_5079232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079232).length < 2 ^ (prefixWord ++ tailWord_5079232).sum := by decide
  have hdescent : baseEnd_5079232 < baseStart_5079232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079236 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5079236 : Nat := 118140960795 + 5079236 * 2 ^ 59
def prefixEnd_5079236 : Nat := 4983230072969 + 3 ^ 40 * 5079236 * 2
def baseEnd_5079236 : Nat := 869363141873398233163675

theorem tailTrace_5079236 : CollatzResearch.WordTrace tailWord_5079236 prefixEnd_5079236 869363141873398233163675 := by
  unfold tailWord_5079236
  simp only [CollatzResearch.WordTrace]
  refine ⟨92627478113401455645768781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123503304151201940861025041 92627478113401455645768781)
  ·
    refine ⟨34735304292525545867163293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92627478113401455645768781 34735304292525545867163293)
    ·
      refine ⟨13025739109697079700186235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34735304292525545867163293 13025739109697079700186235)
      ·
        refine ⟨19538608664545619550279353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13025739109697079700186235 19538608664545619550279353)
        ·
          refine ⟨14653956498409214662709515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19538608664545619550279353 14653956498409214662709515)
          ·
            refine ⟨21980934747613821994064273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14653956498409214662709515 21980934747613821994064273)
            ·
              refine ⟨16485701060710366495548205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21980934747613821994064273 16485701060710366495548205)
              ·
                refine ⟨6182137897766387435830577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16485701060710366495548205 6182137897766387435830577)
                ·
                  refine ⟨4636603423324790576872933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6182137897766387435830577 4636603423324790576872933)
                  ·
                    refine ⟨869363141873398233163675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636603423324790576872933 869363141873398233163675)
                    ·
                      rfl

theorem cell23_5079236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5079236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079236 prefixEnd_5079236 := by exact prefixLift 5079236
  have htrace : WordTrace (prefixWord ++ tailWord_5079236) baseStart_5079236 baseEnd_5079236 := by
    simpa [prefixWord, tailWord_5079236, baseEnd_5079236] using wordTrace_append hprefix tailTrace_5079236
  have hstable : (prefixWord ++ tailWord_5079236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079236).length < 2 ^ (prefixWord ++ tailWord_5079236).sum := by decide
  have hdescent : baseEnd_5079236 < baseStart_5079236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079286 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_5079286 : Nat := 118140960795 + 5079286 * 2 ^ 59
def prefixEnd_5079286 : Nat := 4983230072969 + 3 ^ 40 * 5079286 * 2
def baseEnd_5079286 : Nat := 2608115099652919503865795

theorem tailTrace_5079286 : CollatzResearch.WordTrace tailWord_5079286 prefixEnd_5079286 2608115099652919503865795 := by
  unfold tailWord_5079286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11578548742288860614428607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123504519917747846553905141 11578548742288860614428607)
  ·
    refine ⟨17367823113433290921642911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11578548742288860614428607 17367823113433290921642911)
    ·
      refine ⟨26051734670149936382464367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17367823113433290921642911 26051734670149936382464367)
      ·
        refine ⟨39077602005224904573696551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26051734670149936382464367 39077602005224904573696551)
        ·
          refine ⟨58616403007837356860544827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39077602005224904573696551 58616403007837356860544827)
          ·
            refine ⟨87924604511756035290817241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58616403007837356860544827 87924604511756035290817241)
            ·
              refine ⟨65943453383817026468112931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87924604511756035290817241 65943453383817026468112931)
              ·
                refine ⟨98915180075725539702169397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65943453383817026468112931 98915180075725539702169397)
                ·
                  refine ⟨9273298132099269347078381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98915180075725539702169397 9273298132099269347078381)
                  ·
                    refine ⟨3477486799537226005154393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9273298132099269347078381 3477486799537226005154393)
                    ·
                      refine ⟨2608115099652919503865795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477486799537226005154393 2608115099652919503865795)
                      ·
                        rfl

theorem cell23_5079286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_5079286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079286 prefixEnd_5079286 := by exact prefixLift 5079286
  have htrace : WordTrace (prefixWord ++ tailWord_5079286) baseStart_5079286 baseEnd_5079286 := by
    simpa [prefixWord, tailWord_5079286, baseEnd_5079286] using wordTrace_append hprefix tailTrace_5079286
  have hstable : (prefixWord ++ tailWord_5079286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079286).length < 2 ^ (prefixWord ++ tailWord_5079286).sum := by decide
  have hdescent : baseEnd_5079286 < baseStart_5079286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079319 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5079319 : Nat := 118140960795 + 5079319 * 2 ^ 59
def prefixEnd_5079319 : Nat := 4983230072969 + 3 ^ 40 * 5079319 * 2
def baseEnd_5079319 : Nat := 2608132044514517874753143

theorem tailTrace_5079319 : CollatzResearch.WordTrace tailWord_5079319 prefixEnd_5079319 2608132044514517874753143 := by
  unfold tailWord_5079319
  simp only [CollatzResearch.WordTrace]
  refine ⟨185257983485502216466809011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123505322323668144311206007 185257983485502216466809011)
  ·
    refine ⟨277886975228253324700213517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185257983485502216466809011 277886975228253324700213517)
    ·
      refine ⟨104207615710594996762580069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277886975228253324700213517 104207615710594996762580069)
      ·
        refine ⟨19538927945736561892983763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104207615710594996762580069 19538927945736561892983763)
        ·
          refine ⟨29308391918604842839475645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19538927945736561892983763 29308391918604842839475645)
          ·
            refine ⟨10990646969476816064803367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29308391918604842839475645 10990646969476816064803367)
            ·
              refine ⟨16485970454215224097205051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10990646969476816064803367 16485970454215224097205051)
              ·
                refine ⟨24728955681322836145807577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16485970454215224097205051 24728955681322836145807577)
                ·
                  refine ⟨18546716760992127109355683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24728955681322836145807577 18546716760992127109355683)
                  ·
                    refine ⟨27820075141488190664033525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18546716760992127109355683 27820075141488190664033525)
                    ·
                      refine ⟨2608132044514517874753143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27820075141488190664033525 2608132044514517874753143)
                      ·
                        rfl

theorem cell23_5079319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5079319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079319 prefixEnd_5079319 := by exact prefixLift 5079319
  have htrace : WordTrace (prefixWord ++ tailWord_5079319) baseStart_5079319 baseEnd_5079319 := by
    simpa [prefixWord, tailWord_5079319, baseEnd_5079319] using wordTrace_append hprefix tailTrace_5079319
  have hstable : (prefixWord ++ tailWord_5079319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079319).length < 2 ^ (prefixWord ++ tailWord_5079319).sum := by decide
  have hdescent : baseEnd_5079319 < baseStart_5079319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079349 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_5079349 : Nat := 118140960795 + 5079349 * 2 ^ 59
def prefixEnd_5079349 : Nat := 4983230072969 + 3 ^ 40 * 5079349 * 2
def baseEnd_5079349 : Nat := 2608147448934152757378005

theorem tailTrace_5079349 : CollatzResearch.WordTrace tailWord_5079349 prefixEnd_5079349 2608147448934152757378005 := by
  unfold tailWord_5079349
  simp only [CollatzResearch.WordTrace]
  refine ⟨185259077675393531590401101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123506051783595687726934067 185259077675393531590401101)
  ·
    refine ⟨69472154128272574346400413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185259077675393531590401101 69472154128272574346400413)
    ·
      refine ⟨26052057798102215379900155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69472154128272574346400413 26052057798102215379900155)
      ·
        refine ⟨39078086697153323069850233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26052057798102215379900155 39078086697153323069850233)
        ·
          refine ⟨29308565022864992302387675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39078086697153323069850233 29308565022864992302387675)
          ·
            refine ⟨43962847534297488453581513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29308565022864992302387675 43962847534297488453581513)
            ·
              refine ⟨32972135650723116340186135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43962847534297488453581513 32972135650723116340186135)
              ·
                refine ⟨49458203476084674510279203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32972135650723116340186135 49458203476084674510279203)
                ·
                  refine ⟨74187305214127011765418805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49458203476084674510279203 74187305214127011765418805)
                  ·
                    refine ⟨6955059863824407353008013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74187305214127011765418805 6955059863824407353008013)
                    ·
                      refine ⟨2608147448934152757378005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955059863824407353008013 2608147448934152757378005)
                      ·
                        rfl

theorem cell23_5079349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_5079349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079349 prefixEnd_5079349 := by exact prefixLift 5079349
  have htrace : WordTrace (prefixWord ++ tailWord_5079349) baseStart_5079349 baseEnd_5079349 := by
    simpa [prefixWord, tailWord_5079349, baseEnd_5079349] using wordTrace_append hprefix tailTrace_5079349
  have hstable : (prefixWord ++ tailWord_5079349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079349).length < 2 ^ (prefixWord ++ tailWord_5079349).sum := by decide
  have hdescent : baseEnd_5079349 < baseStart_5079349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079352 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_5079352 : Nat := 118140960795 + 5079352 * 2 ^ 59
def prefixEnd_5079352 : Nat := 4983230072969 + 3 ^ 40 * 5079352 * 2
def baseEnd_5079352 : Nat := 869382996458705415213497

theorem tailTrace_5079352 : CollatzResearch.WordTrace tailWord_5079352 prefixEnd_5079352 869382996458705415213497 := by
  unfold tailWord_5079352
  simp only [CollatzResearch.WordTrace]
  refine ⟨92629593547191331551380155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123506124729588442068506873 92629593547191331551380155)
  ·
    refine ⟨138944390320786997327070233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92629593547191331551380155 138944390320786997327070233)
    ·
      refine ⟨104208292740590247995302675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138944390320786997327070233 104208292740590247995302675)
      ·
        refine ⟨156312439110885371992954013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104208292740590247995302675 156312439110885371992954013)
        ·
          refine ⟨58617164666582014497357755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156312439110885371992954013 58617164666582014497357755)
          ·
            refine ⟨87925746999873021746036633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58617164666582014497357755 87925746999873021746036633)
            ·
              refine ⟨65944310249904766309527475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87925746999873021746036633 65944310249904766309527475)
              ·
                refine ⟨98916465374857149464291213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65944310249904766309527475 98916465374857149464291213)
                ·
                  refine ⟨37093674515571431049109205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98916465374857149464291213 37093674515571431049109205)
                  ·
                    refine ⟨869382996458705415213497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37093674515571431049109205 869382996458705415213497)
                    ·
                      rfl

theorem cell23_5079352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_5079352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079352 prefixEnd_5079352 := by exact prefixLift 5079352
  have htrace : WordTrace (prefixWord ++ tailWord_5079352) baseStart_5079352 baseEnd_5079352 := by
    simpa [prefixWord, tailWord_5079352, baseEnd_5079352] using wordTrace_append hprefix tailTrace_5079352
  have hstable : (prefixWord ++ tailWord_5079352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079352).length < 2 ^ (prefixWord ++ tailWord_5079352).sum := by decide
  have hdescent : baseEnd_5079352 < baseStart_5079352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079409 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_5079409 : Nat := 118140960795 + 5079409 * 2 ^ 59
def prefixEnd_5079409 : Nat := 4983230072969 + 3 ^ 40 * 5079409 * 2
def baseEnd_5079409 : Nat := 2608178257773422522627729

theorem tailTrace_5079409 : CollatzResearch.WordTrace tailWord_5079409 prefixEnd_5079409 2608178257773422522627729 := by
  unfold tailWord_5079409
  simp only [CollatzResearch.WordTrace]
  refine ⟨185261266055176161837585281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123507510703450774558390187 185261266055176161837585281)
  ·
    refine ⟨138945949541382121378188961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185261266055176161837585281 138945949541382121378188961)
    ·
      refine ⟨104209462156036591033641721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138945949541382121378188961 104209462156036591033641721)
      ·
        refine ⟨78157096617027443275231291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104209462156036591033641721 78157096617027443275231291)
        ·
          refine ⟨117235644925541164912846937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78157096617027443275231291 117235644925541164912846937)
          ·
            refine ⟨87926733694155873684635203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117235644925541164912846937 87926733694155873684635203)
            ·
              refine ⟨131890100541233810526952805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87926733694155873684635203 131890100541233810526952805)
              ·
                refine ⟨24729393851481339473803651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131890100541233810526952805 24729393851481339473803651)
                ·
                  refine ⟨37094090777222009210705477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24729393851481339473803651 37094090777222009210705477)
                  ·
                    refine ⟨6955142020729126727007277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37094090777222009210705477 6955142020729126727007277)
                    ·
                      refine ⟨2608178257773422522627729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955142020729126727007277 2608178257773422522627729)
                      ·
                        rfl

theorem cell23_5079409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_5079409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079409 prefixEnd_5079409 := by exact prefixLift 5079409
  have htrace : WordTrace (prefixWord ++ tailWord_5079409) baseStart_5079409 baseEnd_5079409 := by
    simpa [prefixWord, tailWord_5079409, baseEnd_5079409] using wordTrace_append hprefix tailTrace_5079409
  have hstable : (prefixWord ++ tailWord_5079409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079409).length < 2 ^ (prefixWord ++ tailWord_5079409).sum := by decide
  have hdescent : baseEnd_5079409 < baseStart_5079409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079433 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 1, 4]
def baseStart_5079433 : Nat := 118140960795 + 5079433 * 2 ^ 59
def prefixEnd_5079433 : Nat := 4983230072969 + 3 ^ 40 * 5079433 * 2
def baseEnd_5079433 : Nat := 869396860436376809575873

theorem tailTrace_5079433 : CollatzResearch.WordTrace tailWord_5079433 prefixEnd_5079433 869396860436376809575873 := by
  unfold tailWord_5079433
  simp only [CollatzResearch.WordTrace]
  refine ⟨185262141407089213936458953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123508094271392809290972635 185262141407089213936458953)
  ·
    refine ⟨138946606055316910452344215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185262141407089213936458953 138946606055316910452344215)
    ·
      refine ⟨208419909082975365678516323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138946606055316910452344215 208419909082975365678516323)
      ·
        refine ⟨312629863624463048517774485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208419909082975365678516323 312629863624463048517774485)
        ·
          refine ⟨14654524857396705399270679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 312629863624463048517774485 14654524857396705399270679)
          ·
            refine ⟨21981787286095058098906019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14654524857396705399270679 21981787286095058098906019)
            ·
              refine ⟨32972680929142587148359029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21981787286095058098906019 32972680929142587148359029)
              ·
                refine ⟨3091188837107117545158659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32972680929142587148359029 3091188837107117545158659)
                ·
                  refine ⟨4636783255660676317737989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091188837107117545158659 4636783255660676317737989)
                  ·
                    refine ⟨869396860436376809575873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4636783255660676317737989 869396860436376809575873)
                    ·
                      rfl

theorem cell23_5079433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 4].length) (baseStart_5079433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079433 prefixEnd_5079433 := by exact prefixLift 5079433
  have htrace : WordTrace (prefixWord ++ tailWord_5079433) baseStart_5079433 baseEnd_5079433 := by
    simpa [prefixWord, tailWord_5079433, baseEnd_5079433] using wordTrace_append hprefix tailTrace_5079433
  have hstable : (prefixWord ++ tailWord_5079433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079433).length < 2 ^ (prefixWord ++ tailWord_5079433).sum := by decide
  have hdescent : baseEnd_5079433 < baseStart_5079433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079463 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 6]
def baseStart_5079463 : Nat := 118140960795 + 5079463 * 2 ^ 59
def prefixEnd_5079463 : Nat := 4983230072969 + 3 ^ 40 * 5079463 * 2
def baseEnd_5079463 : Nat := 289800665080973923483609

theorem tailTrace_5079463 : CollatzResearch.WordTrace tailWord_5079463 prefixEnd_5079463 289800665080973923483609 := by
  unfold tailWord_5079463
  simp only [CollatzResearch.WordTrace]
  refine ⟨185263235596980529060051043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123508823731320352706700695 185263235596980529060051043)
  ·
    refine ⟨277894853395470793590076565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185263235596980529060051043 277894853395470793590076565)
    ·
      refine ⟨13026321252912693449534839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 277894853395470793590076565 13026321252912693449534839)
      ·
        refine ⟨19539481879369040174302259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13026321252912693449534839 19539481879369040174302259)
        ·
          refine ⟨29309222819053560261453389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19539481879369040174302259 29309222819053560261453389)
          ·
            refine ⟨10990958557145085098045021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29309222819053560261453389 10990958557145085098045021)
            ·
              refine ⟨4121609458929406911766883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10990958557145085098045021 4121609458929406911766883)
              ·
                refine ⟨6182414188394110367650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121609458929406911766883 6182414188394110367650325)
                ·
                  refine ⟨289800665080973923483609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6182414188394110367650325 289800665080973923483609)
                  ·
                    rfl

theorem cell23_5079463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 6].length) (baseStart_5079463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079463 prefixEnd_5079463 := by exact prefixLift 5079463
  have htrace : WordTrace (prefixWord ++ tailWord_5079463) baseStart_5079463 baseEnd_5079463 := by
    simpa [prefixWord, tailWord_5079463, baseEnd_5079463] using wordTrace_append hprefix tailTrace_5079463
  have hstable : (prefixWord ++ tailWord_5079463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079463).length < 2 ^ (prefixWord ++ tailWord_5079463).sum := by decide
  have hdescent : baseEnd_5079463 < baseStart_5079463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079473 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5079473 : Nat := 118140960795 + 5079473 * 2 ^ 59
def prefixEnd_5079473 : Nat := 4983230072969 + 3 ^ 40 * 5079473 * 2
def baseEnd_5079473 : Nat := 2608211120535310272227435

theorem tailTrace_5079473 : CollatzResearch.WordTrace tailWord_5079473 prefixEnd_5079473 2608211120535310272227435 := by
  unfold tailWord_5079473
  simp only [CollatzResearch.WordTrace]
  refine ⟨185263600326944300767915073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123509066884629533845276715 185263600326944300767915073)
  ·
    refine ⟨138947700245208225575936305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185263600326944300767915073 138947700245208225575936305)
    ·
      refine ⟨104210775183906169181952229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138947700245208225575936305 104210775183906169181952229)
      ·
        refine ⟨19539520346982406721616043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104210775183906169181952229 19539520346982406721616043)
        ·
          refine ⟨29309280520473610082424065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19539520346982406721616043 29309280520473610082424065)
          ·
            refine ⟨21981960390355207561818049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29309280520473610082424065 21981960390355207561818049)
            ·
              refine ⟨16486470292766405671363537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21981960390355207561818049 16486470292766405671363537)
              ·
                refine ⟨12364852719574804253522653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16486470292766405671363537 12364852719574804253522653)
                ·
                  refine ⟨4636819769840551595070995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12364852719574804253522653 4636819769840551595070995)
                  ·
                    refine ⟨6955229654760827392606493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4636819769840551595070995 6955229654760827392606493)
                    ·
                      refine ⟨2608211120535310272227435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955229654760827392606493 2608211120535310272227435)
                      ·
                        rfl

theorem cell23_5079473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5079473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079473 prefixEnd_5079473 := by exact prefixLift 5079473
  have htrace : WordTrace (prefixWord ++ tailWord_5079473) baseStart_5079473 baseEnd_5079473 := by
    simpa [prefixWord, tailWord_5079473, baseEnd_5079473] using wordTrace_append hprefix tailTrace_5079473
  have hstable : (prefixWord ++ tailWord_5079473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079473).length < 2 ^ (prefixWord ++ tailWord_5079473).sum := by decide
  have hdescent : baseEnd_5079473 < baseStart_5079473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079500 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5079500 : Nat := 118140960795 + 5079500 * 2 ^ 59
def prefixEnd_5079500 : Nat := 4983230072969 + 3 ^ 40 * 5079500 * 2
def baseEnd_5079500 : Nat := 2608224984512981666589811

theorem tailTrace_5079500 : CollatzResearch.WordTrace tailWord_5079500 prefixEnd_5079500 2608224984512981666589811 := by
  unfold tailWord_5079500
  simp only [CollatzResearch.WordTrace]
  refine ⟨92632292548923242189573977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123509723398564322919431969 92632292548923242189573977)
  ·
    refine ⟨69474219411692431642180483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92632292548923242189573977 69474219411692431642180483)
    ·
      refine ⟨104211329117538647463270725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69474219411692431642180483 104211329117538647463270725)
      ·
        refine ⟨19539624209538496399363261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104211329117538647463270725 19539624209538496399363261)
        ·
          refine ⟨7327359078576936149761223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19539624209538496399363261 7327359078576936149761223)
          ·
            refine ⟨10991038617865404224641835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7327359078576936149761223 10991038617865404224641835)
            ·
              refine ⟨16486557926798106336962753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10991038617865404224641835 16486557926798106336962753)
              ·
                refine ⟨12364918445098579752722065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16486557926798106336962753 12364918445098579752722065)
                ·
                  refine ⟨9273688833823934814541549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12364918445098579752722065 9273688833823934814541549)
                  ·
                    refine ⟨3477633312683975555453081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9273688833823934814541549 3477633312683975555453081)
                    ·
                      refine ⟨2608224984512981666589811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477633312683975555453081 2608224984512981666589811)
                      ·
                        rfl

theorem cell23_5079500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5079500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079500 prefixEnd_5079500 := by exact prefixLift 5079500
  have htrace : WordTrace (prefixWord ++ tailWord_5079500) baseStart_5079500 baseEnd_5079500 := by
    simpa [prefixWord, tailWord_5079500, baseEnd_5079500] using wordTrace_append hprefix tailTrace_5079500
  have hstable : (prefixWord ++ tailWord_5079500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079500).length < 2 ^ (prefixWord ++ tailWord_5079500).sum := by decide
  have hdescent : baseEnd_5079500 < baseStart_5079500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079519 : List Nat := [1, 1, 2, 3, 3, 2, 1, 10]
def baseStart_5079519 : Nat := 118140960795 + 5079519 * 2 ^ 59
def prefixEnd_5079519 : Nat := 4983230072969 + 3 ^ 40 * 5079519 * 2
def baseEnd_5079519 : Nat := 96601286690571003416749

theorem tailTrace_5079519 : CollatzResearch.WordTrace tailWord_5079519 prefixEnd_5079519 96601286690571003416749 := by
  unfold tailWord_5079519
  simp only [CollatzResearch.WordTrace]
  refine ⟨185265278084777650624089611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123510185389851767082726407 185265278084777650624089611)
  ·
    refine ⟨277897917127166475936134417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185265278084777650624089611 277897917127166475936134417)
    ·
      refine ⟨208423437845374856952100813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277897917127166475936134417 208423437845374856952100813)
      ·
        refine ⟨78158789192015571357037805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208423437845374856952100813 78158789192015571357037805)
        ·
          refine ⟨29309545947005839258889177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78158789192015571357037805 29309545947005839258889177)
          ·
            refine ⟨21982159460254379444166883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29309545947005839258889177 21982159460254379444166883)
            ·
              refine ⟨32973239190381569166250325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21982159460254379444166883 32973239190381569166250325)
              ·
                refine ⟨96601286690571003416749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32973239190381569166250325 96601286690571003416749)
                ·
                  rfl

theorem cell23_5079519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 10].length) (baseStart_5079519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079519 prefixEnd_5079519 := by exact prefixLift 5079519
  have htrace : WordTrace (prefixWord ++ tailWord_5079519) baseStart_5079519 baseEnd_5079519 := by
    simpa [prefixWord, tailWord_5079519, baseEnd_5079519] using wordTrace_append hprefix tailTrace_5079519
  have hstable : (prefixWord ++ tailWord_5079519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079519).length < 2 ^ (prefixWord ++ tailWord_5079519).sum := by decide
  have hdescent : baseEnd_5079519 < baseStart_5079519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079530 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_5079530 : Nat := 118140960795 + 5079530 * 2 ^ 59
def prefixEnd_5079530 : Nat := 4983230072969 + 3 ^ 40 * 5079530 * 2
def baseEnd_5079530 : Nat := 2608240388932616549214673

theorem tailTrace_5079530 : CollatzResearch.WordTrace tailWord_5079530 prefixEnd_5079530 2608240388932616549214673 := by
  unfold tailWord_5079530
  simp only [CollatzResearch.WordTrace]
  refine ⟨46316419821934449875685011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123510452858491866335160029 46316419821934449875685011)
  ·
    refine ⟨69474629732901674813527517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46316419821934449875685011 69474629732901674813527517)
    ·
      refine ⟨26052986149838128055072819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69474629732901674813527517 26052986149838128055072819)
      ·
        refine ⟨39079479224757192082609229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26052986149838128055072819 39079479224757192082609229)
        ·
          refine ⟨14654804709283947030978461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39079479224757192082609229 14654804709283947030978461)
          ·
            refine ⟨5495551765981480136616923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14654804709283947030978461 5495551765981480136616923)
            ·
              refine ⟨8243327648972220204925385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495551765981480136616923 8243327648972220204925385)
              ·
                refine ⟨6182495736729165153694039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8243327648972220204925385 6182495736729165153694039)
                ·
                  refine ⟨9273743605093747730541059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6182495736729165153694039 9273743605093747730541059)
                  ·
                    refine ⟨13910615407640621595811589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9273743605093747730541059 13910615407640621595811589)
                    ·
                      refine ⟨2608240388932616549214673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13910615407640621595811589 2608240388932616549214673)
                      ·
                        rfl

theorem cell23_5079530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_5079530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079530 prefixEnd_5079530 := by exact prefixLift 5079530
  have htrace : WordTrace (prefixWord ++ tailWord_5079530) baseStart_5079530 baseEnd_5079530 := by
    simpa [prefixWord, tailWord_5079530, baseEnd_5079530] using wordTrace_append hprefix tailTrace_5079530
  have hstable : (prefixWord ++ tailWord_5079530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079530).length < 2 ^ (prefixWord ++ tailWord_5079530).sum := by decide
  have hdescent : baseEnd_5079530 < baseStart_5079530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079558 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_5079558 : Nat := 118140960795 + 5079558 * 2 ^ 59
def prefixEnd_5079558 : Nat := 4983230072969 + 3 ^ 40 * 5079558 * 2
def baseEnd_5079558 : Nat := 2608254766390942439664545

theorem tailTrace_5079558 : CollatzResearch.WordTrace tailWord_5079558 prefixEnd_5079558 2608254766390942439664545 := by
  unfold tailWord_5079558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789584391613636258898729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123511133687757573523172885 5789584391613636258898729)
  ·
    refine ⟨4342188293710227194174047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5789584391613636258898729 4342188293710227194174047)
    ·
      refine ⟨6513282440565340791261071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342188293710227194174047 6513282440565340791261071)
      ·
        refine ⟨9769923660848011186891607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6513282440565340791261071 9769923660848011186891607)
        ·
          refine ⟨14654885491272016780337411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9769923660848011186891607 14654885491272016780337411)
          ·
            refine ⟨21982328236908025170506117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14654885491272016780337411 21982328236908025170506117)
            ·
              refine ⟨4121686544420254719469897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21982328236908025170506117 4121686544420254719469897)
              ·
                refine ⟨3091264908315191039602423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121686544420254719469897 3091264908315191039602423)
                ·
                  refine ⟨4636897362472786559403635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091264908315191039602423 4636897362472786559403635)
                  ·
                    refine ⟨6955346043709179839105453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4636897362472786559403635 6955346043709179839105453)
                    ·
                      refine ⟨2608254766390942439664545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955346043709179839105453 2608254766390942439664545)
                      ·
                        rfl

theorem cell23_5079558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_5079558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079558 prefixEnd_5079558 := by exact prefixLift 5079558
  have htrace : WordTrace (prefixWord ++ tailWord_5079558) baseStart_5079558 baseEnd_5079558 := by
    simpa [prefixWord, tailWord_5079558, baseEnd_5079558] using wordTrace_append hprefix tailTrace_5079558
  have hstable : (prefixWord ++ tailWord_5079558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079558).length < 2 ^ (prefixWord ++ tailWord_5079558).sum := by decide
  have hdescent : baseEnd_5079558 < baseStart_5079558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079564 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 1, 2, 2]
def baseStart_5079564 : Nat := 118140960795 + 5079564 * 2 ^ 59
def prefixEnd_5079564 : Nat := 4983230072969 + 3 ^ 40 * 5079564 * 2
def baseEnd_5079564 : Nat := 2608257847274869416189517

theorem tailTrace_5079564 : CollatzResearch.WordTrace tailWord_5079564 prefixEnd_5079564 2608257847274869416189517 := by
  unfold tailWord_5079564
  simp only [CollatzResearch.WordTrace]
  refine ⟨92633459684807311654738873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123511279579743082206318497 92633459684807311654738873)
  ·
    refine ⟨69475094763605483741054155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92633459684807311654738873 69475094763605483741054155)
    ·
      refine ⟨104212642145408225611581233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69475094763605483741054155 104212642145408225611581233)
      ·
        refine ⟨78159481609056169208685925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104212642145408225611581233 78159481609056169208685925)
        ·
          refine ⟨14654902801698031726628611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78159481609056169208685925 14654902801698031726628611)
          ·
            refine ⟨21982354202547047589942917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14654902801698031726628611 21982354202547047589942917)
            ·
              refine ⟨4121691412977571423114297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21982354202547047589942917 4121691412977571423114297)
              ·
                refine ⟨3091268559733178567335723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121691412977571423114297 3091268559733178567335723)
                ·
                  refine ⟨4636902839599767851003585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091268559733178567335723 4636902839599767851003585)
                  ·
                    refine ⟨3477677129699825888252689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4636902839599767851003585 3477677129699825888252689)
                    ·
                      refine ⟨2608257847274869416189517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477677129699825888252689 2608257847274869416189517)
                      ·
                        rfl

theorem cell23_5079564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_5079564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079564 prefixEnd_5079564 := by exact prefixLift 5079564
  have htrace : WordTrace (prefixWord ++ tailWord_5079564) baseStart_5079564 baseEnd_5079564 := by
    simpa [prefixWord, tailWord_5079564, baseEnd_5079564] using wordTrace_append hprefix tailTrace_5079564
  have hstable : (prefixWord ++ tailWord_5079564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079564).length < 2 ^ (prefixWord ++ tailWord_5079564).sum := by decide
  have hdescent : baseEnd_5079564 < baseStart_5079564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079566 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_5079566 : Nat := 118140960795 + 5079566 * 2 ^ 59
def prefixEnd_5079566 : Nat := 4983230072969 + 3 ^ 40 * 5079566 * 2
def baseEnd_5079566 : Nat := 869419624745392802788169

theorem tailTrace_5079566 : CollatzResearch.WordTrace tailWord_5079566 prefixEnd_5079566 869419624745392802788169 := by
  unfold tailWord_5079566
  simp only [CollatzResearch.WordTrace]
  refine ⟨23158374039450922206381319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123511328210404918434033701 23158374039450922206381319)
  ·
    refine ⟨34737561059176383309571979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23158374039450922206381319 34737561059176383309571979)
    ·
      refine ⟨52106341588764574964357969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34737561059176383309571979 52106341588764574964357969)
      ·
        refine ⟨39079756191573431223268477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52106341588764574964357969 39079756191573431223268477)
        ·
          refine ⟨14654908571840036708725679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39079756191573431223268477 14654908571840036708725679)
          ·
            refine ⟨21982362857760055063088519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14654908571840036708725679 21982362857760055063088519)
            ·
              refine ⟨32973544286640082594632779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21982362857760055063088519 32973544286640082594632779)
              ·
                refine ⟨49460316429960123891949169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32973544286640082594632779 49460316429960123891949169)
                ·
                  refine ⟨37095237322470092918961877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49460316429960123891949169 37095237322470092918961877)
                  ·
                    refine ⟨869419624745392802788169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37095237322470092918961877 869419624745392802788169)
                    ·
                      rfl

theorem cell23_5079566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_5079566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079566 prefixEnd_5079566 := by exact prefixLift 5079566
  have htrace : WordTrace (prefixWord ++ tailWord_5079566) baseStart_5079566 baseEnd_5079566 := by
    simpa [prefixWord, tailWord_5079566, baseEnd_5079566] using wordTrace_append hprefix tailTrace_5079566
  have hstable : (prefixWord ++ tailWord_5079566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079566).length < 2 ^ (prefixWord ++ tailWord_5079566).sum := by decide
  have hdescent : baseEnd_5079566 < baseStart_5079566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079573 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_5079573 : Nat := 118140960795 + 5079573 * 2 ^ 59
def prefixEnd_5079573 : Nat := 4983230072969 + 3 ^ 40 * 5079573 * 2
def baseEnd_5079573 : Nat := 2608262468600759880976975

theorem tailTrace_5079573 : CollatzResearch.WordTrace tailWord_5079573 prefixEnd_5079573 2608262468600759880976975 := by
  unfold tailWord_5079573
  simp only [CollatzResearch.WordTrace]
  refine ⟨185267247626582017846555373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123511498417721345231036915 185267247626582017846555373)
  ·
    refine ⟨69475217859968256692458265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185267247626582017846555373 69475217859968256692458265)
    ·
      refine ⟨52106413394976192519343699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69475217859968256692458265 52106413394976192519343699)
      ·
        refine ⟨78159620092464288779015549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52106413394976192519343699 78159620092464288779015549)
        ·
          refine ⟨29309857534674108292130831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78159620092464288779015549 29309857534674108292130831)
          ·
            refine ⟨43964786302011162438196247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29309857534674108292130831 43964786302011162438196247)
            ·
              refine ⟨65947179453016743657294371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43964786302011162438196247 65947179453016743657294371)
              ·
                refine ⟨98920769179525115485941557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65947179453016743657294371 98920769179525115485941557)
                ·
                  refine ⟨9273822110580479576807021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98920769179525115485941557 9273822110580479576807021)
                  ·
                    refine ⟨3477683291467679841302633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9273822110580479576807021 3477683291467679841302633)
                    ·
                      refine ⟨2608262468600759880976975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477683291467679841302633 2608262468600759880976975)
                      ·
                        rfl

theorem cell23_5079573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_5079573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079573 prefixEnd_5079573 := by exact prefixLift 5079573
  have htrace : WordTrace (prefixWord ++ tailWord_5079573) baseStart_5079573 baseEnd_5079573 := by
    simpa [prefixWord, tailWord_5079573, baseEnd_5079573] using wordTrace_append hprefix tailTrace_5079573
  have hstable : (prefixWord ++ tailWord_5079573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079573).length < 2 ^ (prefixWord ++ tailWord_5079573).sum := by decide
  have hdescent : baseEnd_5079573 < baseStart_5079573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079580 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_5079580 : Nat := 118140960795 + 5079580 * 2 ^ 59
def prefixEnd_5079580 : Nat := 4983230072969 + 3 ^ 40 * 5079580 * 2
def baseEnd_5079580 : Nat := 2608266062965341353589443

theorem tailTrace_5079580 : CollatzResearch.WordTrace tailWord_5079580 prefixEnd_5079580 2608266062965341353589443 := by
  unfold tailWord_5079580
  simp only [CollatzResearch.WordTrace]
  refine ⟨92633751468778329021030097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123511668625037772028040129 92633751468778329021030097)
  ·
    refine ⟨69475313601583746765772573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92633751468778329021030097 69475313601583746765772573)
    ·
      refine ⟨26053242600593905037164715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69475313601583746765772573 26053242600593905037164715)
      ·
        refine ⟨39079863900890857555747073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26053242600593905037164715 39079863900890857555747073)
        ·
          refine ⟨29309897925668143166810305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39079863900890857555747073 29309897925668143166810305)
          ·
            refine ⟨21982423444251107375107729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29309897925668143166810305 21982423444251107375107729)
            ·
              refine ⟨16486817583188330531330797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21982423444251107375107729 16486817583188330531330797)
              ·
                refine ⟨6182556593695623949249049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16486817583188330531330797 6182556593695623949249049)
                ·
                  refine ⟨4636917445271717961936787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6182556593695623949249049 4636917445271717961936787)
                  ·
                    refine ⟨6955376167907576942905181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4636917445271717961936787 6955376167907576942905181)
                    ·
                      refine ⟨2608266062965341353589443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955376167907576942905181 2608266062965341353589443)
                      ·
                        rfl

theorem cell23_5079580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_5079580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079580 prefixEnd_5079580 := by exact prefixLift 5079580
  have htrace : WordTrace (prefixWord ++ tailWord_5079580) baseStart_5079580 baseEnd_5079580 := by
    simpa [prefixWord, tailWord_5079580, baseEnd_5079580] using wordTrace_append hprefix tailTrace_5079580
  have hstable : (prefixWord ++ tailWord_5079580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079580).length < 2 ^ (prefixWord ++ tailWord_5079580).sum := by decide
  have hdescent : baseEnd_5079580 < baseStart_5079580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079586 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_5079586 : Nat := 118140960795 + 5079586 * 2 ^ 59
def prefixEnd_5079586 : Nat := 4983230072969 + 3 ^ 40 * 5079586 * 2
def baseEnd_5079586 : Nat := 2608269143849268330114415

theorem tailTrace_5079586 : CollatzResearch.WordTrace tailWord_5079586 prefixEnd_5079586 2608269143849268330114415 := by
  unfold tailWord_5079586
  simp only [CollatzResearch.WordTrace]
  refine ⟨46316930443883730266694653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123511814517023280711185741 46316930443883730266694653)
  ·
    refine ⟨17368848916456398850010495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46316930443883730266694653 17368848916456398850010495)
    ·
      refine ⟨26053273374684598275015743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17368848916456398850010495 26053273374684598275015743)
      ·
        refine ⟨39079910062026897412523615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26053273374684598275015743 39079910062026897412523615)
        ·
          refine ⟨58619865093040346118785423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39079910062026897412523615 58619865093040346118785423)
          ·
            refine ⟨87929797639560519178178135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58619865093040346118785423 87929797639560519178178135)
            ·
              refine ⟨131894696459340778767267203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87929797639560519178178135 131894696459340778767267203)
              ·
                refine ⟨197842044689011168150900805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131894696459340778767267203 197842044689011168150900805)
                ·
                  refine ⟨37095383379189594028293901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197842044689011168150900805 37095383379189594028293901)
                  ·
                    refine ⟨13910768767196097760610213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37095383379189594028293901 13910768767196097760610213)
                    ·
                      refine ⟨2608269143849268330114415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13910768767196097760610213 2608269143849268330114415)
                      ·
                        rfl

theorem cell23_5079586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_5079586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079586 prefixEnd_5079586 := by exact prefixLift 5079586
  have htrace : WordTrace (prefixWord ++ tailWord_5079586) baseStart_5079586 baseEnd_5079586 := by
    simpa [prefixWord, tailWord_5079586, baseEnd_5079586] using wordTrace_append hprefix tailTrace_5079586
  have hstable : (prefixWord ++ tailWord_5079586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079586).length < 2 ^ (prefixWord ++ tailWord_5079586).sum := by decide
  have hdescent : baseEnd_5079586 < baseStart_5079586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079603 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 1, 4, 2]
def baseStart_5079603 : Nat := 118140960795 + 5079603 * 2 ^ 59
def prefixEnd_5079603 : Nat := 4983230072969 + 3 ^ 40 * 5079603 * 2
def baseEnd_5079603 : Nat := 2608277873020394763601837

theorem tailTrace_5079603 : CollatzResearch.WordTrace tailWord_5079603 prefixEnd_5079603 2608277873020394763601837 := by
  unfold tailWord_5079603
  simp only [CollatzResearch.WordTrace]
  refine ⟨185268341816473332970147463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123512227877648888646764975 185268341816473332970147463)
  ·
    refine ⟨277902512724709999455221195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185268341816473332970147463 277902512724709999455221195)
    ·
      refine ⟨416853769087064999182831793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277902512724709999455221195 416853769087064999182831793)
      ·
        refine ⟨312640326815298749387123845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416853769087064999182831793 312640326815298749387123845)
        ·
          refine ⟨58620061277868515510085721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312640326815298749387123845 58620061277868515510085721)
          ·
            refine ⟨43965045958401386632564291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58620061277868515510085721 43965045958401386632564291)
            ·
              refine ⟨65947568937602079948846437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43965045958401386632564291 65947568937602079948846437)
              ·
                refine ⟨12365169175800389990408707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65947568937602079948846437 12365169175800389990408707)
                ·
                  refine ⟨18547753763700584985613061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12365169175800389990408707 18547753763700584985613061)
                  ·
                    refine ⟨3477703830693859684802449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18547753763700584985613061 3477703830693859684802449)
                    ·
                      refine ⟨2608277873020394763601837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477703830693859684802449 2608277873020394763601837)
                      ·
                        rfl

theorem cell23_5079603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4, 2].length) (baseStart_5079603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079603 prefixEnd_5079603 := by exact prefixLift 5079603
  have htrace : WordTrace (prefixWord ++ tailWord_5079603) baseStart_5079603 baseEnd_5079603 := by
    simpa [prefixWord, tailWord_5079603, baseEnd_5079603] using wordTrace_append hprefix tailTrace_5079603
  have hstable : (prefixWord ++ tailWord_5079603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079603).length < 2 ^ (prefixWord ++ tailWord_5079603).sum := by decide
  have hdescent : baseEnd_5079603 < baseStart_5079603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079616 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_5079616 : Nat := 118140960795 + 5079616 * 2 ^ 59
def prefixEnd_5079616 : Nat := 4983230072969 + 3 ^ 40 * 5079616 * 2
def baseEnd_5079616 : Nat := 2608284548268903212739277

theorem tailTrace_5079616 : CollatzResearch.WordTrace tailWord_5079616 prefixEnd_5079616 2608284548268903212739277 := by
  unfold tailWord_5079616
  simp only [CollatzResearch.WordTrace]
  refine ⟨92634407982713118095185351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123512543976950824126913801 92634407982713118095185351)
  ·
    refine ⟨138951611974069677142778027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92634407982713118095185351 138951611974069677142778027)
    ·
      refine ⟨208427417961104515714167041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138951611974069677142778027 208427417961104515714167041)
      ·
        refine ⟨156320563470828386785625281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208427417961104515714167041 156320563470828386785625281)
        ·
          refine ⟨117240422603121290089218961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156320563470828386785625281 117240422603121290089218961)
          ·
            refine ⟨87930316952340967566914221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117240422603121290089218961 87930316952340967566914221)
            ·
              refine ⟨32973868857127862837592833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87930316952340967566914221 32973868857127862837592833)
              ·
                refine ⟨24730401642845897128194625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32973868857127862837592833 24730401642845897128194625)
                ·
                  refine ⟨18547801232134422846145969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24730401642845897128194625 18547801232134422846145969)
                  ·
                    refine ⟨13910850924100817134609477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18547801232134422846145969 13910850924100817134609477)
                    ·
                      refine ⟨2608284548268903212739277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13910850924100817134609477 2608284548268903212739277)
                      ·
                        rfl

theorem cell23_5079616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_5079616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079616 prefixEnd_5079616 := by exact prefixLift 5079616
  have htrace : WordTrace (prefixWord ++ tailWord_5079616) baseStart_5079616 baseEnd_5079616 := by
    simpa [prefixWord, tailWord_5079616, baseEnd_5079616] using wordTrace_append hprefix tailTrace_5079616
  have hstable : (prefixWord ++ tailWord_5079616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079616).length < 2 ^ (prefixWord ++ tailWord_5079616).sum := by decide
  have hdescent : baseEnd_5079616 < baseStart_5079616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079626 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_5079626 : Nat := 118140960795 + 5079626 * 2 ^ 59
def prefixEnd_5079626 : Nat := 4983230072969 + 3 ^ 40 * 5079626 * 2
def baseEnd_5079626 : Nat := 289809964786160908179359

theorem tailTrace_5079626 : CollatzResearch.WordTrace tailWord_5079626 prefixEnd_5079626 289809964786160908179359 := by
  unfold tailWord_5079626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46317295173847501974558683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123512787130260005265489821 46317295173847501974558683)
  ·
    refine ⟨69475942760771252961838025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46317295173847501974558683 69475942760771252961838025)
    ·
      refine ⟨52106957070578439721378519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69475942760771252961838025 52106957070578439721378519)
      ·
        refine ⟨78160435605867659582067779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52106957070578439721378519 78160435605867659582067779)
        ·
          refine ⟨117240653408801489373101669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78160435605867659582067779 117240653408801489373101669)
          ·
            refine ⟨21982622514150279257456563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117240653408801489373101669 21982622514150279257456563)
            ·
              refine ⟨32973933771225418886184845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21982622514150279257456563 32973933771225418886184845)
              ·
                refine ⟨12365225164209532082319317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32973933771225418886184845 12365225164209532082319317)
                ·
                  refine ⟨289809964786160908179359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12365225164209532082319317 289809964786160908179359)
                  ·
                    rfl

theorem cell23_5079626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_5079626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079626 prefixEnd_5079626 := by exact prefixLift 5079626
  have htrace : WordTrace (prefixWord ++ tailWord_5079626) baseStart_5079626 baseEnd_5079626 := by
    simpa [prefixWord, tailWord_5079626, baseEnd_5079626] using wordTrace_append hprefix tailTrace_5079626
  have hstable : (prefixWord ++ tailWord_5079626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079626).length < 2 ^ (prefixWord ++ tailWord_5079626).sum := by decide
  have hdescent : baseEnd_5079626 < baseStart_5079626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079673 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_5079673 : Nat := 118140960795 + 5079673 * 2 ^ 59
def prefixEnd_5079673 : Nat := 4983230072969 + 3 ^ 40 * 5079673 * 2
def baseEnd_5079673 : Nat := 869437938888736496575505

theorem tailTrace_5079673 : CollatzResearch.WordTrace tailWord_5079673 prefixEnd_5079673 869437938888736496575505 := by
  unfold tailWord_5079673
  simp only [CollatzResearch.WordTrace]
  refine ⟨185270894926219734925195673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123513929950813156616797115 185270894926219734925195673)
  ·
    refine ⟨138953171194664801193896755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185270894926219734925195673 138953171194664801193896755)
    ·
      refine ⟨208429756791997201790845133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138953171194664801193896755 208429756791997201790845133)
      ·
        refine ⟨78161158796998950671566925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208429756791997201790845133 78161158796998950671566925)
        ·
          refine ⟨29310434548874606501837597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78161158796998950671566925 29310434548874606501837597)
          ·
            refine ⟨10991412955827977438189099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29310434548874606501837597 10991412955827977438189099)
            ·
              refine ⟨16487119433741966157283649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10991412955827977438189099 16487119433741966157283649)
              ·
                refine ⟨12365339575306474617962737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16487119433741966157283649 12365339575306474617962737)
                ·
                  refine ⟨9274004681479855963472053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12365339575306474617962737 9274004681479855963472053)
                  ·
                    refine ⟨869437938888736496575505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9274004681479855963472053 869437938888736496575505)
                    ·
                      rfl

theorem cell23_5079673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_5079673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079673 prefixEnd_5079673 := by exact prefixLift 5079673
  have htrace : WordTrace (prefixWord ++ tailWord_5079673) baseStart_5079673 baseEnd_5079673 := by
    simpa [prefixWord, tailWord_5079673, baseEnd_5079673] using wordTrace_append hprefix tailTrace_5079673
  have hstable : (prefixWord ++ tailWord_5079673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079673).length < 2 ^ (prefixWord ++ tailWord_5079673).sum := by decide
  have hdescent : baseEnd_5079673 < baseStart_5079673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079677 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 5]
def baseStart_5079677 : Nat := 118140960795 + 5079677 * 2 ^ 59
def prefixEnd_5079677 : Nat := 4983230072969 + 3 ^ 40 * 5079677 * 2
def baseEnd_5079677 : Nat := 289812874509869719341833

theorem tailTrace_5079677 : CollatzResearch.WordTrace tailWord_5079677 prefixEnd_5079677 289812874509869719341833 := by
  unfold tailWord_5079677
  simp only [CollatzResearch.WordTrace]
  refine ⟨185271040818205243608341285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123514027212136829072227523 185271040818205243608341285)
  ·
    refine ⟨34738320153413483176563991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185271040818205243608341285 34738320153413483176563991)
    ·
      refine ⟨52107480230120224764845987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34738320153413483176563991 52107480230120224764845987)
      ·
        refine ⟨78161220345180337147268981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52107480230120224764845987 78161220345180337147268981)
        ·
          refine ⟨7327614407360656607556467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78161220345180337147268981 7327614407360656607556467)
          ·
            refine ⟨10991421611040984911334701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7327614407360656607556467 10991421611040984911334701)
            ·
              refine ⟨4121783104140369341750513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10991421611040984911334701 4121783104140369341750513)
              ·
                refine ⟨3091337328105277006312885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121783104140369341750513 3091337328105277006312885)
                ·
                  refine ⟨289812874509869719341833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091337328105277006312885 289812874509869719341833)
                  ·
                    rfl

theorem cell23_5079677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_5079677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079677 prefixEnd_5079677 := by exact prefixLift 5079677
  have htrace : WordTrace (prefixWord ++ tailWord_5079677) baseStart_5079677 baseEnd_5079677 := by
    simpa [prefixWord, tailWord_5079677, baseEnd_5079677] using wordTrace_append hprefix tailTrace_5079677
  have hstable : (prefixWord ++ tailWord_5079677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079677).length < 2 ^ (prefixWord ++ tailWord_5079677).sum := by decide
  have hdescent : baseEnd_5079677 < baseStart_5079677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079703 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 5, 4]
def baseStart_5079703 : Nat := 118140960795 + 5079703 * 2 ^ 59
def prefixEnd_5079703 : Nat := 4983230072969 + 3 ^ 40 * 5079703 * 2
def baseEnd_5079703 : Nat := 869443073695281457450459

theorem tailTrace_5079703 : CollatzResearch.WordTrace tailWord_5079703 prefixEnd_5079703 869443073695281457450459 := by
  unfold tailWord_5079703
  simp only [CollatzResearch.WordTrace]
  refine ⟨185271989116111050048787763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123514659410740700032525175 185271989116111050048787763)
  ·
    refine ⟨277907983674166575073181645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185271989116111050048787763 277907983674166575073181645)
    ·
      refine ⟨104215493877812465652443117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277907983674166575073181645 104215493877812465652443117)
      ·
        refine ⟨39080810204179674619666169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104215493877812465652443117 39080810204179674619666169)
        ·
          refine ⟨29310607653134755964749627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39080810204179674619666169 29310607653134755964749627)
          ·
            refine ⟨43965911479702133947124441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29310607653134755964749627 43965911479702133947124441)
            ·
              refine ⟨32974433609776600460343331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43965911479702133947124441 32974433609776600460343331)
              ·
                refine ⟨49461650414664900690514997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32974433609776600460343331 49461650414664900690514997)
                ·
                  refine ⟨4637029726374834439735781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49461650414664900690514997 4637029726374834439735781)
                  ·
                    refine ⟨869443073695281457450459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4637029726374834439735781 869443073695281457450459)
                    ·
                      rfl

theorem cell23_5079703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_5079703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079703 prefixEnd_5079703 := by exact prefixLift 5079703
  have htrace : WordTrace (prefixWord ++ tailWord_5079703) baseStart_5079703 baseEnd_5079703 := by
    simpa [prefixWord, tailWord_5079703, baseEnd_5079703] using wordTrace_append hprefix tailTrace_5079703
  have hstable : (prefixWord ++ tailWord_5079703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079703).length < 2 ^ (prefixWord ++ tailWord_5079703).sum := by decide
  have hdescent : baseEnd_5079703 < baseStart_5079703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079764 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5079764 : Nat := 118140960795 + 5079764 * 2 ^ 59
def prefixEnd_5079764 : Nat := 4983230072969 + 3 ^ 40 * 5079764 * 2
def baseEnd_5079764 : Nat := 2608360543405768633688597

theorem tailTrace_5079764 : CollatzResearch.WordTrace tailWord_5079764 prefixEnd_5079764 2608360543405768633688597 := by
  unfold tailWord_5079764
  simp only [CollatzResearch.WordTrace]
  refine ⟨92637106984445028733379173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123516142645926704977838897 92637106984445028733379173)
  ·
    refine ⟨17369457559583442887508595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92637106984445028733379173 17369457559583442887508595)
    ·
      refine ⟨26054186339375164331262893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17369457559583442887508595 26054186339375164331262893)
      ·
        refine ⟨9770319877265686624223585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26054186339375164331262893 9770319877265686624223585)
        ·
          refine ⟨7327739907949264968167689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9770319877265686624223585 7327739907949264968167689)
          ·
            refine ⟨5495804930961948726125767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7327739907949264968167689 5495804930961948726125767)
            ·
              refine ⟨8243707396442923089188651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495804930961948726125767 8243707396442923089188651)
              ·
                refine ⟨12365561094664384633782977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8243707396442923089188651 12365561094664384633782977)
                ·
                  refine ⟨9274170820998288475337233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12365561094664384633782977 9274170820998288475337233)
                  ·
                    refine ⟨6955628115748716356502925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9274170820998288475337233 6955628115748716356502925)
                    ·
                      refine ⟨2608360543405768633688597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955628115748716356502925 2608360543405768633688597)
                      ·
                        rfl

theorem cell23_5079764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5079764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079764 prefixEnd_5079764 := by exact prefixLift 5079764
  have htrace : WordTrace (prefixWord ++ tailWord_5079764) baseStart_5079764 baseEnd_5079764 := by
    simpa [prefixWord, tailWord_5079764, baseEnd_5079764] using wordTrace_append hprefix tailTrace_5079764
  have hstable : (prefixWord ++ tailWord_5079764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079764).length < 2 ^ (prefixWord ++ tailWord_5079764).sum := by decide
  have hdescent : baseEnd_5079764 < baseStart_5079764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079770 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2]
def baseStart_5079770 : Nat := 118140960795 + 5079770 * 2 ^ 59
def prefixEnd_5079770 : Nat := 4983230072969 + 3 ^ 40 * 5079770 * 2
def baseEnd_5079770 : Nat := 2608363624289695610213569

theorem tailTrace_5079770 : CollatzResearch.WordTrace tailWord_5079770 prefixEnd_5079770 2608363624289695610213569 := by
  unfold tailWord_5079770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46318608201717080122869191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123516288537912213660984509 46318608201717080122869191)
  ·
    refine ⟨69477912302575620184303787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46318608201717080122869191 69477912302575620184303787)
    ·
      refine ⟨104216868453863430276455681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69477912302575620184303787 104216868453863430276455681)
      ·
        refine ⟨78162651340397572707341761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104216868453863430276455681 78162651340397572707341761)
        ·
          refine ⟨58621988505298179530506321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78162651340397572707341761 58621988505298179530506321)
          ·
            refine ⟨43966491378973634647879741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58621988505298179530506321 43966491378973634647879741)
            ·
              refine ⟨16487434267115112992954903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43966491378973634647879741 16487434267115112992954903)
              ·
                refine ⟨24731151400672669489432355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16487434267115112992954903 24731151400672669489432355)
                ·
                  refine ⟨37096727101009004234148533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24731151400672669489432355 37096727101009004234148533)
                  ·
                    refine ⟨3477818165719594146951425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37096727101009004234148533 3477818165719594146951425)
                    ·
                      refine ⟨2608363624289695610213569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477818165719594146951425 2608363624289695610213569)
                      ·
                        rfl

theorem cell23_5079770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_5079770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079770 prefixEnd_5079770 := by exact prefixLift 5079770
  have htrace : WordTrace (prefixWord ++ tailWord_5079770) baseStart_5079770 baseEnd_5079770 := by
    simpa [prefixWord, tailWord_5079770, baseEnd_5079770] using wordTrace_append hprefix tailTrace_5079770
  have hstable : (prefixWord ++ tailWord_5079770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079770).length < 2 ^ (prefixWord ++ tailWord_5079770).sum := by decide
  have hdescent : baseEnd_5079770 < baseStart_5079770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079780 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_5079780 : Nat := 118140960795 + 5079780 * 2 ^ 59
def prefixEnd_5079780 : Nat := 4983230072969 + 3 ^ 40 * 5079780 * 2
def baseEnd_5079780 : Nat := 869456253032080190362841

theorem tailTrace_5079780 : CollatzResearch.WordTrace tailWord_5079780 prefixEnd_5079780 869456253032080190362841 := by
  unfold tailWord_5079780
  simp only [CollatzResearch.WordTrace]
  refine ⟨92637398768416046099670397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123516531691221394799560529 92637398768416046099670397)
  ·
    refine ⟨34739024538156017287376399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92637398768416046099670397 34739024538156017287376399)
    ·
      refine ⟨52108536807234025931064599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34739024538156017287376399 52108536807234025931064599)
      ·
        refine ⟨78162805210851038896596899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52108536807234025931064599 78162805210851038896596899)
        ·
          refine ⟨117244207816276558344895349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78162805210851038896596899 117244207816276558344895349)
          ·
            refine ⟨10991644482775927344833939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117244207816276558344895349 10991644482775927344833939)
            ·
              refine ⟨16487466724163891017250909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10991644482775927344833939 16487466724163891017250909)
              ·
                refine ⟨6182800021561459131469091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16487466724163891017250909 6182800021561459131469091)
                ·
                  refine ⟨9274200032342188697203637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6182800021561459131469091 9274200032342188697203637)
                  ·
                    refine ⟨869456253032080190362841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9274200032342188697203637 869456253032080190362841)
                    ·
                      rfl

theorem cell23_5079780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_5079780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079780 prefixEnd_5079780 := by exact prefixLift 5079780
  have htrace : WordTrace (prefixWord ++ tailWord_5079780) baseStart_5079780 baseEnd_5079780 := by
    simpa [prefixWord, tailWord_5079780, baseEnd_5079780] using wordTrace_append hprefix tailTrace_5079780
  have hstable : (prefixWord ++ tailWord_5079780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079780).length < 2 ^ (prefixWord ++ tailWord_5079780).sum := by decide
  have hdescent : baseEnd_5079780 < baseStart_5079780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079794 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5079794 : Nat := 118140960795 + 5079794 * 2 ^ 59
def prefixEnd_5079794 : Nat := 4983230072969 + 3 ^ 40 * 5079794 * 2
def baseEnd_5079794 : Nat := 2608375947825403516313459

theorem tailTrace_5079794 : CollatzResearch.WordTrace tailWord_5079794 prefixEnd_5079794 2608375947825403516313459 := by
  unfold tailWord_5079794
  simp only [CollatzResearch.WordTrace]
  refine ⟨46318827039695343147587609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123516872105854248393566957 46318827039695343147587609)
  ·
    refine ⟨34739120279771507360690707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46318827039695343147587609 34739120279771507360690707)
    ·
      refine ⟨52108680419657261041036061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34739120279771507360690707 52108680419657261041036061)
      ·
        refine ⟨19540755157371472890388523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52108680419657261041036061 19540755157371472890388523)
        ·
          refine ⟨29311132736057209335582785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19540755157371472890388523 29311132736057209335582785)
          ·
            refine ⟨21983349552042907001687089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29311132736057209335582785 21983349552042907001687089)
            ·
              refine ⟨16487512164032180251265317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21983349552042907001687089 16487512164032180251265317)
              ·
                refine ⟨3091408530756033797112247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16487512164032180251265317 3091408530756033797112247)
                ·
                  refine ⟨4637112796134050695668371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091408530756033797112247 4637112796134050695668371)
                  ·
                    refine ⟨6955669194201076043502557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4637112796134050695668371 6955669194201076043502557)
                    ·
                      refine ⟨2608375947825403516313459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955669194201076043502557 2608375947825403516313459)
                      ·
                        rfl

theorem cell23_5079794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5079794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079794 prefixEnd_5079794 := by exact prefixLift 5079794
  have htrace : WordTrace (prefixWord ++ tailWord_5079794) baseStart_5079794 baseEnd_5079794 := by
    simpa [prefixWord, tailWord_5079794, baseEnd_5079794] using wordTrace_append hprefix tailTrace_5079794
  have hstable : (prefixWord ++ tailWord_5079794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079794).length < 2 ^ (prefixWord ++ tailWord_5079794).sum := by decide
  have hdescent : baseEnd_5079794 < baseStart_5079794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079817 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 3, 2, 2]
def baseStart_5079817 : Nat := 118140960795 + 5079817 * 2 ^ 59
def prefixEnd_5079817 : Nat := 4983230072969 + 3 ^ 40 * 5079817 * 2
def baseEnd_5079817 : Nat := 2608387757880456926325853

theorem tailTrace_5079817 : CollatzResearch.WordTrace tailWord_5079817 prefixEnd_5079817 2608387757880456926325853 := by
  unfold tailWord_5079817
  simp only [CollatzResearch.WordTrace]
  refine ⟨185276147037698047518437705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123517431358465365012291803 185276147037698047518437705)
  ·
    refine ⟨138957110278273535638828279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185276147037698047518437705 138957110278273535638828279)
    ·
      refine ⟨208435665417410303458242419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138957110278273535638828279 208435665417410303458242419)
      ·
        refine ⟨312653498126115455187363629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208435665417410303458242419 312653498126115455187363629)
        ·
          refine ⟨117245061797293295695261361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312653498126115455187363629 117245061797293295695261361)
          ·
            refine ⟨87933796347969971771446021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117245061797293295695261361 87933796347969971771446021)
            ·
              refine ⟨16487586815244369707146129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87933796347969971771446021 16487586815244369707146129)
              ·
                refine ⟨12365690111433277280359597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16487586815244369707146129 12365690111433277280359597)
                ·
                  refine ⟨4637133791787478980134849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12365690111433277280359597 4637133791787478980134849)
                  ·
                    refine ⟨3477850343840609235101137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4637133791787478980134849 3477850343840609235101137)
                    ·
                      refine ⟨2608387757880456926325853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477850343840609235101137 2608387757880456926325853)
                      ·
                        rfl

theorem cell23_5079817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 2, 2].length) (baseStart_5079817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079817 prefixEnd_5079817 := by exact prefixLift 5079817
  have htrace : WordTrace (prefixWord ++ tailWord_5079817) baseStart_5079817 baseEnd_5079817 := by
    simpa [prefixWord, tailWord_5079817, baseEnd_5079817] using wordTrace_append hprefix tailTrace_5079817
  have hstable : (prefixWord ++ tailWord_5079817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079817).length < 2 ^ (prefixWord ++ tailWord_5079817).sum := by decide
  have hdescent : baseEnd_5079817 < baseStart_5079817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079877 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 1, 3, 2]
def baseStart_5079877 : Nat := 118140960795 + 5079877 * 2 ^ 59
def prefixEnd_5079877 : Nat := 4983230072969 + 3 ^ 40 * 5079877 * 2
def baseEnd_5079877 : Nat := 2608418566719726691575577

theorem tailTrace_5079877 : CollatzResearch.WordTrace tailWord_5079877 prefixEnd_5079877 2608418566719726691575577 := by
  unfold tailWord_5079877
  simp only [CollatzResearch.WordTrace]
  refine ⟨185278335417480677765621885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123518890278320451843747923 185278335417480677765621885)
  ·
    refine ⟨69479375781555254162108207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185278335417480677765621885 69479375781555254162108207)
    ·
      refine ⟨104219063672332881243162311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69479375781555254162108207 104219063672332881243162311)
      ·
        refine ⟨156328595508499321864743467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104219063672332881243162311 156328595508499321864743467)
        ·
          refine ⟨234492893262748982797115201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156328595508499321864743467 234492893262748982797115201)
          ·
            refine ⟨175869669947061737097836401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234492893262748982797115201 175869669947061737097836401)
            ·
              refine ⟨131902252460296302823377301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175869669947061737097836401 131902252460296302823377301)
              ·
                refine ⟨6182918084076389194845811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131902252460296302823377301 6182918084076389194845811)
                ·
                  refine ⟨9274377126114583792268717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6182918084076389194845811 9274377126114583792268717)
                  ·
                    refine ⟨3477891422292968922100769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9274377126114583792268717 3477891422292968922100769)
                    ·
                      refine ⟨2608418566719726691575577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3477891422292968922100769 2608418566719726691575577)
                      ·
                        rfl

theorem cell23_5079877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_5079877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079877 prefixEnd_5079877 := by exact prefixLift 5079877
  have htrace : WordTrace (prefixWord ++ tailWord_5079877) baseStart_5079877 baseEnd_5079877 := by
    simpa [prefixWord, tailWord_5079877, baseEnd_5079877] using wordTrace_append hprefix tailTrace_5079877
  have hstable : (prefixWord ++ tailWord_5079877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079877).length < 2 ^ (prefixWord ++ tailWord_5079877).sum := by decide
  have hdescent : baseEnd_5079877 < baseStart_5079877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079940 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_5079940 : Nat := 118140960795 + 5079940 * 2 ^ 59
def prefixEnd_5079940 : Nat := 4983230072969 + 3 ^ 40 * 5079940 * 2
def baseEnd_5079940 : Nat := 2608450916000959945087787

theorem tailTrace_5079940 : CollatzResearch.WordTrace tailWord_5079940 prefixEnd_5079940 2608450916000959945087787 := by
  unfold tailWord_5079940
  simp only [CollatzResearch.WordTrace]
  refine ⟨92640316608126219762582637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123520422144168293016776849 92640316608126219762582637)
  ·
    refine ⟨34740118728047332410968489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92640316608126219762582637 34740118728047332410968489)
    ·
      refine ⟨26055089046035499308226367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34740118728047332410968489 26055089046035499308226367)
      ·
        refine ⟨39082633569053248962339551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26055089046035499308226367 39082633569053248962339551)
        ·
          refine ⟨58623950353579873443509327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39082633569053248962339551 58623950353579873443509327)
          ·
            refine ⟨87935925530369810165263991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58623950353579873443509327 87935925530369810165263991)
            ·
              refine ⟨131903888295554715247895987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87935925530369810165263991 131903888295554715247895987)
              ·
                refine ⟨197855832443332072871843981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131903888295554715247895987 197855832443332072871843981)
                ·
                  refine ⟨74195937166249527326941493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197855832443332072871843981 74195937166249527326941493)
                  ·
                    refine ⟨6955869109335893186900765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74195937166249527326941493 6955869109335893186900765)
                    ·
                      refine ⟨2608450916000959945087787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955869109335893186900765 2608450916000959945087787)
                      ·
                        rfl

theorem cell23_5079940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_5079940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079940 prefixEnd_5079940 := by exact prefixLift 5079940
  have htrace : WordTrace (prefixWord ++ tailWord_5079940) baseStart_5079940 baseEnd_5079940 := by
    simpa [prefixWord, tailWord_5079940, baseEnd_5079940] using wordTrace_append hprefix tailTrace_5079940
  have hstable : (prefixWord ++ tailWord_5079940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079940).length < 2 ^ (prefixWord ++ tailWord_5079940).sum := by decide
  have hdescent : baseEnd_5079940 < baseStart_5079940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5079980 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_5079980 : Nat := 118140960795 + 5079980 * 2 ^ 59
def prefixEnd_5079980 : Nat := 4983230072969 + 3 ^ 40 * 5079980 * 2
def baseEnd_5079980 : Nat := 2608471455227139788587603

theorem tailTrace_5079980 : CollatzResearch.WordTrace tailWord_5079980 prefixEnd_5079980 2608471455227139788587603 := by
  unfold tailWord_5079980
  simp only [CollatzResearch.WordTrace]
  refine ⟨92641046068053763178310697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123521394757405017571080929 92641046068053763178310697)
  ·
    refine ⟨69480784551040322383733023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92641046068053763178310697 69480784551040322383733023)
    ·
      refine ⟨104221176826560483575599535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69480784551040322383733023 104221176826560483575599535)
      ·
        refine ⟨156331765239840725363399303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104221176826560483575599535 156331765239840725363399303)
        ·
          refine ⟨234497647859761088045098955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156331765239840725363399303 234497647859761088045098955)
          ·
            refine ⟨351746471789641632067648433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234497647859761088045098955 351746471789641632067648433)
            ·
              refine ⟨263809853842231224050736325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351746471789641632067648433 263809853842231224050736325)
              ·
                refine ⟨49464347595418354509513061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263809853842231224050736325 49464347595418354509513061)
                ·
                  refine ⟨9274565174140941470533699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49464347595418354509513061 9274565174140941470533699)
                  ·
                    refine ⟨13911847761211412205800549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9274565174140941470533699 13911847761211412205800549)
                    ·
                      refine ⟨2608471455227139788587603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13911847761211412205800549 2608471455227139788587603)
                      ·
                        rfl

theorem cell23_5079980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_5079980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5079980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5079980 prefixEnd_5079980 := by exact prefixLift 5079980
  have htrace : WordTrace (prefixWord ++ tailWord_5079980) baseStart_5079980 baseEnd_5079980 := by
    simpa [prefixWord, tailWord_5079980, baseEnd_5079980] using wordTrace_append hprefix tailTrace_5079980
  have hstable : (prefixWord ++ tailWord_5079980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5079980).length < 2 ^ (prefixWord ++ tailWord_5079980).sum := by decide
  have hdescent : baseEnd_5079980 < baseStart_5079980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5079980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080017 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_5080017 : Nat := 118140960795 + 5080017 * 2 ^ 59
def prefixEnd_5080017 : Nat := 4983230072969 + 3 ^ 40 * 5080017 * 2
def baseEnd_5080017 : Nat := 2608490454011356143824933

theorem tailTrace_5080017 : CollatzResearch.WordTrace tailWord_5080017 prefixEnd_5080017 2608490454011356143824933 := by
  unfold tailWord_5080017
  simp only [CollatzResearch.WordTrace]
  refine ⟨185283441636973481675718305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123522294424648987783812203 185283441636973481675718305)
  ·
    refine ⟨138962581227730111256788729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185283441636973481675718305 138962581227730111256788729)
    ·
      refine ⟨104221935920797583442591547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138962581227730111256788729 104221935920797583442591547)
      ·
        refine ⟨156332903881196375163887321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104221935920797583442591547 156332903881196375163887321)
        ·
          refine ⟨117249677910897281372915491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156332903881196375163887321 117249677910897281372915491)
          ·
            refine ⟨175874516866345922059373237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117249677910897281372915491 175874516866345922059373237)
            ·
              refine ⟨16488235956219930193066241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175874516866345922059373237 16488235956219930193066241)
              ·
                refine ⟨12366176967164947644799681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16488235956219930193066241 12366176967164947644799681)
                ·
                  refine ⟨9274632725373710733599761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12366176967164947644799681 9274632725373710733599761)
                  ·
                    refine ⟨6955974544030283050199821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9274632725373710733599761 6955974544030283050199821)
                    ·
                      refine ⟨2608490454011356143824933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6955974544030283050199821 2608490454011356143824933)
                      ·
                        rfl

theorem cell23_5080017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_5080017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080017 prefixEnd_5080017 := by exact prefixLift 5080017
  have htrace : WordTrace (prefixWord ++ tailWord_5080017) baseStart_5080017 baseEnd_5080017 := by
    simpa [prefixWord, tailWord_5080017, baseEnd_5080017] using wordTrace_append hprefix tailTrace_5080017
  have hstable : (prefixWord ++ tailWord_5080017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080017).length < 2 ^ (prefixWord ++ tailWord_5080017).sum := by decide
  have hdescent : baseEnd_5080017 < baseStart_5080017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080024 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 3, 4]
def baseStart_5080024 : Nat := 118140960795 + 5080024 * 2 ^ 59
def prefixEnd_5080024 : Nat := 4983230072969 + 3 ^ 40 * 5080024 * 2
def baseEnd_5080024 : Nat := 869498016125312538812467

theorem tailTrace_5080024 : CollatzResearch.WordTrace tailWord_5080024 prefixEnd_5080024 869498016125312538812467 := by
  unfold tailWord_5080024
  simp only [CollatzResearch.WordTrace]
  refine ⟨92641848473974060935611563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123522464631965414580815417 92641848473974060935611563)
  ·
    refine ⟨138962772710961091403417345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92641848473974060935611563 138962772710961091403417345)
    ·
      refine ⟨104222079533220818552563009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138962772710961091403417345 104222079533220818552563009)
      ·
        refine ⟨78166559649915613914422257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104222079533220818552563009 78166559649915613914422257)
        ·
          refine ⟨58624919737436710435816693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78166559649915613914422257 58624919737436710435816693)
          ·
            refine ⟨5496086225384691603357815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58624919737436710435816693 5496086225384691603357815)
            ·
              refine ⟨8244129338077037405036723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496086225384691603357815 8244129338077037405036723)
              ·
                refine ⟨12366194007115556107555085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8244129338077037405036723 12366194007115556107555085)
                ·
                  refine ⟨4637322752668333540333157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12366194007115556107555085 4637322752668333540333157)
                  ·
                    refine ⟨869498016125312538812467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4637322752668333540333157 869498016125312538812467)
                    ·
                      rfl

theorem cell23_5080024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_5080024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080024 prefixEnd_5080024 := by exact prefixLift 5080024
  have htrace : WordTrace (prefixWord ++ tailWord_5080024) baseStart_5080024 baseEnd_5080024 := by
    simpa [prefixWord, tailWord_5080024, baseEnd_5080024] using wordTrace_append hprefix tailTrace_5080024
  have hstable : (prefixWord ++ tailWord_5080024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080024).length < 2 ^ (prefixWord ++ tailWord_5080024).sum := by decide
  have hdescent : baseEnd_5080024 < baseStart_5080024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080040 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5080040 : Nat := 118140960795 + 5080040 * 2 ^ 59
def prefixEnd_5080040 : Nat := 4983230072969 + 3 ^ 40 * 5080040 * 2
def baseEnd_5080040 : Nat := 2608502264066409553837327

theorem tailTrace_5080040 : CollatzResearch.WordTrace tailWord_5080040 prefixEnd_5080040 2608502264066409553837327 := by
  unfold tailWord_5080040
  simp only [CollatzResearch.WordTrace]
  refine ⟨92642140257945078301902787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123522853677260104402537049 92642140257945078301902787)
  ·
    refine ⟨138963210386917617452854181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92642140257945078301902787 138963210386917617452854181)
    ·
      refine ⟨26055601947547053272410159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138963210386917617452854181 26055601947547053272410159)
      ·
        refine ⟨39083402921320579908615239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26055601947547053272410159 39083402921320579908615239)
        ·
          refine ⟨58625104381980869862922859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39083402921320579908615239 58625104381980869862922859)
          ·
            refine ⟨87937656572971304794384289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58625104381980869862922859 87937656572971304794384289)
            ·
              refine ⟨65953242429728478595788217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87937656572971304794384289 65953242429728478595788217)
              ·
                refine ⟨49464931822296358946841163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65953242429728478595788217 49464931822296358946841163)
                ·
                  refine ⟨74197397733444538420261745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49464931822296358946841163 74197397733444538420261745)
                  ·
                    refine ⟨55648048300083403815196309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74197397733444538420261745 55648048300083403815196309)
                    ·
                      refine ⟨2608502264066409553837327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55648048300083403815196309 2608502264066409553837327)
                      ·
                        rfl

theorem cell23_5080040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5080040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080040 prefixEnd_5080040 := by exact prefixLift 5080040
  have htrace : WordTrace (prefixWord ++ tailWord_5080040) baseStart_5080040 baseEnd_5080040 := by
    simpa [prefixWord, tailWord_5080040, baseEnd_5080040] using wordTrace_append hprefix tailTrace_5080040
  have hstable : (prefixWord ++ tailWord_5080040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080040).length < 2 ^ (prefixWord ++ tailWord_5080040).sum := by decide
  have hdescent : baseEnd_5080040 < baseStart_5080040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080097 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_5080097 : Nat := 118140960795 + 5080097 * 2 ^ 59
def prefixEnd_5080097 : Nat := 4983230072969 + 3 ^ 40 * 5080097 * 2
def baseEnd_5080097 : Nat := 869510510821238610274855

theorem tailTrace_5080097 : CollatzResearch.WordTrace tailWord_5080097 prefixEnd_5080097 869510510821238610274855 := by
  unfold tailWord_5080097
  simp only [CollatzResearch.WordTrace]
  refine ⟨185286359476683655338630545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123524239651122436892420363 185286359476683655338630545)
  ·
    refine ⟨138964769607512741503972909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185286359476683655338630545 138964769607512741503972909)
    ·
      refine ⟨52111788602817278063989841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138964769607512741503972909 52111788602817278063989841)
      ·
        refine ⟨39083841452112958547992381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52111788602817278063989841 39083841452112958547992381)
        ·
          refine ⟨14656440544542359455497143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39083841452112958547992381 14656440544542359455497143)
          ·
            refine ⟨21984660816813539183245715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14656440544542359455497143 21984660816813539183245715)
            ·
              refine ⟨32976991225220308774868573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21984660816813539183245715 32976991225220308774868573)
              ·
                refine ⟨12366371709457615790575715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32976991225220308774868573 12366371709457615790575715)
                ·
                  refine ⟨18549557564186423685863573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12366371709457615790575715 18549557564186423685863573)
                  ·
                    refine ⟨869510510821238610274855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18549557564186423685863573 869510510821238610274855)
                    ·
                      rfl

theorem cell23_5080097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_5080097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080097 prefixEnd_5080097 := by exact prefixLift 5080097
  have htrace : WordTrace (prefixWord ++ tailWord_5080097) baseStart_5080097 baseEnd_5080097 := by
    simpa [prefixWord, tailWord_5080097, baseEnd_5080097] using wordTrace_append hprefix tailTrace_5080097
  have hstable : (prefixWord ++ tailWord_5080097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080097).length < 2 ^ (prefixWord ++ tailWord_5080097).sum := by decide
  have hdescent : baseEnd_5080097 < baseStart_5080097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080107 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 3]
def baseStart_5080107 : Nat := 118140960795 + 5080107 * 2 ^ 59
def prefixEnd_5080107 : Nat := 4983230072969 + 3 ^ 40 * 5080107 * 2
def baseEnd_5080107 : Nat := 2608536667270260791699519

theorem tailTrace_5080107 : CollatzResearch.WordTrace tailWord_5080107 prefixEnd_5080107 2608536667270260791699519 := by
  unfold tailWord_5080107
  simp only [CollatzResearch.WordTrace]
  refine ⟨185286724206647427046494575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123524482804431618030996383 185286724206647427046494575)
  ·
    refine ⟨277930086309971140569741863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185286724206647427046494575 277930086309971140569741863)
    ·
      refine ⟨416895129464956710854612795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277930086309971140569741863 416895129464956710854612795)
      ·
        refine ⟨625342694197435066281919193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416895129464956710854612795 625342694197435066281919193)
        ·
          refine ⟨469007020648076299711439395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625342694197435066281919193 469007020648076299711439395)
          ·
            refine ⟨703510530972114449567159093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469007020648076299711439395 703510530972114449567159093)
            ·
              refine ⟨65954112278635729646921165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 703510530972114449567159093 65954112278635729646921165)
              ·
                refine ⟨24732792104488398617595437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65954112278635729646921165 24732792104488398617595437)
                ·
                  refine ⟨9274797039183149481598289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24732792104488398617595437 9274797039183149481598289)
                  ·
                    refine ⟨6956097779387362111198717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9274797039183149481598289 6956097779387362111198717)
                    ·
                      refine ⟨2608536667270260791699519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6956097779387362111198717 2608536667270260791699519)
                      ·
                        rfl

theorem cell23_5080107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 3].length) (baseStart_5080107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080107 prefixEnd_5080107 := by exact prefixLift 5080107
  have htrace : WordTrace (prefixWord ++ tailWord_5080107) baseStart_5080107 baseEnd_5080107 := by
    simpa [prefixWord, tailWord_5080107, baseEnd_5080107] using wordTrace_append hprefix tailTrace_5080107
  have hstable : (prefixWord ++ tailWord_5080107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080107).length < 2 ^ (prefixWord ++ tailWord_5080107).sum := by decide
  have hdescent : baseEnd_5080107 < baseStart_5080107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080118 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5080118 : Nat := 118140960795 + 5080118 * 2 ^ 59
def prefixEnd_5080118 : Nat := 4983230072969 + 3 ^ 40 * 5080118 * 2
def baseEnd_5080118 : Nat := 869514105185820082887323

theorem tailTrace_5080118 : CollatzResearch.WordTrace tailWord_5080118 prefixEnd_5080118 869514105185820082887323 := by
  unfold tailWord_5080118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580445338100473495321563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123524750273071717283430005 11580445338100473495321563)
  ·
    refine ⟨17370668007150710242982345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11580445338100473495321563 17370668007150710242982345)
    ·
      refine ⟨13028001005363032682236759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17370668007150710242982345 13028001005363032682236759)
      ·
        refine ⟨19542001508044549023355139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13028001005363032682236759 19542001508044549023355139)
        ·
          refine ⟨29313002262066823535032709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19542001508044549023355139 29313002262066823535032709)
          ·
            refine ⟨5496187924137529412818633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29313002262066823535032709 5496187924137529412818633)
            ·
              refine ⟨4122140943103147059613975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496187924137529412818633 4122140943103147059613975)
              ·
                refine ⟨6183211414654720589420963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122140943103147059613975 6183211414654720589420963)
                ·
                  refine ⟨9274817121982080884131445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183211414654720589420963 9274817121982080884131445)
                  ·
                    refine ⟨869514105185820082887323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9274817121982080884131445 869514105185820082887323)
                    ·
                      rfl

theorem cell23_5080118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5080118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080118 prefixEnd_5080118 := by exact prefixLift 5080118
  have htrace : WordTrace (prefixWord ++ tailWord_5080118) baseStart_5080118 baseEnd_5080118 := by
    simpa [prefixWord, tailWord_5080118, baseEnd_5080118] using wordTrace_append hprefix tailTrace_5080118
  have hstable : (prefixWord ++ tailWord_5080118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080118).length < 2 ^ (prefixWord ++ tailWord_5080118).sum := by decide
  have hdescent : baseEnd_5080118 < baseStart_5080118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080121 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5080121 : Nat := 118140960795 + 5080121 * 2 ^ 59
def prefixEnd_5080121 : Nat := 4983230072969 + 3 ^ 40 * 5080121 * 2
def baseEnd_5080121 : Nat := 2608543855999423736924455

theorem tailTrace_5080121 : CollatzResearch.WordTrace tailWord_5080121 prefixEnd_5080121 2608543855999423736924455 := by
  unfold tailWord_5080121
  simp only [CollatzResearch.WordTrace]
  refine ⟨185287234828596707437504217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123524823219064471625002811 185287234828596707437504217)
  ·
    refine ⟨138965426121447530578128163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185287234828596707437504217 138965426121447530578128163)
    ·
      refine ⟨208448139182171295867192245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138965426121447530578128163 208448139182171295867192245)
      ·
        refine ⟨19542013048328558987549273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208448139182171295867192245 19542013048328558987549273)
        ·
          refine ⟨14656509786246419240661955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19542013048328558987549273 14656509786246419240661955)
          ·
            refine ⟨21984764679369628860992933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14656509786246419240661955 21984764679369628860992933)
            ·
              refine ⟨4122143377381805411436175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21984764679369628860992933 4122143377381805411436175)
              ·
                refine ⟨6183215066072708117154263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122143377381805411436175 6183215066072708117154263)
                ·
                  refine ⟨9274822599109062175731395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183215066072708117154263 9274822599109062175731395)
                  ·
                    refine ⟨13912233898663593263597093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9274822599109062175731395 13912233898663593263597093)
                    ·
                      refine ⟨2608543855999423736924455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13912233898663593263597093 2608543855999423736924455)
                      ·
                        rfl

theorem cell23_5080121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5080121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080121 prefixEnd_5080121 := by exact prefixLift 5080121
  have htrace : WordTrace (prefixWord ++ tailWord_5080121) baseStart_5080121 baseEnd_5080121 := by
    simpa [prefixWord, tailWord_5080121, baseEnd_5080121] using wordTrace_append hprefix tailTrace_5080121
  have hstable : (prefixWord ++ tailWord_5080121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080121).length < 2 ^ (prefixWord ++ tailWord_5080121).sum := by decide
  have hdescent : baseEnd_5080121 < baseStart_5080121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080138 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_5080138 : Nat := 118140960795 + 5080138 * 2 ^ 59
def prefixEnd_5080138 : Nat := 4983230072969 + 3 ^ 40 * 5080138 * 2
def baseEnd_5080138 : Nat := 2608552585170550170411877

theorem tailTrace_5080138 : CollatzResearch.WordTrace tailWord_5080138 prefixEnd_5080138 2608552585170550170411877 := by
  unfold tailWord_5080138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46321963717383779835218267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123525236579690079560582045 46321963717383779835218267)
  ·
    refine ⟨69482945576075669752827401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46321963717383779835218267 69482945576075669752827401)
    ·
      refine ⟨52112209182056752314620551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69482945576075669752827401 52112209182056752314620551)
      ·
        refine ⟨78168313773085128471930827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52112209182056752314620551 78168313773085128471930827)
        ·
          refine ⟨117252470659627692707896241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78168313773085128471930827 117252470659627692707896241)
          ·
            refine ⟨87939352994720769530922181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117252470659627692707896241 87939352994720769530922181)
            ·
              refine ⟨16488628686510144287047909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87939352994720769530922181 16488628686510144287047909)
              ·
                refine ⟨3091617878720652053821483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16488628686510144287047909 3091617878720652053821483)
                ·
                  refine ⟨4637426818080978080732225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091617878720652053821483 4637426818080978080732225)
                  ·
                    refine ⟨3478070113560733560549169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4637426818080978080732225 3478070113560733560549169)
                    ·
                      refine ⟨2608552585170550170411877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478070113560733560549169 2608552585170550170411877)
                      ·
                        rfl

theorem cell23_5080138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_5080138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080138 prefixEnd_5080138 := by exact prefixLift 5080138
  have htrace : WordTrace (prefixWord ++ tailWord_5080138) baseStart_5080138 baseEnd_5080138 := by
    simpa [prefixWord, tailWord_5080138, baseEnd_5080138] using wordTrace_append hprefix tailTrace_5080138
  have hstable : (prefixWord ++ tailWord_5080138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080138).length < 2 ^ (prefixWord ++ tailWord_5080138).sum := by decide
  have hdescent : baseEnd_5080138 < baseStart_5080138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080167 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5080167 : Nat := 118140960795 + 5080167 * 2 ^ 59
def prefixEnd_5080167 : Nat := 4983230072969 + 3 ^ 40 * 5080167 * 2
def baseEnd_5080167 : Nat := 2608567476109530556949243

theorem tailTrace_5080167 : CollatzResearch.WordTrace tailWord_5080167 prefixEnd_5080167 2608567476109530556949243 := by
  unfold tailWord_5080167
  simp only [CollatzResearch.WordTrace]
  refine ⟨185288912586430057293678755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123525941724286704862452503 185288912586430057293678755)
  ·
    refine ⟨277933368879645085940518133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185288912586430057293678755 277933368879645085940518133)
    ·
      refine ⟨26056253332466726806923575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277933368879645085940518133 26056253332466726806923575)
      ·
        refine ⟨39084379998700090210385363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26056253332466726806923575 39084379998700090210385363)
        ·
          refine ⟨58626569998050135315578045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39084379998700090210385363 58626569998050135315578045)
          ·
            refine ⟨21984963749268800743341767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58626569998050135315578045 21984963749268800743341767)
            ·
              refine ⟨32977445623903201115012651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21984963749268800743341767 32977445623903201115012651)
              ·
                refine ⟨49466168435854801672518977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32977445623903201115012651 49466168435854801672518977)
                ·
                  refine ⟨37099626326891101254389233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49466168435854801672518977 37099626326891101254389233)
                  ·
                    refine ⟨27824719745168325940791925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37099626326891101254389233 27824719745168325940791925)
                    ·
                      refine ⟨2608567476109530556949243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27824719745168325940791925 2608567476109530556949243)
                      ·
                        rfl

theorem cell23_5080167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5080167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080167 prefixEnd_5080167 := by exact prefixLift 5080167
  have htrace : WordTrace (prefixWord ++ tailWord_5080167) baseStart_5080167 baseEnd_5080167 := by
    simpa [prefixWord, tailWord_5080167, baseEnd_5080167] using wordTrace_append hprefix tailTrace_5080167
  have hstable : (prefixWord ++ tailWord_5080167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080167).length < 2 ^ (prefixWord ++ tailWord_5080167).sum := by decide
  have hdescent : baseEnd_5080167 < baseStart_5080167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080318 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_5080318 : Nat := 118140960795 + 5080318 * 2 ^ 59
def prefixEnd_5080318 : Nat := 4983230072969 + 3 ^ 40 * 5080318 * 2
def baseEnd_5080318 : Nat := 2608645011688359466161049

theorem tailTrace_5080318 : CollatzResearch.WordTrace tailWord_5080318 prefixEnd_5080318 2608645011688359466161049 := by
  unfold tailWord_5080318
  simp only [CollatzResearch.WordTrace]
  refine ⟨23161802501110376260303201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123529613339255340054950405 23161802501110376260303201)
  ·
    refine ⟨17371351875832782195227401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23161802501110376260303201 17371351875832782195227401)
    ·
      refine ⟨13028513906874586646420551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17371351875832782195227401 13028513906874586646420551)
      ·
        refine ⟨19542770860311879969630827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13028513906874586646420551 19542770860311879969630827)
        ·
          refine ⟨29314156290467819954446241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19542770860311879969630827 29314156290467819954446241)
          ·
            refine ⟨21985617217850864965834681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29314156290467819954446241 21985617217850864965834681)
            ·
              refine ⟨16489212913388148724376011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21985617217850864965834681 16489212913388148724376011)
              ·
                refine ⟨24733819370082223086564017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16489212913388148724376011 24733819370082223086564017)
                ·
                  refine ⟨18550364527561667314923013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24733819370082223086564017 18550364527561667314923013)
                  ·
                    refine ⟨3478193348917812621548065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18550364527561667314923013 3478193348917812621548065)
                    ·
                      refine ⟨2608645011688359466161049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478193348917812621548065 2608645011688359466161049)
                      ·
                        rfl

theorem cell23_5080318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_5080318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080318 prefixEnd_5080318 := by exact prefixLift 5080318
  have htrace : WordTrace (prefixWord ++ tailWord_5080318) baseStart_5080318 baseEnd_5080318 := by
    simpa [prefixWord, tailWord_5080318, baseEnd_5080318] using wordTrace_append hprefix tailTrace_5080318
  have hstable : (prefixWord ++ tailWord_5080318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080318).length < 2 ^ (prefixWord ++ tailWord_5080318).sum := by decide
  have hdescent : baseEnd_5080318 < baseStart_5080318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080362 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_5080362 : Nat := 118140960795 + 5080362 * 2 ^ 59
def prefixEnd_5080362 : Nat := 4983230072969 + 3 ^ 40 * 5080362 * 2
def baseEnd_5080362 : Nat := 869555868279052431336949

theorem tailTrace_5080362 : CollatzResearch.WordTrace tailWord_5080362 prefixEnd_5080362 869555868279052431336949 := by
  unfold tailWord_5080362
  simp only [CollatzResearch.WordTrace]
  refine ⟨46324006205180901399256835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123530683213815737064684893 46324006205180901399256835)
  ·
    refine ⟨69486009307771352098885253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46324006205180901399256835 69486009307771352098885253)
    ·
      refine ⟨13028626745207128518540985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69486009307771352098885253 13028626745207128518540985)
      ·
        refine ⟨9771470058905346388905739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13028626745207128518540985 9771470058905346388905739)
        ·
          refine ⟨14657205088358019583358609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9771470058905346388905739 14657205088358019583358609)
          ·
            refine ⟨10992903816268514687518957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14657205088358019583358609 10992903816268514687518957)
            ·
              refine ⟨4122338931100693007819609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10992903816268514687518957 4122338931100693007819609)
              ·
                refine ⟨3091754198325519755864707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122338931100693007819609 3091754198325519755864707)
                ·
                  refine ⟨4637631297488279633797061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091754198325519755864707 4637631297488279633797061)
                  ·
                    refine ⟨869555868279052431336949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4637631297488279633797061 869555868279052431336949)
                    ·
                      rfl

theorem cell23_5080362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_5080362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080362 prefixEnd_5080362 := by exact prefixLift 5080362
  have htrace : WordTrace (prefixWord ++ tailWord_5080362) baseStart_5080362 baseEnd_5080362 := by
    simpa [prefixWord, tailWord_5080362, baseEnd_5080362] using wordTrace_append hprefix tailTrace_5080362
  have hstable : (prefixWord ++ tailWord_5080362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080362).length < 2 ^ (prefixWord ++ tailWord_5080362).sum := by decide
  have hdescent : baseEnd_5080362 < baseStart_5080362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080384 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_5080384 : Nat := 118140960795 + 5080384 * 2 ^ 59
def prefixEnd_5080384 : Nat := 4983230072969 + 3 ^ 40 * 5080384 * 2
def baseEnd_5080384 : Nat := 869559633803852069311915

theorem tailTrace_5080384 : CollatzResearch.WordTrace tailWord_5080384 prefixEnd_5080384 869559633803852069311915 := by
  unfold tailWord_5080384
  simp only [CollatzResearch.WordTrace]
  refine ⟨92648413613321951677164103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123531218151095935569552137 92648413613321951677164103)
  ·
    refine ⟨138972620419982927515746155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92648413613321951677164103 138972620419982927515746155)
    ·
      refine ⟨208458930629974391273619233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138972620419982927515746155 208458930629974391273619233)
      ·
        refine ⟨156344197972480793455214425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208458930629974391273619233 156344197972480793455214425)
        ·
          refine ⟨117258148479360595091410819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156344197972480793455214425 117258148479360595091410819)
          ·
            refine ⟨175887222719040892637116229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117258148479360595091410819 175887222719040892637116229)
            ·
              refine ⟨32978854259820167369459293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175887222719040892637116229 32978854259820167369459293)
              ·
                refine ⟨12367070347432562763547235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32978854259820167369459293 12367070347432562763547235)
                ·
                  refine ⟨18550605521148844145320853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12367070347432562763547235 18550605521148844145320853)
                  ·
                    refine ⟨869559633803852069311915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18550605521148844145320853 869559633803852069311915)
                    ·
                      rfl

theorem cell23_5080384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_5080384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080384 prefixEnd_5080384 := by exact prefixLift 5080384
  have htrace : WordTrace (prefixWord ++ tailWord_5080384) baseStart_5080384 baseEnd_5080384 := by
    simpa [prefixWord, tailWord_5080384, baseEnd_5080384] using wordTrace_append hprefix tailTrace_5080384
  have hstable : (prefixWord ++ tailWord_5080384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080384).length < 2 ^ (prefixWord ++ tailWord_5080384).sum := by decide
  have hdescent : baseEnd_5080384 < baseStart_5080384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080388 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5080388 : Nat := 118140960795 + 5080388 * 2 ^ 59
def prefixEnd_5080388 : Nat := 4983230072969 + 3 ^ 40 * 5080388 * 2
def baseEnd_5080388 : Nat := 869560318444724730761909

theorem tailTrace_5080388 : CollatzResearch.WordTrace tailWord_5080388 prefixEnd_5080388 869560318444724730761909 := by
  unfold tailWord_5080388
  simp only [CollatzResearch.WordTrace]
  refine ⟨92648486559314706018736909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123531315412419608024982545 92648486559314706018736909)
  ·
    refine ⟨34743182459743014757026341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92648486559314706018736909 34743182459743014757026341)
    ·
      refine ⟨6514346711201815266942439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34743182459743014757026341 6514346711201815266942439)
      ·
        refine ⟨9771520066802722900413659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514346711201815266942439 9771520066802722900413659)
        ·
          refine ⟨14657280100204084350620489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9771520066802722900413659 14657280100204084350620489)
          ·
            refine ⟨10992960075153063262965367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14657280100204084350620489 10992960075153063262965367)
            ·
              refine ⟨16489440112729594894448051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10992960075153063262965367 16489440112729594894448051)
              ·
                refine ⟨24734160169094392341672077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16489440112729594894448051 24734160169094392341672077)
                ·
                  refine ⟨9275310063410397128127029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24734160169094392341672077 9275310063410397128127029)
                  ·
                    refine ⟨869560318444724730761909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9275310063410397128127029 869560318444724730761909)
                    ·
                      rfl

theorem cell23_5080388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5080388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080388 prefixEnd_5080388 := by exact prefixLift 5080388
  have htrace : WordTrace (prefixWord ++ tailWord_5080388) baseStart_5080388 baseEnd_5080388 := by
    simpa [prefixWord, tailWord_5080388, baseEnd_5080388] using wordTrace_append hprefix tailTrace_5080388
  have hstable : (prefixWord ++ tailWord_5080388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080388).length < 2 ^ (prefixWord ++ tailWord_5080388).sum := by decide
  have hdescent : baseEnd_5080388 < baseStart_5080388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080391 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_5080391 : Nat := 118140960795 + 5080391 * 2 ^ 59
def prefixEnd_5080391 : Nat := 4983230072969 + 3 ^ 40 * 5080391 * 2
def baseEnd_5080391 : Nat := 2608682495776137680548213

theorem tailTrace_5080391 : CollatzResearch.WordTrace tailWord_5080391 prefixEnd_5080391 2608682495776137680548213 := by
  unfold tailWord_5080391
  simp only [CollatzResearch.WordTrace]
  refine ⟨185297082537618543549833027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123531388358412362366555351 185297082537618543549833027)
  ·
    refine ⟨277945623806427815324749541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185297082537618543549833027 277945623806427815324749541)
    ·
      refine ⟨52114804463705215373390539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277945623806427815324749541 52114804463705215373390539)
      ·
        refine ⟨78172206695557823060085809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52114804463705215373390539 78172206695557823060085809)
        ·
          refine ⟨58629155021668367295064357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78172206695557823060085809 58629155021668367295064357)
          ·
            refine ⟨10992966566562818867824567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58629155021668367295064357 10992966566562818867824567)
            ·
              refine ⟨16489449849844228301736851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10992966566562818867824567 16489449849844228301736851)
              ·
                refine ⟨24734174774766342452605277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16489449849844228301736851 24734174774766342452605277)
                ·
                  refine ⟨9275315540537378419726979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24734174774766342452605277 9275315540537378419726979)
                  ·
                    refine ⟨13912973310806067629590469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9275315540537378419726979 13912973310806067629590469)
                    ·
                      refine ⟨2608682495776137680548213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13912973310806067629590469 2608682495776137680548213)
                      ·
                        rfl

theorem cell23_5080391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_5080391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080391 prefixEnd_5080391 := by exact prefixLift 5080391
  have htrace : WordTrace (prefixWord ++ tailWord_5080391) baseStart_5080391 baseEnd_5080391 := by
    simpa [prefixWord, tailWord_5080391, baseEnd_5080391] using wordTrace_append hprefix tailTrace_5080391
  have hstable : (prefixWord ++ tailWord_5080391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080391).length < 2 ^ (prefixWord ++ tailWord_5080391).sum := by decide
  have hdescent : baseEnd_5080391 < baseStart_5080391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080394 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_5080394 : Nat := 118140960795 + 5080394 * 2 ^ 59
def prefixEnd_5080394 : Nat := 4983230072969 + 3 ^ 40 * 5080394 * 2
def baseEnd_5080394 : Nat := 2608684036218101168810699

theorem tailTrace_5080394 : CollatzResearch.WordTrace tailWord_5080394 prefixEnd_5080394 2608684036218101168810699 := by
  unfold tailWord_5080394
  simp only [CollatzResearch.WordTrace]
  refine ⟨46324297989151918765548059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123531461304405116708128157 46324297989151918765548059)
  ·
    refine ⟨69486446983727878148322089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46324297989151918765548059 69486446983727878148322089)
    ·
      refine ⟨52114835237795908611241567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69486446983727878148322089 52114835237795908611241567)
      ·
        refine ⟨78172252856693862916862351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52114835237795908611241567 78172252856693862916862351)
        ·
          refine ⟨117258379285040794375293527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78172252856693862916862351 117258379285040794375293527)
          ·
            refine ⟨175887568927561191562940291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117258379285040794375293527 175887568927561191562940291)
            ·
              refine ⟨263831353391341787344410437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175887568927561191562940291 263831353391341787344410437)
              ·
                refine ⟨49468378760876585127076957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263831353391341787344410437 49468378760876585127076957)
                ·
                  refine ⟨18550642035328719422653859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49468378760876585127076957 18550642035328719422653859)
                  ·
                    refine ⟨27825963052993079133980789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18550642035328719422653859 27825963052993079133980789)
                    ·
                      refine ⟨2608684036218101168810699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27825963052993079133980789 2608684036218101168810699)
                      ·
                        rfl

theorem cell23_5080394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_5080394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080394 prefixEnd_5080394 := by exact prefixLift 5080394
  have htrace : WordTrace (prefixWord ++ tailWord_5080394) baseStart_5080394 baseEnd_5080394 := by
    simpa [prefixWord, tailWord_5080394, baseEnd_5080394] using wordTrace_append hprefix tailTrace_5080394
  have hstable : (prefixWord ++ tailWord_5080394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080394).length < 2 ^ (prefixWord ++ tailWord_5080394).sum := by decide
  have hdescent : baseEnd_5080394 < baseStart_5080394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080408 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 1, 1, 4]
def baseStart_5080408 : Nat := 118140960795 + 5080408 * 2 ^ 59
def prefixEnd_5080408 : Nat := 4983230072969 + 3 ^ 40 * 5080408 * 2
def baseEnd_5080408 : Nat := 2608691224947264114035635

theorem tailTrace_5080408 : CollatzResearch.WordTrace tailWord_5080408 prefixEnd_5080408 2608691224947264114035635 := by
  unfold tailWord_5080408
  simp only [CollatzResearch.WordTrace]
  refine ⟨92648851289278477726600939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123531801719037970302134585 92648851289278477726600939)
  ·
    refine ⟨138973276933917716589901409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92648851289278477726600939 138973276933917716589901409)
    ·
      refine ⟨104229957700438287442426057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138973276933917716589901409 104229957700438287442426057)
      ·
        refine ⟨78172468275328715581819543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104229957700438287442426057 78172468275328715581819543)
        ·
          refine ⟨117258702412993073372729315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78172468275328715581819543 117258702412993073372729315)
          ·
            refine ⟨175888053619489610059093973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117258702412993073372729315 175888053619489610059093973)
            ·
              refine ⟨4122376256706787735760015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 175888053619489610059093973 4122376256706787735760015)
              ·
                refine ⟨6183564385060181603640023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122376256706787735760015 6183564385060181603640023)
                ·
                  refine ⟨9275346577590272405460035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183564385060181603640023 9275346577590272405460035)
                  ·
                    refine ⟨13913019866385408608190053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9275346577590272405460035 13913019866385408608190053)
                    ·
                      refine ⟨2608691224947264114035635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13913019866385408608190053 2608691224947264114035635)
                      ·
                        rfl

theorem cell23_5080408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_5080408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080408 prefixEnd_5080408 := by exact prefixLift 5080408
  have htrace : WordTrace (prefixWord ++ tailWord_5080408) baseStart_5080408 baseEnd_5080408 := by
    simpa [prefixWord, tailWord_5080408, baseEnd_5080408] using wordTrace_append hprefix tailTrace_5080408
  have hstable : (prefixWord ++ tailWord_5080408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080408).length < 2 ^ (prefixWord ++ tailWord_5080408).sum := by decide
  have hdescent : baseEnd_5080408 < baseStart_5080408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080413 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5080413 : Nat := 118140960795 + 5080413 * 2 ^ 59
def prefixEnd_5080413 : Nat := 4983230072969 + 3 ^ 40 * 5080413 * 2
def baseEnd_5080413 : Nat := 869564597450178864824371

theorem tailTrace_5080413 : CollatzResearch.WordTrace tailWord_5080413 prefixEnd_5080413 869564597450178864824371 := by
  unfold tailWord_5080413
  simp only [CollatzResearch.WordTrace]
  refine ⟨185297884943538841307133893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123531923295692560871422595 185297884943538841307133893)
  ·
    refine ⟨34743353426913532745087605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185297884943538841307133893 34743353426913532745087605)
    ·
      refine ⟨3257189383773143694851963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34743353426913532745087605 3257189383773143694851963)
      ·
        refine ⟨4885784075659715542277945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257189383773143694851963 4885784075659715542277945)
        ·
          refine ⟨3664338056744786656708459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885784075659715542277945 3664338056744786656708459)
          ·
            refine ⟨5496507085117179985062689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664338056744786656708459 5496507085117179985062689)
            ·
              refine ⟨4122380313837884988797017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496507085117179985062689 4122380313837884988797017)
              ·
                refine ⟨3091785235378413741597763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122380313837884988797017 3091785235378413741597763)
                ·
                  refine ⟨4637677853067620612396645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091785235378413741597763 4637677853067620612396645)
                  ·
                    refine ⟨869564597450178864824371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4637677853067620612396645 869564597450178864824371)
                    ·
                      rfl

theorem cell23_5080413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5080413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080413 prefixEnd_5080413 := by exact prefixLift 5080413
  have htrace : WordTrace (prefixWord ++ tailWord_5080413) baseStart_5080413 baseEnd_5080413 := by
    simpa [prefixWord, tailWord_5080413, baseEnd_5080413] using wordTrace_append hprefix tailTrace_5080413
  have hstable : (prefixWord ++ tailWord_5080413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080413).length < 2 ^ (prefixWord ++ tailWord_5080413).sum := by decide
  have hdescent : baseEnd_5080413 < baseStart_5080413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080441 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_5080441 : Nat := 118140960795 + 5080441 * 2 ^ 59
def prefixEnd_5080441 : Nat := 4983230072969 + 3 ^ 40 * 5080441 * 2
def baseEnd_5080441 : Nat := 2608708169808862484922983

theorem tailTrace_5080441 : CollatzResearch.WordTrace tailWord_5080441 prefixEnd_5080441 2608708169808862484922983 := by
  unfold tailWord_5080441
  simp only [CollatzResearch.WordTrace]
  refine ⟨185298906187437402089153177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123532604124958268059435451 185298906187437402089153177)
  ·
    refine ⟨138974179640578051566864883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185298906187437402089153177 138974179640578051566864883)
    ·
      refine ⟨208461269460867077350297325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138974179640578051566864883 208461269460867077350297325)
      ·
        refine ⟨78172976047825154006361497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208461269460867077350297325 78172976047825154006361497)
        ·
          refine ⟨58629732035868865504771123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78172976047825154006361497 58629732035868865504771123)
          ·
            refine ⟨87944598053803298257156685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58629732035868865504771123 87944598053803298257156685)
            ·
              refine ⟨32979224270176236846433757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87944598053803298257156685 32979224270176236846433757)
              ·
                refine ⟨12367209101316088817412659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32979224270176236846433757 12367209101316088817412659)
                ·
                  refine ⟨18550813651974133226118989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12367209101316088817412659 18550813651974133226118989)
                  ·
                    refine ⟨6956555119490299959794621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18550813651974133226118989 6956555119490299959794621)
                    ·
                      refine ⟨2608708169808862484922983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6956555119490299959794621 2608708169808862484922983)
                      ·
                        rfl

theorem cell23_5080441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_5080441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080441 prefixEnd_5080441 := by exact prefixLift 5080441
  have htrace : WordTrace (prefixWord ++ tailWord_5080441) baseStart_5080441 baseEnd_5080441 := by
    simpa [prefixWord, tailWord_5080441, baseEnd_5080441] using wordTrace_append hprefix tailTrace_5080441
  have hstable : (prefixWord ++ tailWord_5080441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080441).length < 2 ^ (prefixWord ++ tailWord_5080441).sum := by decide
  have hdescent : baseEnd_5080441 < baseStart_5080441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080444 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_5080444 : Nat := 118140960795 + 5080444 * 2 ^ 59
def prefixEnd_5080444 : Nat := 4983230072969 + 3 ^ 40 * 5080444 * 2
def baseEnd_5080444 : Nat := 869569903416941991061823

theorem tailTrace_5080444 : CollatzResearch.WordTrace tailWord_5080444 prefixEnd_5080444 869569903416941991061823 := by
  unfold tailWord_5080444
  simp only [CollatzResearch.WordTrace]
  refine ⟨92649507803213266800756193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123532677070951022401008257 92649507803213266800756193)
  ·
    refine ⟨69487130852409950100567145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92649507803213266800756193 69487130852409950100567145)
    ·
      refine ⟨52115348139307462575425359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69487130852409950100567145 52115348139307462575425359)
      ·
        refine ⟨78173022208961193863138039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52115348139307462575425359 78173022208961193863138039)
        ·
          refine ⟨117259533313441790794707059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78173022208961193863138039 117259533313441790794707059)
          ·
            refine ⟨175889299970162686192060589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117259533313441790794707059 175889299970162686192060589)
            ·
              refine ⟨65958487488811007322022721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175889299970162686192060589 65958487488811007322022721)
              ·
                refine ⟨49468865616608255491517041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65958487488811007322022721 49468865616608255491517041)
                ·
                  refine ⟨37101649212456191618637781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49468865616608255491517041 37101649212456191618637781)
                  ·
                    refine ⟨869569903416941991061823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37101649212456191618637781 869569903416941991061823)
                    ·
                      rfl

theorem cell23_5080444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_5080444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080444 prefixEnd_5080444 := by exact prefixLift 5080444
  have htrace : WordTrace (prefixWord ++ tailWord_5080444) baseStart_5080444 baseEnd_5080444 := by
    simpa [prefixWord, tailWord_5080444, baseEnd_5080444] using wordTrace_append hprefix tailTrace_5080444
  have hstable : (prefixWord ++ tailWord_5080444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080444).length < 2 ^ (prefixWord ++ tailWord_5080444).sum := by decide
  have hdescent : baseEnd_5080444 < baseStart_5080444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080446 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5080446 : Nat := 118140960795 + 5080446 * 2 ^ 59
def prefixEnd_5080446 : Nat := 4983230072969 + 3 ^ 40 * 5080446 * 2
def baseEnd_5080446 : Nat := 2608710737212134965360461

theorem tailTrace_5080446 : CollatzResearch.WordTrace tailWord_5080446 prefixEnd_5080446 2608710737212134965360461 := by
  unfold tailWord_5080446
  simp only [CollatzResearch.WordTrace]
  refine ⟨23162386069052410992885649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123532725701612858628723461 23162386069052410992885649)
  ·
    refine ⟨17371789551789308244664237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23162386069052410992885649 17371789551789308244664237)
    ·
      refine ⟨6514421081920990591749089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17371789551789308244664237 6514421081920990591749089)
      ·
        refine ⟨4885815811440742943811817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6514421081920990591749089 4885815811440742943811817)
        ·
          refine ⟨3664361858580557207858863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885815811440742943811817 3664361858580557207858863)
          ·
            refine ⟨5496542787870835811788295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664361858580557207858863 5496542787870835811788295)
            ·
              refine ⟨8244814181806253717682443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496542787870835811788295 8244814181806253717682443)
              ·
                refine ⟨12367221272709380576523665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8244814181806253717682443 12367221272709380576523665)
                ·
                  refine ⟨9275415954532035432392749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12367221272709380576523665 9275415954532035432392749)
                  ·
                    refine ⟨3478280982949513287147281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9275415954532035432392749 3478280982949513287147281)
                    ·
                      refine ⟨2608710737212134965360461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478280982949513287147281 2608710737212134965360461)
                      ·
                        rfl

theorem cell23_5080446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5080446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080446 prefixEnd_5080446 := by exact prefixLift 5080446
  have htrace : WordTrace (prefixWord ++ tailWord_5080446) baseStart_5080446 baseEnd_5080446 := by
    simpa [prefixWord, tailWord_5080446, baseEnd_5080446] using wordTrace_append hprefix tailTrace_5080446
  have hstable : (prefixWord ++ tailWord_5080446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080446).length < 2 ^ (prefixWord ++ tailWord_5080446).sum := by decide
  have hdescent : baseEnd_5080446 < baseStart_5080446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080498 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_5080498 : Nat := 118140960795 + 5080498 * 2 ^ 59
def prefixEnd_5080498 : Nat := 4983230072969 + 3 ^ 40 * 5080498 * 2
def baseEnd_5080498 : Nat := 2608737438206168761910221

theorem tailTrace_5080498 : CollatzResearch.WordTrace tailWord_5080498 prefixEnd_5080498 2608737438206168761910221 := by
  unfold tailWord_5080498
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325246287057725205994537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123533990098820600549318765 46325246287057725205994537)
  ·
    refine ⟨34743934715293293904495903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46325246287057725205994537 34743934715293293904495903)
    ·
      refine ⟨52115902072939940856743855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34743934715293293904495903 52115902072939940856743855)
      ·
        refine ⟨78173853109409911285115783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52115902072939940856743855 78173853109409911285115783)
        ·
          refine ⟨117260779664114866927673675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78173853109409911285115783 117260779664114866927673675)
          ·
            refine ⟨175891169496172300391510513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117260779664114866927673675 175891169496172300391510513)
            ·
              refine ⟨131918377122129225293632885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175891169496172300391510513 131918377122129225293632885)
              ·
                refine ⟨12367347855199614871278083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131918377122129225293632885 12367347855199614871278083)
                ·
                  refine ⟨18551021782799422306917125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12367347855199614871278083 18551021782799422306917125)
                  ·
                    refine ⟨3478316584274891682546961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18551021782799422306917125 3478316584274891682546961)
                    ·
                      refine ⟨2608737438206168761910221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478316584274891682546961 2608737438206168761910221)
                      ·
                        rfl

theorem cell23_5080498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_5080498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080498 prefixEnd_5080498 := by exact prefixLift 5080498
  have htrace : WordTrace (prefixWord ++ tailWord_5080498) baseStart_5080498 baseEnd_5080498 := by
    simpa [prefixWord, tailWord_5080498, baseEnd_5080498] using wordTrace_append hprefix tailTrace_5080498
  have hstable : (prefixWord ++ tailWord_5080498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080498).length < 2 ^ (prefixWord ++ tailWord_5080498).sum := by decide
  have hdescent : baseEnd_5080498 < baseStart_5080498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080538 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_5080538 : Nat := 118140960795 + 5080538 * 2 ^ 59
def prefixEnd_5080538 : Nat := 4983230072969 + 3 ^ 40 * 5080538 * 2
def baseEnd_5080538 : Nat := 289861997492483178378893

theorem tailTrace_5080538 : CollatzResearch.WordTrace tailWord_5080538 prefixEnd_5080538 289861997492483178378893 := by
  unfold tailWord_5080538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325611017021496913858567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123534962712057325103622845 46325611017021496913858567)
  ·
    refine ⟨69488416525532245370787851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46325611017021496913858567 69488416525532245370787851)
    ·
      refine ⟨104232624788298368056181777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69488416525532245370787851 104232624788298368056181777)
      ·
        refine ⟨78174468591223776042136333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104232624788298368056181777 78174468591223776042136333)
        ·
          refine ⟨29315425721708916015801125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78174468591223776042136333 29315425721708916015801125)
          ·
            refine ⟨5496642322820421752962711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29315425721708916015801125 5496642322820421752962711)
            ·
              refine ⟨8244963484230632629444067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496642322820421752962711 8244963484230632629444067)
              ·
                refine ⟨12367445226345948944166101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8244963484230632629444067 12367445226345948944166101)
                ·
                  refine ⟨289861997492483178378893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12367445226345948944166101 289861997492483178378893)
                  ·
                    rfl

theorem cell23_5080538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_5080538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080538 prefixEnd_5080538 := by exact prefixLift 5080538
  have htrace : WordTrace (prefixWord ++ tailWord_5080538) baseStart_5080538 baseEnd_5080538 := by
    simpa [prefixWord, tailWord_5080538, baseEnd_5080538] using wordTrace_append hprefix tailTrace_5080538
  have hstable : (prefixWord ++ tailWord_5080538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080538).length < 2 ^ (prefixWord ++ tailWord_5080538).sum := by decide
  have hdescent : baseEnd_5080538 < baseStart_5080538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080549 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5080549 : Nat := 118140960795 + 5080549 * 2 ^ 59
def prefixEnd_5080549 : Nat := 4983230072969 + 3 ^ 40 * 5080549 * 2
def baseEnd_5080549 : Nat := 2608763625719548062372487

theorem tailTrace_5080549 : CollatzResearch.WordTrace tailWord_5080549 prefixEnd_5080549 2608763625719548062372487 := by
  unfold tailWord_5080549
  simp only [CollatzResearch.WordTrace]
  refine ⟨185302845271046136534084701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123535230180697424356056467 185302845271046136534084701)
  ·
    refine ⟨69488566976642301200281763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185302845271046136534084701 69488566976642301200281763)
    ·
      refine ⟨104232850464963451800422645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69488566976642301200281763 104232850464963451800422645)
      ·
        refine ⟨9771829731090323606289623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104232850464963451800422645 9771829731090323606289623)
        ·
          refine ⟨14657744596635485409434435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9771829731090323606289623 14657744596635485409434435)
          ·
            refine ⟨21986616894953228114151653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14657744596635485409434435 21986616894953228114151653)
            ·
              refine ⟨4122490667803730271403435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21986616894953228114151653 4122490667803730271403435)
              ·
                refine ⟨6183736001705595407105153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122490667803730271403435 6183736001705595407105153)
                ·
                  refine ⟨4637802001279196555328865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6183736001705595407105153 4637802001279196555328865)
                  ·
                    refine ⟨3478351500959397416496649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4637802001279196555328865 3478351500959397416496649)
                    ·
                      refine ⟨2608763625719548062372487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478351500959397416496649 2608763625719548062372487)
                      ·
                        rfl

theorem cell23_5080549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5080549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080549 prefixEnd_5080549 := by exact prefixLift 5080549
  have htrace : WordTrace (prefixWord ++ tailWord_5080549) baseStart_5080549 baseEnd_5080549 := by
    simpa [prefixWord, tailWord_5080549, baseEnd_5080549] using wordTrace_append hprefix tailTrace_5080549
  have hstable : (prefixWord ++ tailWord_5080549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080549).length < 2 ^ (prefixWord ++ tailWord_5080549).sum := by decide
  have hdescent : baseEnd_5080549 < baseStart_5080549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080568 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 2, 5]
def baseStart_5080568 : Nat := 118140960795 + 5080568 * 2 ^ 59
def prefixEnd_5080568 : Nat := 4983230072969 + 3 ^ 40 * 5080568 * 2
def baseEnd_5080568 : Nat := 869591127283994496011633

theorem tailTrace_5080568 : CollatzResearch.WordTrace tailWord_5080568 prefixEnd_5080568 869591127283994496011633 := by
  unfold tailWord_5080568
  simp only [CollatzResearch.WordTrace]
  refine ⟨92651769128988651389513179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123535692171984868519350905 92651769128988651389513179)
  ·
    refine ⟨138977653693482977084269769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92651769128988651389513179 138977653693482977084269769)
    ·
      refine ⟨104233240270112232813202327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138977653693482977084269769 104233240270112232813202327)
      ·
        refine ⟨156349860405168349219803491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104233240270112232813202327 156349860405168349219803491)
        ·
          refine ⟨234524790607752523829705237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156349860405168349219803491 234524790607752523829705237)
          ·
            refine ⟨10993349559738399554517433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 234524790607752523829705237 10993349559738399554517433)
            ·
              refine ⟨8245012169803799665888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10993349559738399554517433 8245012169803799665888075)
              ·
                refine ⟨12367518254705699498832113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8245012169803799665888075 12367518254705699498832113)
                ·
                  refine ⟨9275638691029274624124085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12367518254705699498832113 9275638691029274624124085)
                  ·
                    refine ⟨869591127283994496011633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9275638691029274624124085 869591127283994496011633)
                    ·
                      rfl

theorem cell23_5080568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_5080568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080568 prefixEnd_5080568 := by exact prefixLift 5080568
  have htrace : WordTrace (prefixWord ++ tailWord_5080568) baseStart_5080568 baseEnd_5080568 := by
    simpa [prefixWord, tailWord_5080568, baseEnd_5080568] using wordTrace_append hprefix tailTrace_5080568
  have hstable : (prefixWord ++ tailWord_5080568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080568).length < 2 ^ (prefixWord ++ tailWord_5080568).sum := by decide
  have hdescent : baseEnd_5080568 < baseStart_5080568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080571 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 4]
def baseStart_5080571 : Nat := 118140960795 + 5080571 * 2 ^ 59
def prefixEnd_5080571 : Nat := 4983230072969 + 3 ^ 40 * 5080571 * 2
def baseEnd_5080571 : Nat := 2608774922293946976297385

theorem tailTrace_5080571 : CollatzResearch.WordTrace tailWord_5080571 prefixEnd_5080571 2608774922293946976297385 := by
  unfold tailWord_5080571
  simp only [CollatzResearch.WordTrace]
  refine ⟨185303647676966434291385567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123535765117977622860923711 185303647676966434291385567)
  ·
    refine ⟨277955471515449651437078351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185303647676966434291385567 277955471515449651437078351)
    ·
      refine ⟨416933207273174477155617527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277955471515449651437078351 416933207273174477155617527)
      ·
        refine ⟨625399810909761715733426291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416933207273174477155617527 625399810909761715733426291)
        ·
          refine ⟨938099716364642573600139437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625399810909761715733426291 938099716364642573600139437)
          ·
            refine ⟨351787393636740965100052289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 938099716364642573600139437 351787393636740965100052289)
            ·
              refine ⟨263840545227555723825039217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351787393636740965100052289 263840545227555723825039217)
              ·
                refine ⟨197880408920666792868779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263840545227555723825039217 197880408920666792868779413)
                ·
                  refine ⟨9275644168156255915724035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 197880408920666792868779413 9275644168156255915724035)
                  ·
                    refine ⟨13913466252234383873586053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9275644168156255915724035 13913466252234383873586053)
                    ·
                      refine ⟨2608774922293946976297385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13913466252234383873586053 2608774922293946976297385)
                      ·
                        rfl

theorem cell23_5080571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 4].length) (baseStart_5080571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080571 prefixEnd_5080571 := by exact prefixLift 5080571
  have htrace : WordTrace (prefixWord ++ tailWord_5080571) baseStart_5080571 baseEnd_5080571 := by
    simpa [prefixWord, tailWord_5080571, baseEnd_5080571] using wordTrace_append hprefix tailTrace_5080571
  have hstable : (prefixWord ++ tailWord_5080571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080571).length < 2 ^ (prefixWord ++ tailWord_5080571).sum := by decide
  have hdescent : baseEnd_5080571 < baseStart_5080571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080589 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 5]
def baseStart_5080589 : Nat := 118140960795 + 5080589 * 2 ^ 59
def prefixEnd_5080589 : Nat := 4983230072969 + 3 ^ 40 * 5080589 * 2
def baseEnd_5080589 : Nat := 289864907216191989541367

theorem tailTrace_5080589 : CollatzResearch.WordTrace tailWord_5080589 prefixEnd_5080589 289864907216191989541367 := by
  unfold tailWord_5080589
  simp only [CollatzResearch.WordTrace]
  refine ⟨185304304190901223365540821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123536202793934148910360547 185304304190901223365540821)
  ·
    refine ⟨4343069629474247422629863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 185304304190901223365540821 4343069629474247422629863)
    ·
      refine ⟨6514604444211371133944795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4343069629474247422629863 6514604444211371133944795)
      ·
        refine ⟨9771906666317056700917193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514604444211371133944795 9771906666317056700917193)
        ·
          refine ⟨7328929999737792525687895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9771906666317056700917193 7328929999737792525687895)
          ·
            refine ⟨10993394999606688788531843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7328929999737792525687895 10993394999606688788531843)
            ·
              refine ⟨16490092499410033182797765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10993394999606688788531843 16490092499410033182797765)
              ·
                refine ⟨3091892343639381221774581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16490092499410033182797765 3091892343639381221774581)
                ·
                  refine ⟨289864907216191989541367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3091892343639381221774581 289864907216191989541367)
                  ·
                    rfl

theorem cell23_5080589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_5080589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080589 prefixEnd_5080589 := by exact prefixLift 5080589
  have htrace : WordTrace (prefixWord ++ tailWord_5080589) baseStart_5080589 baseEnd_5080589 := by
    simpa [prefixWord, tailWord_5080589, baseEnd_5080589] using wordTrace_append hprefix tailTrace_5080589
  have hstable : (prefixWord ++ tailWord_5080589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080589).length < 2 ^ (prefixWord ++ tailWord_5080589).sum := by decide
  have hdescent : baseEnd_5080589 < baseStart_5080589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080605 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_5080605 : Nat := 118140960795 + 5080605 * 2 ^ 59
def prefixEnd_5080605 : Nat := 4983230072969 + 3 ^ 40 * 5080605 * 2
def baseEnd_5080605 : Nat := 2608792380636199843272229

theorem tailTrace_5080605 : CollatzResearch.WordTrace tailWord_5080605 prefixEnd_5080605 2608792380636199843272229 := by
  unfold tailWord_5080605
  simp only [CollatzResearch.WordTrace]
  refine ⟨185304887758843258098123269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123536591839228838732082179 185304887758843258098123269)
  ·
    refine ⟨34744666454783110893398113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185304887758843258098123269 34744666454783110893398113)
    ·
      refine ⟨26058499841087333170048585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34744666454783110893398113 26058499841087333170048585)
      ·
        refine ⟨19543874880815499877536439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26058499841087333170048585 19543874880815499877536439)
        ·
          refine ⟨29315812321223249816304659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19543874880815499877536439 29315812321223249816304659)
          ·
            refine ⟨43973718481834874724456989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29315812321223249816304659 43973718481834874724456989)
            ·
              refine ⟨16490144430688078021671371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43973718481834874724456989 16490144430688078021671371)
              ·
                refine ⟨24735216646032117032507057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16490144430688078021671371 24735216646032117032507057)
                ·
                  refine ⟨18551412484524087774380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24735216646032117032507057 18551412484524087774380293)
                  ·
                    refine ⟨3478389840848266457696305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18551412484524087774380293 3478389840848266457696305)
                    ·
                      refine ⟨2608792380636199843272229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478389840848266457696305 2608792380636199843272229)
                      ·
                        rfl

theorem cell23_5080605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_5080605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080605 prefixEnd_5080605 := by exact prefixLift 5080605
  have htrace : WordTrace (prefixWord ++ tailWord_5080605) baseStart_5080605 baseEnd_5080605 := by
    simpa [prefixWord, tailWord_5080605, baseEnd_5080605] using wordTrace_append hprefix tailTrace_5080605
  have hstable : (prefixWord ++ tailWord_5080605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080605).length < 2 ^ (prefixWord ++ tailWord_5080605).sum := by decide
  have hdescent : baseEnd_5080605 < baseStart_5080605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080622 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5080622 : Nat := 118140960795 + 5080622 * 2 ^ 59
def prefixEnd_5080622 : Nat := 4983230072969 + 3 ^ 40 * 5080622 * 2
def baseEnd_5080622 : Nat := 2608801109807326276759651

theorem tailTrace_5080622 : CollatzResearch.WordTrace tailWord_5080622 prefixEnd_5080622 2608801109807326276759651 := by
  unfold tailWord_5080622
  simp only [CollatzResearch.WordTrace]
  refine ⟨23163188474972708750186515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123537005199854446667661413 23163188474972708750186515)
  ·
    refine ⟨34744782712459063125279773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23163188474972708750186515 34744782712459063125279773)
    ·
      refine ⟨13029293517172148671979915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34744782712459063125279773 13029293517172148671979915)
      ·
        refine ⟨19543940275758223007969873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029293517172148671979915 19543940275758223007969873)
        ·
          refine ⟨14657955206818667255977405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19543940275758223007969873 14657955206818667255977405)
          ·
            refine ⟨5496733202557000220991527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14657955206818667255977405 5496733202557000220991527)
            ·
              refine ⟨8245099803835500331487291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496733202557000220991527 8245099803835500331487291)
              ·
                refine ⟨12367649705753250497230937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8245099803835500331487291 12367649705753250497230937)
                ·
                  refine ⟨9275737279314937872923203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12367649705753250497230937 9275737279314937872923203)
                  ·
                    refine ⟨13913605918972406809384805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9275737279314937872923203 13913605918972406809384805)
                    ·
                      refine ⟨2608801109807326276759651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13913605918972406809384805 2608801109807326276759651)
                      ·
                        rfl

theorem cell23_5080622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5080622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080622 prefixEnd_5080622 := by exact prefixLift 5080622
  have htrace : WordTrace (prefixWord ++ tailWord_5080622) baseStart_5080622 baseEnd_5080622 := by
    simpa [prefixWord, tailWord_5080622, baseEnd_5080622] using wordTrace_append hprefix tailTrace_5080622
  have hstable : (prefixWord ++ tailWord_5080622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080622).length < 2 ^ (prefixWord ++ tailWord_5080622).sum := by decide
  have hdescent : baseEnd_5080622 < baseStart_5080622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080632 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 1, 4]
def baseStart_5080632 : Nat := 118140960795 + 5080632 * 2 ^ 59
def prefixEnd_5080632 : Nat := 4983230072969 + 3 ^ 40 * 5080632 * 2
def baseEnd_5080632 : Nat := 869602081537957079211535

theorem tailTrace_5080632 : CollatzResearch.WordTrace tailWord_5080632 prefixEnd_5080632 869602081537957079211535 := by
  unfold tailWord_5080632
  simp only [CollatzResearch.WordTrace]
  refine ⟨92652936264872720854678075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123537248353163627806237433 92652936264872720854678075)
  ·
    refine ⟨138979404397309081282017113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92652936264872720854678075 138979404397309081282017113)
    ·
      refine ⟨104234553297981810961512835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138979404397309081282017113 104234553297981810961512835)
      ·
        refine ⟨156351829946972716442269253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104234553297981810961512835 156351829946972716442269253)
        ·
          refine ⟨29315968115057384332925485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156351829946972716442269253 29315968115057384332925485)
          ·
            refine ⟨10993488043146519124847057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29315968115057384332925485 10993488043146519124847057)
            ·
              refine ⟨8245116032359889343635293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10993488043146519124847057 8245116032359889343635293)
              ·
                refine ⟨3091918512134958503863235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8245116032359889343635293 3091918512134958503863235)
                ·
                  refine ⟨4637877768202437755794853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091918512134958503863235 4637877768202437755794853)
                  ·
                    refine ⟨869602081537957079211535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4637877768202437755794853 869602081537957079211535)
                    ·
                      rfl

theorem cell23_5080632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_5080632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080632 prefixEnd_5080632 := by exact prefixLift 5080632
  have htrace : WordTrace (prefixWord ++ tailWord_5080632) baseStart_5080632 baseEnd_5080632 := by
    simpa [prefixWord, tailWord_5080632, baseEnd_5080632] using wordTrace_append hprefix tailTrace_5080632
  have hstable : (prefixWord ++ tailWord_5080632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080632).length < 2 ^ (prefixWord ++ tailWord_5080632).sum := by decide
  have hdescent : baseEnd_5080632 < baseStart_5080632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080675 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 1, 5]
def baseStart_5080675 : Nat := 118140960795 + 5080675 * 2 ^ 59
def prefixEnd_5080675 : Nat := 4983230072969 + 3 ^ 40 * 5080675 * 2
def baseEnd_5080675 : Nat := 869609441427338189798969

theorem tailTrace_5080675 : CollatzResearch.WordTrace tailWord_5080675 prefixEnd_5080675 869609441427338189798969 := by
  unfold tailWord_5080675
  simp only [CollatzResearch.WordTrace]
  refine ⟨185307440868589660053171479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123538293912393106702114319 185307440868589660053171479)
  ·
    refine ⟨277961161302884490079757219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185307440868589660053171479 277961161302884490079757219)
    ·
      refine ⟨416941741954326735119635829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277961161302884490079757219 416941741954326735119635829)
      ·
        refine ⟨39088288308218131417465859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 416941741954326735119635829 39088288308218131417465859)
        ·
          refine ⟨58632432462327197126198789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39088288308218131417465859 58632432462327197126198789)
          ·
            refine ⟨10993581086686349461162273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58632432462327197126198789 10993581086686349461162273)
            ·
              refine ⟨8245185815014762095871705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10993581086686349461162273 8245185815014762095871705)
              ·
                refine ⟨6183889361261071571903779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8245185815014762095871705 6183889361261071571903779)
                ·
                  refine ⟨9275834041891607357855669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183889361261071571903779 9275834041891607357855669)
                  ·
                    refine ⟨869609441427338189798969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9275834041891607357855669 869609441427338189798969)
                    ·
                      rfl

theorem cell23_5080675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 5].length) (baseStart_5080675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080675 prefixEnd_5080675 := by exact prefixLift 5080675
  have htrace : WordTrace (prefixWord ++ tailWord_5080675) baseStart_5080675 baseEnd_5080675 := by
    simpa [prefixWord, tailWord_5080675, baseEnd_5080675] using wordTrace_append hprefix tailTrace_5080675
  have hstable : (prefixWord ++ tailWord_5080675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080675).length < 2 ^ (prefixWord ++ tailWord_5080675).sum := by decide
  have hdescent : baseEnd_5080675 < baseStart_5080675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080705 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 4, 4]
def baseStart_5080705 : Nat := 118140960795 + 5080705 * 2 ^ 59
def prefixEnd_5080705 : Nat := 4983230072969 + 3 ^ 40 * 5080705 * 2
def baseEnd_5080705 : Nat := 869614576233883150673923

theorem tailTrace_5080705 : CollatzResearch.WordTrace tailWord_5080705 prefixEnd_5080705 869614576233883150673923 := by
  unfold tailWord_5080705
  simp only [CollatzResearch.WordTrace]
  refine ⟨185308535058480975176763569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123539023372320650117842379 185308535058480975176763569)
  ·
    refine ⟨138981401293860731382572677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185308535058480975176763569 138981401293860731382572677)
    ·
      refine ⟨26059012742598887134232377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138981401293860731382572677 26059012742598887134232377)
      ·
        refine ⟨19544259556949165350674283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26059012742598887134232377 19544259556949165350674283)
        ·
          refine ⟨29316389335423748026011425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19544259556949165350674283 29316389335423748026011425)
          ·
            refine ⟨21987292001567811019508569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29316389335423748026011425 21987292001567811019508569)
            ·
              refine ⟨16490469001175858264631427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21987292001567811019508569 16490469001175858264631427)
              ·
                refine ⟨24735703501763787396947141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16490469001175858264631427 24735703501763787396947141)
                ·
                  refine ⟨4637944406580710136927589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24735703501763787396947141 4637944406580710136927589)
                  ·
                    refine ⟨869614576233883150673923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4637944406580710136927589 869614576233883150673923)
                    ·
                      rfl

theorem cell23_5080705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_5080705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080705 prefixEnd_5080705 := by exact prefixLift 5080705
  have htrace : WordTrace (prefixWord ++ tailWord_5080705) baseStart_5080705 baseEnd_5080705 := by
    simpa [prefixWord, tailWord_5080705, baseEnd_5080705] using wordTrace_append hprefix tailTrace_5080705
  have hstable : (prefixWord ++ tailWord_5080705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080705).length < 2 ^ (prefixWord ++ tailWord_5080705).sum := by decide
  have hdescent : baseEnd_5080705 < baseStart_5080705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080718 : List Nat := [4, 1, 1, 3, 1, 2, 1, 10]
def baseStart_5080718 : Nat := 118140960795 + 5080718 * 2 ^ 59
def prefixEnd_5080718 : Nat := 4983230072969 + 3 ^ 40 * 5080718 * 2
def baseEnd_5080718 : Nat := 96624089035191033376267

theorem tailTrace_5080718 : CollatzResearch.WordTrace tailWord_5080718 prefixEnd_5080718 96624089035191033376267 := by
  unfold tailWord_5080718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23163626150929234799623351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123539339471622585597991205 23163626150929234799623351)
  ·
    refine ⟨34745439226393852199435027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23163626150929234799623351 34745439226393852199435027)
    ·
      refine ⟨52118158839590778299152541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34745439226393852199435027 52118158839590778299152541)
      ·
        refine ⟨19544309564846541862182203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52118158839590778299152541 19544309564846541862182203)
        ·
          refine ⟨29316464347269812793273305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19544309564846541862182203 29316464347269812793273305)
          ·
            refine ⟨21987348260452359594954979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29316464347269812793273305 21987348260452359594954979)
            ·
              refine ⟨32981022390678539392432469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21987348260452359594954979 32981022390678539392432469)
              ·
                refine ⟨96624089035191033376267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32981022390678539392432469 96624089035191033376267)
                ·
                  rfl

theorem cell23_5080718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_5080718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080718 prefixEnd_5080718 := by exact prefixLift 5080718
  have htrace : WordTrace (prefixWord ++ tailWord_5080718) baseStart_5080718 baseEnd_5080718 := by
    simpa [prefixWord, tailWord_5080718, baseEnd_5080718] using wordTrace_append hprefix tailTrace_5080718
  have hstable : (prefixWord ++ tailWord_5080718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080718).length < 2 ^ (prefixWord ++ tailWord_5080718).sum := by decide
  have hdescent : baseEnd_5080718 < baseStart_5080718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080732 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5080732 : Nat := 118140960795 + 5080732 * 2 ^ 59
def prefixEnd_5080732 : Nat := 4983230072969 + 3 ^ 40 * 5080732 * 2
def baseEnd_5080732 : Nat := 2608857592679320846384145

theorem tailTrace_5080732 : CollatzResearch.WordTrace tailWord_5080732 prefixEnd_5080732 2608857592679320846384145 := by
  unfold tailWord_5080732
  simp only [CollatzResearch.WordTrace]
  refine ⟨92654759914691579393998225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123539679886255439191997633 92654759914691579393998225)
  ·
    refine ⟨69491069936018684545498669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92654759914691579393998225 69491069936018684545498669)
    ·
      refine ⟨26059151226007006704562001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69491069936018684545498669 26059151226007006704562001)
      ·
        refine ⟨19544363419505255028421501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26059151226007006704562001 19544363419505255028421501)
        ·
          refine ⟨7329136282314470635658063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19544363419505255028421501 7329136282314470635658063)
          ·
            refine ⟨10993704423471705953487095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329136282314470635658063 10993704423471705953487095)
            ·
              refine ⟨16490556635207558930230643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10993704423471705953487095 16490556635207558930230643)
              ·
                refine ⟨24735834952811338395345965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16490556635207558930230643 24735834952811338395345965)
                ·
                  refine ⟨9275938107304251898254737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24735834952811338395345965 9275938107304251898254737)
                  ·
                    refine ⟨6956953580478188923691053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9275938107304251898254737 6956953580478188923691053)
                    ·
                      refine ⟨2608857592679320846384145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6956953580478188923691053 2608857592679320846384145)
                      ·
                        rfl

theorem cell23_5080732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5080732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080732 prefixEnd_5080732 := by exact prefixLift 5080732
  have htrace : WordTrace (prefixWord ++ tailWord_5080732) baseStart_5080732 baseEnd_5080732 := by
    simpa [prefixWord, tailWord_5080732, baseEnd_5080732] using wordTrace_append hprefix tailTrace_5080732
  have hstable : (prefixWord ++ tailWord_5080732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080732).length < 2 ^ (prefixWord ++ tailWord_5080732).sum := by decide
  have hdescent : baseEnd_5080732 < baseStart_5080732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080749 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5080749 : Nat := 118140960795 + 5080749 * 2 ^ 59
def prefixEnd_5080749 : Nat := 4983230072969 + 3 ^ 40 * 5080749 * 2
def baseEnd_5080749 : Nat := 2608866321850447279871567

theorem tailTrace_5080749 : CollatzResearch.WordTrace tailWord_5080749 prefixEnd_5080749 2608866321850447279871567 := by
  unfold tailWord_5080749
  simp only [CollatzResearch.WordTrace]
  refine ⟨185310139870321570691365301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123540093246881047127576867 185310139870321570691365301)
  ·
    refine ⟨17372825612842647252315497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185310139870321570691365301 17372825612842647252315497)
    ·
      refine ⟨13029619209631985439236623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17372825612842647252315497 13029619209631985439236623)
      ·
        refine ⟨19544428814447978158854935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029619209631985439236623 19544428814447978158854935)
        ·
          refine ⟨29316643221671967238282403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19544428814447978158854935 29316643221671967238282403)
          ·
            refine ⟨43974964832507950857423605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29316643221671967238282403 43974964832507950857423605)
            ·
              refine ⟨4122652953047620392883463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43974964832507950857423605 4122652953047620392883463)
              ·
                refine ⟨6183979429571430589325195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122652953047620392883463 6183979429571430589325195)
                ·
                  refine ⟨9275969144357145883987793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183979429571430589325195 9275969144357145883987793)
                  ·
                    refine ⟨6956976858267859412990845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9275969144357145883987793 6956976858267859412990845)
                    ·
                      refine ⟨2608866321850447279871567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6956976858267859412990845 2608866321850447279871567)
                      ·
                        rfl

theorem cell23_5080749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5080749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080749 prefixEnd_5080749 := by exact prefixLift 5080749
  have htrace : WordTrace (prefixWord ++ tailWord_5080749) baseStart_5080749 baseEnd_5080749 := by
    simpa [prefixWord, tailWord_5080749, baseEnd_5080749] using wordTrace_append hprefix tailTrace_5080749
  have hstable : (prefixWord ++ tailWord_5080749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080749).length < 2 ^ (prefixWord ++ tailWord_5080749).sum := by decide
  have hdescent : baseEnd_5080749 < baseStart_5080749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080762 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_5080762 : Nat := 118140960795 + 5080762 * 2 ^ 59
def prefixEnd_5080762 : Nat := 4983230072969 + 3 ^ 40 * 5080762 * 2
def baseEnd_5080762 : Nat := 2608872997098955729009007

theorem tailTrace_5080762 : CollatzResearch.WordTrace tailWord_5080762 prefixEnd_5080762 2608872997098955729009007 := by
  unfold tailWord_5080762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46327653504818618477897135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123540409346182982607725693 46327653504818618477897135)
  ·
    refine ⟨69491480257227927716845703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46327653504818618477897135 69491480257227927716845703)
    ·
      refine ⟨104237220385841891575268555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69491480257227927716845703 104237220385841891575268555)
      ·
        refine ⟨156355830578762837362902833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104237220385841891575268555 156355830578762837362902833)
        ·
          refine ⟨117266872934072128022177125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156355830578762837362902833 117266872934072128022177125)
          ·
            refine ⟨21987538675138524004158211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117266872934072128022177125 21987538675138524004158211)
            ·
              refine ⟨32981308012707786006237317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21987538675138524004158211 32981308012707786006237317)
              ·
                refine ⟨6183995252382709876169497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32981308012707786006237317 6183995252382709876169497)
                ·
                  refine ⟨4637996439287032407127123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6183995252382709876169497 4637996439287032407127123)
                  ·
                    refine ⟨6956994658930548610690685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4637996439287032407127123 6956994658930548610690685)
                    ·
                      refine ⟨2608872997098955729009007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6956994658930548610690685 2608872997098955729009007)
                      ·
                        rfl

theorem cell23_5080762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_5080762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080762 prefixEnd_5080762 := by exact prefixLift 5080762
  have htrace : WordTrace (prefixWord ++ tailWord_5080762) baseStart_5080762 baseEnd_5080762 := by
    simpa [prefixWord, tailWord_5080762, baseEnd_5080762] using wordTrace_append hprefix tailTrace_5080762
  have hstable : (prefixWord ++ tailWord_5080762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080762).length < 2 ^ (prefixWord ++ tailWord_5080762).sum := by decide
  have hdescent : baseEnd_5080762 < baseStart_5080762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080768 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_5080768 : Nat := 118140960795 + 5080768 * 2 ^ 59
def prefixEnd_5080768 : Nat := 4983230072969 + 3 ^ 40 * 5080768 * 2
def baseEnd_5080768 : Nat := 2608876077982882705533979

theorem tailTrace_5080768 : CollatzResearch.WordTrace tailWord_5080768 prefixEnd_5080768 2608876077982882705533979 := by
  unfold tailWord_5080768
  simp only [CollatzResearch.WordTrace]
  refine ⟨92655416428626368468153479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123540555238168491290871305 92655416428626368468153479)
  ·
    refine ⟨138983124642939552702230219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92655416428626368468153479 138983124642939552702230219)
    ·
      refine ⟨208474686964409329053345329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138983124642939552702230219 208474686964409329053345329)
      ·
        refine ⟨156356015223306996790008997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208474686964409329053345329 156356015223306996790008997)
        ·
          refine ⟨29316752854370061898126687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156356015223306996790008997 29316752854370061898126687)
          ·
            refine ⟨43975129281555092847190031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29316752854370061898126687 43975129281555092847190031)
            ·
              refine ⟨65962693922332639270785047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43975129281555092847190031 65962693922332639270785047)
              ·
                refine ⟨98944040883498958906177571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65962693922332639270785047 98944040883498958906177571)
                ·
                  refine ⟨148416061325248438359266357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98944040883498958906177571 148416061325248438359266357)
                  ·
                    refine ⟨13914005749242041096181221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148416061325248438359266357 13914005749242041096181221)
                    ·
                      refine ⟨2608876077982882705533979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13914005749242041096181221 2608876077982882705533979)
                      ·
                        rfl

theorem cell23_5080768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_5080768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080768 prefixEnd_5080768 := by exact prefixLift 5080768
  have htrace : WordTrace (prefixWord ++ tailWord_5080768) baseStart_5080768 baseEnd_5080768 := by
    simpa [prefixWord, tailWord_5080768, baseEnd_5080768] using wordTrace_append hprefix tailTrace_5080768
  have hstable : (prefixWord ++ tailWord_5080768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080768).length < 2 ^ (prefixWord ++ tailWord_5080768).sum := by decide
  have hdescent : baseEnd_5080768 < baseStart_5080768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080772 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5080772 : Nat := 118140960795 + 5080772 * 2 ^ 59
def prefixEnd_5080772 : Nat := 4983230072969 + 3 ^ 40 * 5080772 * 2
def baseEnd_5080772 : Nat := 2608878131905500689883961

theorem tailTrace_5080772 : CollatzResearch.WordTrace tailWord_5080772 prefixEnd_5080772 2608878131905500689883961 := by
  unfold tailWord_5080772
  simp only [CollatzResearch.WordTrace]
  refine ⟨92655489374619122809726285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123540652499492163746301713 92655489374619122809726285)
  ·
    refine ⟨34745808515482171053647357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92655489374619122809726285 34745808515482171053647357)
    ·
      refine ⟨13029678193305814145117759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34745808515482171053647357 13029678193305814145117759)
      ·
        refine ⟨19544517289958721217676639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029678193305814145117759 19544517289958721217676639)
        ·
          refine ⟨29316775934938081826514959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19544517289958721217676639 29316775934938081826514959)
          ·
            refine ⟨43975163902407122739772439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29316775934938081826514959 43975163902407122739772439)
            ·
              refine ⟨65962745853610684109658659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43975163902407122739772439 65962745853610684109658659)
              ·
                refine ⟨98944118780416026164487989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65962745853610684109658659 98944118780416026164487989)
                ·
                  refine ⟨9276011135664002452920749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98944118780416026164487989 9276011135664002452920749)
                  ·
                    refine ⟨3478504175874000919845281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9276011135664002452920749 3478504175874000919845281)
                    ·
                      refine ⟨2608878131905500689883961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478504175874000919845281 2608878131905500689883961)
                      ·
                        rfl

theorem cell23_5080772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5080772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080772 prefixEnd_5080772 := by exact prefixLift 5080772
  have htrace : WordTrace (prefixWord ++ tailWord_5080772) baseStart_5080772 baseEnd_5080772 := by
    simpa [prefixWord, tailWord_5080772, baseEnd_5080772] using wordTrace_append hprefix tailTrace_5080772
  have hstable : (prefixWord ++ tailWord_5080772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080772).length < 2 ^ (prefixWord ++ tailWord_5080772).sum := by decide
  have hdescent : baseEnd_5080772 < baseStart_5080772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080819 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 2, 2, 2]
def baseStart_5080819 : Nat := 118140960795 + 5080819 * 2 ^ 59
def prefixEnd_5080819 : Nat := 4983230072969 + 3 ^ 40 * 5080819 * 2
def baseEnd_5080819 : Nat := 2608902265496262005996245

theorem tailTrace_5080819 : CollatzResearch.WordTrace tailWord_5080819 prefixEnd_5080819 2608902265496262005996245 := by
  unfold tailWord_5080819
  simp only [CollatzResearch.WordTrace]
  refine ⟨185312692980067972646413511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123541795320045315097609007 185312692980067972646413511)
  ·
    refine ⟨277969039470101958969620267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185312692980067972646413511 277969039470101958969620267)
    ·
      refine ⟨416953559205152938454430401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277969039470101958969620267 416953559205152938454430401)
      ·
        refine ⟨312715169403864703840822801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416953559205152938454430401 312715169403864703840822801)
        ·
          refine ⟨234536377052898527880617101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312715169403864703840822801 234536377052898527880617101)
          ·
            refine ⟨87951141394836947955231413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234536377052898527880617101 87951141394836947955231413)
            ·
              refine ⟨8245419505765963870802945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87951141394836947955231413 8245419505765963870802945)
              ·
                refine ⟨6184064629324472903102209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8245419505765963870802945 6184064629324472903102209)
                ·
                  refine ⟨4638048471993354677326657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6184064629324472903102209 4638048471993354677326657)
                  ·
                    refine ⟨3478536353995016007994993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638048471993354677326657 3478536353995016007994993)
                    ·
                      refine ⟨2608902265496262005996245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478536353995016007994993 2608902265496262005996245)
                      ·
                        rfl

theorem cell23_5080819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 2, 2].length) (baseStart_5080819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080819 prefixEnd_5080819 := by exact prefixLift 5080819
  have htrace : WordTrace (prefixWord ++ tailWord_5080819) baseStart_5080819 baseEnd_5080819 := by
    simpa [prefixWord, tailWord_5080819, baseEnd_5080819] using wordTrace_append hprefix tailTrace_5080819
  have hstable : (prefixWord ++ tailWord_5080819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080819).length < 2 ^ (prefixWord ++ tailWord_5080819).sum := by decide
  have hdescent : baseEnd_5080819 < baseStart_5080819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080835 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 3]
def baseStart_5080835 : Nat := 118140960795 + 5080835 * 2 ^ 59
def prefixEnd_5080835 : Nat := 4983230072969 + 3 ^ 40 * 5080835 * 2
def baseEnd_5080835 : Nat := 2608910481186733943396171

theorem tailTrace_5080835 : CollatzResearch.WordTrace tailWord_5080835 prefixEnd_5080835 2608910481186733943396171 := by
  unfold tailWord_5080835
  simp only [CollatzResearch.WordTrace]
  refine ⟨185313276548010007378995959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123542184365340004919330639 185313276548010007378995959)
  ·
    refine ⟨277969914822015011068493939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185313276548010007378995959 277969914822015011068493939)
    ·
      refine ⟨416954872233022516602740909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277969914822015011068493939 416954872233022516602740909)
      ·
        refine ⟨156358077087383443726027841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416954872233022516602740909 156358077087383443726027841)
        ·
          refine ⟨117268557815537582794520881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156358077087383443726027841 117268557815537582794520881)
          ·
            refine ⟨87951418361653187095890661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117268557815537582794520881 87951418361653187095890661)
            ·
              refine ⟨16490890942809972580479499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87951418361653187095890661 16490890942809972580479499)
              ·
                refine ⟨24736336414214958870719249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16490890942809972580479499 24736336414214958870719249)
                ·
                  refine ⟨18552252310661219153039437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24736336414214958870719249 18552252310661219153039437)
                  ·
                    refine ⟨6957094616497957182389789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18552252310661219153039437 6957094616497957182389789)
                    ·
                      refine ⟨2608910481186733943396171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957094616497957182389789 2608910481186733943396171)
                      ·
                        rfl

theorem cell23_5080835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_5080835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080835 prefixEnd_5080835 := by exact prefixLift 5080835
  have htrace : WordTrace (prefixWord ++ tailWord_5080835) baseStart_5080835 baseEnd_5080835 := by
    simpa [prefixWord, tailWord_5080835, baseEnd_5080835] using wordTrace_append hprefix tailTrace_5080835
  have hstable : (prefixWord ++ tailWord_5080835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080835).length < 2 ^ (prefixWord ++ tailWord_5080835).sum := by decide
  have hdescent : baseEnd_5080835 < baseStart_5080835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080855 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 1, 7]
def baseStart_5080855 : Nat := 118140960795 + 5080855 * 2 ^ 59
def prefixEnd_5080855 : Nat := 4983230072969 + 3 ^ 40 * 5080855 * 2
def baseEnd_5080855 : Nat := 869640250266607955048693

theorem tailTrace_5080855 : CollatzResearch.WordTrace tailWord_5080855 prefixEnd_5080855 869640250266607955048693 := by
  unfold tailWord_5080855
  simp only [CollatzResearch.WordTrace]
  refine ⟨185314006007937550794724019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123542670671958367196482679 185314006007937550794724019)
  ·
    refine ⟨277971009011906326192086029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185314006007937550794724019 277971009011906326192086029)
    ·
      refine ⟨104239128379464872322032261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277971009011906326192086029 104239128379464872322032261)
      ·
        refine ⟨19544836571149663560381049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104239128379464872322032261 19544836571149663560381049)
        ·
          refine ⟨14658627428362247670285787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19544836571149663560381049 14658627428362247670285787)
          ·
            refine ⟨21987941142543371505428681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14658627428362247670285787 21987941142543371505428681)
            ·
              refine ⟨16490955856907528629071511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21987941142543371505428681 16490955856907528629071511)
              ·
                refine ⟨24736433785361292943607267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16490955856907528629071511 24736433785361292943607267)
                ·
                  refine ⟨37104650678041939415410901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24736433785361292943607267 37104650678041939415410901)
                  ·
                    refine ⟨869640250266607955048693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37104650678041939415410901 869640250266607955048693)
                    ·
                      rfl

theorem cell23_5080855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_5080855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080855 prefixEnd_5080855 := by exact prefixLift 5080855
  have htrace : WordTrace (prefixWord ++ tailWord_5080855) baseStart_5080855 baseEnd_5080855 := by
    simpa [prefixWord, tailWord_5080855, baseEnd_5080855] using wordTrace_append hprefix tailTrace_5080855
  have hstable : (prefixWord ++ tailWord_5080855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080855).length < 2 ^ (prefixWord ++ tailWord_5080855).sum := by decide
  have hdescent : baseEnd_5080855 < baseStart_5080855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080872 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5080872 : Nat := 118140960795 + 5080872 * 2 ^ 59
def prefixEnd_5080872 : Nat := 4983230072969 + 3 ^ 40 * 5080872 * 2
def baseEnd_5080872 : Nat := 869643159990316766211167

theorem tailTrace_5080872 : CollatzResearch.WordTrace tailWord_5080872 prefixEnd_5080872 869643159990316766211167 := by
  unfold tailWord_5080872
  simp only [CollatzResearch.WordTrace]
  refine ⟨92657313024437981349046435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123543084032583975132061913 92657313024437981349046435)
  ·
    refine ⟨138985969536656972023569653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92657313024437981349046435 138985969536656972023569653)
    ·
      refine ⟨13029934644061591127209655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138985969536656972023569653 13029934644061591127209655)
      ·
        refine ⟨19544901966092386690814483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029934644061591127209655 19544901966092386690814483)
        ·
          refine ⟨29317352949138580036221725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19544901966092386690814483 29317352949138580036221725)
          ·
            refine ⟨10994007355926967513583147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29317352949138580036221725 10994007355926967513583147)
            ·
              refine ⟨16491011033890451270374721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10994007355926967513583147 16491011033890451270374721)
              ·
                refine ⟨12368258275417838452781041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16491011033890451270374721 12368258275417838452781041)
                ·
                  refine ⟨9276193706563378839585781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12368258275417838452781041 9276193706563378839585781)
                  ·
                    refine ⟨869643159990316766211167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9276193706563378839585781 869643159990316766211167)
                    ·
                      rfl

theorem cell23_5080872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5080872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080872 prefixEnd_5080872 := by exact prefixLift 5080872
  have htrace : WordTrace (prefixWord ++ tailWord_5080872) baseStart_5080872 baseEnd_5080872 := by
    simpa [prefixWord, tailWord_5080872, baseEnd_5080872] using wordTrace_append hprefix tailTrace_5080872
  have hstable : (prefixWord ++ tailWord_5080872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080872).length < 2 ^ (prefixWord ++ tailWord_5080872).sum := by decide
  have hdescent : baseEnd_5080872 < baseStart_5080872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080892 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_5080892 : Nat := 118140960795 + 5080892 * 2 ^ 59
def prefixEnd_5080892 : Nat := 4983230072969 + 3 ^ 40 * 5080892 * 2
def baseEnd_5080892 : Nat := 2608939749584040220383409

theorem tailTrace_5080892 : CollatzResearch.WordTrace tailWord_5080892 prefixEnd_5080892 2608939749584040220383409 := by
  unfold tailWord_5080892
  simp only [CollatzResearch.WordTrace]
  refine ⟨92657677754401753056910465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123543570339202337409213953 92657677754401753056910465)
  ·
    refine ⟨69493258315801314792682849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92657677754401753056910465 69493258315801314792682849)
    ·
      refine ⟨52119943736850986094512137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69493258315801314792682849 52119943736850986094512137)
      ·
        refine ⟨39089957802638239570884103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52119943736850986094512137 39089957802638239570884103)
        ·
          refine ⟨58634936703957359356326155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39089957802638239570884103 58634936703957359356326155)
          ·
            refine ⟨87952405055936039034489233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58634936703957359356326155 87952405055936039034489233)
            ·
              refine ⟨65964303791952029275866925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87952405055936039034489233 65964303791952029275866925)
              ·
                refine ⟨24736613921982010978450097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65964303791952029275866925 24736613921982010978450097)
                ·
                  refine ⟨18552460441486508233837573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24736613921982010978450097 18552460441486508233837573)
                  ·
                    refine ⟨3478586332778720293844545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18552460441486508233837573 3478586332778720293844545)
                    ·
                      refine ⟨2608939749584040220383409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478586332778720293844545 2608939749584040220383409)
                      ·
                        rfl

theorem cell23_5080892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_5080892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080892 prefixEnd_5080892 := by exact prefixLift 5080892
  have htrace : WordTrace (prefixWord ++ tailWord_5080892) baseStart_5080892 baseEnd_5080892 := by
    simpa [prefixWord, tailWord_5080892, baseEnd_5080892] using wordTrace_append hprefix tailTrace_5080892
  have hstable : (prefixWord ++ tailWord_5080892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080892).length < 2 ^ (prefixWord ++ tailWord_5080892).sum := by decide
  have hdescent : baseEnd_5080892 < baseStart_5080892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080909 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5080909 : Nat := 118140960795 + 5080909 * 2 ^ 59
def prefixEnd_5080909 : Nat := 4983230072969 + 3 ^ 40 * 5080909 * 2
def baseEnd_5080909 : Nat := 2608948478755166653870831

theorem tailTrace_5080909 : CollatzResearch.WordTrace tailWord_5080909 prefixEnd_5080909 2608948478755166653870831 := by
  unfold tailWord_5080909
  simp only [CollatzResearch.WordTrace]
  refine ⟨185315975549741918017189781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123543983699827945344793187 185315975549741918017189781)
  ·
    refine ⟨8686686353894152407055771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 185315975549741918017189781 8686686353894152407055771)
    ·
      refine ⟨13030029530841228610583657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8686686353894152407055771 13030029530841228610583657)
      ·
        refine ⟨9772522148130921457937743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13030029530841228610583657 9772522148130921457937743)
        ·
          refine ⟨14658783222196382186906615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9772522148130921457937743 14658783222196382186906615)
          ·
            refine ⟨21988174833294573280359923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14658783222196382186906615 21988174833294573280359923)
            ·
              refine ⟨32982262249941859920539885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21988174833294573280359923 32982262249941859920539885)
              ·
                refine ⟨12368348343728197470202457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32982262249941859920539885 12368348343728197470202457)
                ·
                  refine ⟨9276261257796148102651843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12368348343728197470202457 9276261257796148102651843)
                  ·
                    refine ⟨13914391886694222153977765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9276261257796148102651843 13914391886694222153977765)
                    ·
                      refine ⟨2608948478755166653870831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13914391886694222153977765 2608948478755166653870831)
                      ·
                        rfl

theorem cell23_5080909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5080909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080909 prefixEnd_5080909 := by exact prefixLift 5080909
  have htrace : WordTrace (prefixWord ++ tailWord_5080909) baseStart_5080909 baseEnd_5080909 := by
    simpa [prefixWord, tailWord_5080909, baseEnd_5080909] using wordTrace_append hprefix tailTrace_5080909
  have hstable : (prefixWord ++ tailWord_5080909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080909).length < 2 ^ (prefixWord ++ tailWord_5080909).sum := by decide
  have hdescent : baseEnd_5080909 < baseStart_5080909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080935 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5080935 : Nat := 118140960795 + 5080935 * 2 ^ 59
def prefixEnd_5080935 : Nat := 4983230072969 + 3 ^ 40 * 5080935 * 2
def baseEnd_5080935 : Nat := 2608961829252183552145711

theorem tailTrace_5080935 : CollatzResearch.WordTrace tailWord_5080935 prefixEnd_5080935 2608961829252183552145711 := by
  unfold tailWord_5080935
  simp only [CollatzResearch.WordTrace]
  refine ⟨185316923847647724457636259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123544615898431816305090839 185316923847647724457636259)
  ·
    refine ⟨277975385771471586686454389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185316923847647724457636259 277975385771471586686454389)
    ·
      refine ⟨26060192416075461251855099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277975385771471586686454389 26060192416075461251855099)
      ·
        refine ⟨39090288624113191877782649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26060192416075461251855099 39090288624113191877782649)
        ·
          refine ⟨29317716468084893908336987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39090288624113191877782649 29317716468084893908336987)
          ·
            refine ⟨43976574702127340862505481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29317716468084893908336987 43976574702127340862505481)
            ·
              refine ⟨32982431026595505646879111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43976574702127340862505481 32982431026595505646879111)
              ·
                refine ⟨49473646539893258470318667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32982431026595505646879111 49473646539893258470318667)
                ·
                  refine ⟨74210469809839887705478001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49473646539893258470318667 74210469809839887705478001)
                  ·
                    refine ⟨55657852357379915779108501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74210469809839887705478001 55657852357379915779108501)
                    ·
                      refine ⟨2608961829252183552145711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55657852357379915779108501 2608961829252183552145711)
                      ·
                        rfl

theorem cell23_5080935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5080935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080935 prefixEnd_5080935 := by exact prefixLift 5080935
  have htrace : WordTrace (prefixWord ++ tailWord_5080935) baseStart_5080935 baseEnd_5080935 := by
    simpa [prefixWord, tailWord_5080935, baseEnd_5080935] using wordTrace_append hprefix tailTrace_5080935
  have hstable : (prefixWord ++ tailWord_5080935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080935).length < 2 ^ (prefixWord ++ tailWord_5080935).sum := by decide
  have hdescent : baseEnd_5080935 < baseStart_5080935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080945 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_5080945 : Nat := 118140960795 + 5080945 * 2 ^ 59
def prefixEnd_5080945 : Nat := 4983230072969 + 3 ^ 40 * 5080945 * 2
def baseEnd_5080945 : Nat := 869655654686242837673555

theorem tailTrace_5080945 : CollatzResearch.WordTrace tailWord_5080945 prefixEnd_5080945 869655654686242837673555 := by
  unfold tailWord_5080945
  simp only [CollatzResearch.WordTrace]
  refine ⟨185317288577611496165500289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123544859051740997443666859 185317288577611496165500289)
  ·
    refine ⟨138987966433208622124125217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185317288577611496165500289 138987966433208622124125217)
    ·
      refine ⟨104240974824906466593093913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138987966433208622124125217 104240974824906466593093913)
      ·
        refine ⟨78180731118679849944820435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104240974824906466593093913 78180731118679849944820435)
        ·
          refine ⟨117271096678019774917230653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78180731118679849944820435 117271096678019774917230653)
          ·
            refine ⟨43976661254257415593961495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117271096678019774917230653 43976661254257415593961495)
            ·
              refine ⟨65964991881386123390942243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43976661254257415593961495 65964991881386123390942243)
              ·
                refine ⟨98947487822079185086413365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65964991881386123390942243 98947487822079185086413365)
                ·
                  refine ⟨9276326983319923601851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98947487822079185086413365 9276326983319923601851253)
                  ·
                    refine ⟨869655654686242837673555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9276326983319923601851253 869655654686242837673555)
                    ·
                      rfl

theorem cell23_5080945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_5080945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080945 prefixEnd_5080945 := by exact prefixLift 5080945
  have htrace : WordTrace (prefixWord ++ tailWord_5080945) baseStart_5080945 baseEnd_5080945 := by
    simpa [prefixWord, tailWord_5080945, baseEnd_5080945] using wordTrace_append hprefix tailTrace_5080945
  have hstable : (prefixWord ++ tailWord_5080945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080945).length < 2 ^ (prefixWord ++ tailWord_5080945).sum := by decide
  have hdescent : baseEnd_5080945 < baseStart_5080945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5080995 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6]
def baseStart_5080995 : Nat := 118140960795 + 5080995 * 2 ^ 59
def prefixEnd_5080995 : Nat := 4983230072969 + 3 ^ 40 * 5080995 * 2
def baseEnd_5080995 : Nat := 2608992638091453317395435

theorem tailTrace_5080995 : CollatzResearch.WordTrace tailWord_5080995 prefixEnd_5080995 2608992638091453317395435 := by
  unfold tailWord_5080995
  simp only [CollatzResearch.WordTrace]
  refine ⟨185319112227430354704820439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123546074818286903136546959 185319112227430354704820439)
  ·
    refine ⟨277978668341145532057230659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185319112227430354704820439 277978668341145532057230659)
    ·
      refine ⟨416968002511718298085845989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277978668341145532057230659 416968002511718298085845989)
      ·
        refine ⟨78181500470947180891096123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416968002511718298085845989 78181500470947180891096123)
        ·
          refine ⟨117272250706420771336644185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78181500470947180891096123 117272250706420771336644185)
          ·
            refine ⟨87954188029815578502483139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117272250706420771336644185 87954188029815578502483139)
            ·
              refine ⟨131931282044723367753724709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87954188029815578502483139 131931282044723367753724709)
              ·
                refine ⟨24737115383385631453823383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131931282044723367753724709 24737115383385631453823383)
                ·
                  refine ⟨37105673075078447180735075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24737115383385631453823383 37105673075078447180735075)
                  ·
                    refine ⟨55658509612617670771102613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37105673075078447180735075 55658509612617670771102613)
                    ·
                      refine ⟨2608992638091453317395435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55658509612617670771102613 2608992638091453317395435)
                      ·
                        rfl

theorem cell23_5080995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_5080995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5080995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5080995 prefixEnd_5080995 := by exact prefixLift 5080995
  have htrace : WordTrace (prefixWord ++ tailWord_5080995) baseStart_5080995 baseEnd_5080995 := by
    simpa [prefixWord, tailWord_5080995, baseEnd_5080995] using wordTrace_append hprefix tailTrace_5080995
  have hstable : (prefixWord ++ tailWord_5080995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5080995).length < 2 ^ (prefixWord ++ tailWord_5080995).sum := by decide
  have hdescent : baseEnd_5080995 < baseStart_5080995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5080995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081009 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 1, 6]
def baseStart_5081009 : Nat := 118140960795 + 5081009 * 2 ^ 59
def prefixEnd_5081009 : Nat := 4983230072969 + 3 ^ 40 * 5081009 * 2
def baseEnd_5081009 : Nat := 869666608940205420873457

theorem tailTrace_5081009 : CollatzResearch.WordTrace tailWord_5081009 prefixEnd_5081009 869666608940205420873457 := by
  unfold tailWord_5081009
  simp only [CollatzResearch.WordTrace]
  refine ⟨185319622849379635095830081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123546415232919756730553387 185319622849379635095830081)
  ·
    refine ⟨138989717137034726321872561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185319622849379635095830081 138989717137034726321872561)
    ·
      refine ⟨104242287852776044741404421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138989717137034726321872561 104242287852776044741404421)
      ·
        refine ⟨19545428972395508389013329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104242287852776044741404421 19545428972395508389013329)
        ·
          refine ⟨14659071729296631291759997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19545428972395508389013329 14659071729296631291759997)
          ·
            refine ⟨5497151898486236734409999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14659071729296631291759997 5497151898486236734409999)
            ·
              refine ⟨8245727847729355101614999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497151898486236734409999 8245727847729355101614999)
              ·
                refine ⟨12368591771594032652422499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8245727847729355101614999 12368591771594032652422499)
                ·
                  refine ⟨18552887657391048978633749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12368591771594032652422499 18552887657391048978633749)
                  ·
                    refine ⟨869666608940205420873457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18552887657391048978633749 869666608940205420873457)
                    ·
                      rfl

theorem cell23_5081009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_5081009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081009 prefixEnd_5081009 := by exact prefixLift 5081009
  have htrace : WordTrace (prefixWord ++ tailWord_5081009) baseStart_5081009 baseEnd_5081009 := by
    simpa [prefixWord, tailWord_5081009, baseEnd_5081009] using wordTrace_append hprefix tailTrace_5081009
  have hstable : (prefixWord ++ tailWord_5081009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081009).length < 2 ^ (prefixWord ++ tailWord_5081009).sum := by decide
  have hdescent : baseEnd_5081009 < baseStart_5081009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081022 : List Nat := [4, 2, 1, 1, 1, 4, 1, 9]
def baseStart_5081022 : Nat := 118140960795 + 5081022 * 2 ^ 59
def prefixEnd_5081022 : Nat := 4983230072969 + 3 ^ 40 * 5081022 * 2
def baseEnd_5081022 : Nat := 96629870447004618953993

theorem tailTrace_5081022 : CollatzResearch.WordTrace tailWord_5081022 prefixEnd_5081022 96629870447004618953993 := by
  unfold tailWord_5081022
  simp only [CollatzResearch.WordTrace]
  refine ⟨23165012124791567289506665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123546731332221692210702213 23165012124791567289506665)
  ·
    refine ⟨17373759093593675467129999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23165012124791567289506665 17373759093593675467129999)
    ·
      refine ⟨26060638640390513200694999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17373759093593675467129999 26060638640390513200694999)
      ·
        refine ⟨39090957960585769801042499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26060638640390513200694999 39090957960585769801042499)
        ·
          refine ⟨58636436940878654701563749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39090957960585769801042499 58636436940878654701563749)
          ·
            refine ⟨10994331926414747756543203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58636436940878654701563749 10994331926414747756543203)
            ·
              refine ⟨16491497889622121634814805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10994331926414747756543203 16491497889622121634814805)
              ·
                refine ⟨96629870447004618953993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16491497889622121634814805 96629870447004618953993)
                ·
                  rfl

theorem cell23_5081022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_5081022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081022 prefixEnd_5081022 := by exact prefixLift 5081022
  have htrace : WordTrace (prefixWord ++ tailWord_5081022) baseStart_5081022 baseEnd_5081022 := by
    simpa [prefixWord, tailWord_5081022, baseEnd_5081022] using wordTrace_append hprefix tailTrace_5081022
  have hstable : (prefixWord ++ tailWord_5081022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081022).length < 2 ^ (prefixWord ++ tailWord_5081022).sum := by decide
  have hdescent : baseEnd_5081022 < baseStart_5081022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081050 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2]
def baseStart_5081050 : Nat := 118140960795 + 5081050 * 2 ^ 59
def prefixEnd_5081050 : Nat := 4983230072969 + 3 ^ 40 * 5081050 * 2
def baseEnd_5081050 : Nat := 2609020879527450602207683

theorem tailTrace_5081050 : CollatzResearch.WordTrace tailWord_5081050 prefixEnd_5081050 2609020879527450602207683 := by
  unfold tailWord_5081050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46330279560557774774518151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123547412161487399398715069 46330279560557774774518151)
  ·
    refine ⟨69495419340836662161777227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46330279560557774774518151 69495419340836662161777227)
    ·
      refine ⟨104243129011254993242665841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69495419340836662161777227 104243129011254993242665841)
      ·
        refine ⟨78182346758441244931999381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104243129011254993242665841 78182346758441244931999381)
        ·
          refine ⟨3664797504301933356187471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78182346758441244931999381 3664797504301933356187471)
          ·
            refine ⟨5497196256452900034281207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664797504301933356187471 5497196256452900034281207)
            ·
              refine ⟨8245794384679350051421811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497196256452900034281207 8245794384679350051421811)
              ·
                refine ⟨12368691577019025077132717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8245794384679350051421811 12368691577019025077132717)
                ·
                  refine ⟨4638259341382134403924769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12368691577019025077132717 4638259341382134403924769)
                  ·
                    refine ⟨3478694506036600802943577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638259341382134403924769 3478694506036600802943577)
                    ·
                      refine ⟨2609020879527450602207683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478694506036600802943577 2609020879527450602207683)
                      ·
                        rfl

theorem cell23_5081050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_5081050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081050 prefixEnd_5081050 := by exact prefixLift 5081050
  have htrace : WordTrace (prefixWord ++ tailWord_5081050) baseStart_5081050 baseEnd_5081050 := by
    simpa [prefixWord, tailWord_5081050, baseEnd_5081050] using wordTrace_append hprefix tailTrace_5081050
  have hstable : (prefixWord ++ tailWord_5081050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081050).length < 2 ^ (prefixWord ++ tailWord_5081050).sum := by decide
  have hdescent : baseEnd_5081050 < baseStart_5081050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081066 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_5081066 : Nat := 118140960795 + 5081066 * 2 ^ 59
def prefixEnd_5081066 : Nat := 4983230072969 + 3 ^ 40 * 5081066 * 2
def baseEnd_5081066 : Nat := 2609029095217922539607609

theorem tailTrace_5081066 : CollatzResearch.WordTrace tailWord_5081066 prefixEnd_5081066 2609029095217922539607609 := by
  unfold tailWord_5081066
  simp only [CollatzResearch.WordTrace]
  refine ⟨46330425452543283457663763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123547801206782089220436701 46330425452543283457663763)
  ·
    refine ⟨69495638178814925186495645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46330425452543283457663763 69495638178814925186495645)
    ·
      refine ⟨26060864317055596944935867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69495638178814925186495645 26060864317055596944935867)
      ·
        refine ⟨39091296475583395417403801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26060864317055596944935867 39091296475583395417403801)
        ·
          refine ⟨29318472356687546563052851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39091296475583395417403801 29318472356687546563052851)
          ·
            refine ⟨43977708535031319844579277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29318472356687546563052851 43977708535031319844579277)
            ·
              refine ⟨16491640700636744941717229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43977708535031319844579277 16491640700636744941717229)
              ·
                refine ⟨6184365262738779353143961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16491640700636744941717229 6184365262738779353143961)
                ·
                  refine ⟨4638273947054084514857971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6184365262738779353143961 4638273947054084514857971)
                  ·
                    refine ⟨6957410920581126772286957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4638273947054084514857971 6957410920581126772286957)
                    ·
                      refine ⟨2609029095217922539607609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957410920581126772286957 2609029095217922539607609)
                      ·
                        rfl

theorem cell23_5081066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_5081066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081066 prefixEnd_5081066 := by exact prefixLift 5081066
  have htrace : WordTrace (prefixWord ++ tailWord_5081066) baseStart_5081066 baseEnd_5081066 := by
    simpa [prefixWord, tailWord_5081066, baseEnd_5081066] using wordTrace_append hprefix tailTrace_5081066
  have hstable : (prefixWord ++ tailWord_5081066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081066).length < 2 ^ (prefixWord ++ tailWord_5081066).sum := by decide
  have hdescent : baseEnd_5081066 < baseStart_5081066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081093 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 1, 3, 2]
def baseStart_5081093 : Nat := 118140960795 + 5081093 * 2 ^ 59
def prefixEnd_5081093 : Nat := 4983230072969 + 3 ^ 40 * 5081093 * 2
def baseEnd_5081093 : Nat := 2609042959195593933969985

theorem tailTrace_5081093 : CollatzResearch.WordTrace tailWord_5081093 prefixEnd_5081093 2609042959195593933969985 := by
  unfold tailWord_5081093
  simp only [CollatzResearch.WordTrace]
  refine ⟨185322686581075317441887933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123548457720716878294591955 185322686581075317441887933)
  ·
    refine ⟨69496007467903244040707975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185322686581075317441887933 69496007467903244040707975)
    ·
      refine ⟨104244011201854866061061963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69496007467903244040707975 104244011201854866061061963)
      ·
        refine ⟨156366016802782299091592945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104244011201854866061061963 156366016802782299091592945)
        ·
          refine ⟨117274512602086724318694709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156366016802782299091592945 117274512602086724318694709)
          ·
            refine ⟨10994485556445630404877629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117274512602086724318694709 10994485556445630404877629)
            ·
              refine ⟨4122932083667111401829111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10994485556445630404877629 4122932083667111401829111)
              ·
                refine ⟨6184398125500667102743667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122932083667111401829111 6184398125500667102743667)
                ·
                  refine ⟨9276597188251000654115501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6184398125500667102743667 9276597188251000654115501)
                  ·
                    refine ⟨3478723945594125245293313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9276597188251000654115501 3478723945594125245293313)
                    ·
                      refine ⟨2609042959195593933969985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478723945594125245293313 2609042959195593933969985)
                      ·
                        rfl

theorem cell23_5081093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_5081093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081093 prefixEnd_5081093 := by exact prefixLift 5081093
  have htrace : WordTrace (prefixWord ++ tailWord_5081093) baseStart_5081093 baseEnd_5081093 := by
    simpa [prefixWord, tailWord_5081093, baseEnd_5081093] using wordTrace_append hprefix tailTrace_5081093
  have hstable : (prefixWord ++ tailWord_5081093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081093).length < 2 ^ (prefixWord ++ tailWord_5081093).sum := by decide
  have hdescent : baseEnd_5081093 < baseStart_5081093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081112 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 7]
def baseStart_5081112 : Nat := 118140960795 + 5081112 * 2 ^ 59
def prefixEnd_5081112 : Nat := 4983230072969 + 3 ^ 40 * 5081112 * 2
def baseEnd_5081112 : Nat := 289894746147558817736933

theorem tailTrace_5081112 : CollatzResearch.WordTrace tailWord_5081112 prefixEnd_5081112 289894746147558817736933 := by
  unfold tailWord_5081112
  simp only [CollatzResearch.WordTrace]
  refine ⟨92661689784003241843414795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123548919712004322457886393 92661689784003241843414795)
  ·
    refine ⟨138992534676004862765122193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92661689784003241843414795 138992534676004862765122193)
    ·
      refine ⟨104244401007003647073841645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138992534676004862765122193 104244401007003647073841645)
      ·
        refine ⟨39091650377626367652690617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104244401007003647073841645 39091650377626367652690617)
        ·
          refine ⟨29318737783219775739517963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39091650377626367652690617 29318737783219775739517963)
          ·
            refine ⟨43978106674829663609276945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29318737783219775739517963 43978106674829663609276945)
            ·
              refine ⟨32983580006122247706957709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43978106674829663609276945 32983580006122247706957709)
              ·
                refine ⟨12368842502295842890109141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32983580006122247706957709 12368842502295842890109141)
                ·
                  refine ⟨289894746147558817736933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12368842502295842890109141 289894746147558817736933)
                  ·
                    rfl

theorem cell23_5081112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_5081112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081112 prefixEnd_5081112 := by exact prefixLift 5081112
  have htrace : WordTrace (prefixWord ++ tailWord_5081112) baseStart_5081112 baseEnd_5081112 := by
    simpa [prefixWord, tailWord_5081112, baseEnd_5081112] using wordTrace_append hprefix tailTrace_5081112
  have hstable : (prefixWord ++ tailWord_5081112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081112).length < 2 ^ (prefixWord ++ tailWord_5081112).sum := by decide
  have hdescent : baseEnd_5081112 < baseStart_5081112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081174 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5081174 : Nat := 118140960795 + 5081174 * 2 ^ 59
def prefixEnd_5081174 : Nat := 4983230072969 + 3 ^ 40 * 5081174 * 2
def baseEnd_5081174 : Nat := 2609084551128608117057113

theorem tailTrace_5081174 : CollatzResearch.WordTrace tailWord_5081174 prefixEnd_5081174 2609084551128608117057113 := by
  unfold tailWord_5081174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582852555861366767224161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123550427262521245517057717 11582852555861366767224161)
  ·
    refine ⟨8687139416896025075418121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11582852555861366767224161 8687139416896025075418121)
    ·
      refine ⟨6515354562672018806563591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8687139416896025075418121 6515354562672018806563591)
      ·
        refine ⟨9773031844008028209845387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6515354562672018806563591 9773031844008028209845387)
        ·
          refine ⟨14659547766012042314768081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9773031844008028209845387 14659547766012042314768081)
          ·
            refine ⟨10994660824509031736076061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14659547766012042314768081 10994660824509031736076061)
            ·
              refine ⟨4122997809190886901028523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10994660824509031736076061 4122997809190886901028523)
              ·
                refine ⟨6184496713786330351542785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122997809190886901028523 6184496713786330351542785)
                ·
                  refine ⟨4638372535339747763657089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6184496713786330351542785 4638372535339747763657089)
                  ·
                    refine ⟨3478779401504810822742817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638372535339747763657089 3478779401504810822742817)
                    ·
                      refine ⟨2609084551128608117057113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478779401504810822742817 2609084551128608117057113)
                      ·
                        rfl

theorem cell23_5081174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5081174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081174 prefixEnd_5081174 := by exact prefixLift 5081174
  have htrace : WordTrace (prefixWord ++ tailWord_5081174) baseStart_5081174 baseEnd_5081174 := by
    simpa [prefixWord, tailWord_5081174, baseEnd_5081174] using wordTrace_append hprefix tailTrace_5081174
  have hstable : (prefixWord ++ tailWord_5081174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081174).length < 2 ^ (prefixWord ++ tailWord_5081174).sum := by decide
  have hdescent : baseEnd_5081174 < baseStart_5081174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081199 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_5081199 : Nat := 118140960795 + 5081199 * 2 ^ 59
def prefixEnd_5081199 : Nat := 4983230072969 + 3 ^ 40 * 5081199 * 2
def baseEnd_5081199 : Nat := 2609097388144970519244497

theorem tailTrace_5081199 : CollatzResearch.WordTrace tailWord_5081199 prefixEnd_5081199 2609097388144970519244497 := by
  unfold tailWord_5081199
  simp only [CollatzResearch.WordTrace]
  refine ⟨185326552718691297545246651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123551035145794198363497767 185326552718691297545246651)
  ·
    refine ⟨277989829078036946317869977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185326552718691297545246651 277989829078036946317869977)
    ·
      refine ⟨208492371808527709738402483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277989829078036946317869977 208492371808527709738402483)
      ·
        refine ⟨312738557712791564607603725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208492371808527709738402483 312738557712791564607603725)
        ·
          refine ⟨117276959142296836727851397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312738557712791564607603725 117276959142296836727851397)
          ·
            refine ⟨21989429839180656886472137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117276959142296836727851397 21989429839180656886472137)
            ·
              refine ⟨16492072379385492664854103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21989429839180656886472137 16492072379385492664854103)
              ·
                refine ⟨24738108569078238997281155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16492072379385492664854103 24738108569078238997281155)
                ·
                  refine ⟨37107162853617358495921733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24738108569078238997281155 37107162853617358495921733)
                  ·
                    refine ⟨6957593035053254717985325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37107162853617358495921733 6957593035053254717985325)
                    ·
                      refine ⟨2609097388144970519244497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957593035053254717985325 2609097388144970519244497)
                      ·
                        rfl

theorem cell23_5081199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_5081199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081199 prefixEnd_5081199 := by exact prefixLift 5081199
  have htrace : WordTrace (prefixWord ++ tailWord_5081199) baseStart_5081199 baseEnd_5081199 := by
    simpa [prefixWord, tailWord_5081199, baseEnd_5081199] using wordTrace_append hprefix tailTrace_5081199
  have hstable : (prefixWord ++ tailWord_5081199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081199).length < 2 ^ (prefixWord ++ tailWord_5081199).sum := by decide
  have hdescent : baseEnd_5081199 < baseStart_5081199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081263 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 1, 1, 3]
def baseStart_5081263 : Nat := 118140960795 + 5081263 * 2 ^ 59
def prefixEnd_5081263 : Nat := 4983230072969 + 3 ^ 40 * 5081263 * 2
def baseEnd_5081263 : Nat := 2609130250906858268844203

theorem tailTrace_5081263 : CollatzResearch.WordTrace tailWord_5081263 prefixEnd_5081263 2609130250906858268844203 := by
  unfold tailWord_5081263
  simp only [CollatzResearch.WordTrace]
  refine ⟨185328886990459436475576443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123552591326972957650384295 185328886990459436475576443)
  ·
    refine ⟨277993330485689154713364665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185328886990459436475576443 277993330485689154713364665)
    ·
      refine ⟨208494997864266866035023499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277993330485689154713364665 208494997864266866035023499)
      ·
        refine ⟨312742496796400299052535249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208494997864266866035023499 312742496796400299052535249)
        ·
          refine ⟨234556872597300224289401437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312742496796400299052535249 234556872597300224289401437)
          ·
            refine ⟨87958827223987584108525539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234556872597300224289401437 87958827223987584108525539)
            ·
              refine ⟨131938240835981376162788309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87958827223987584108525539 131938240835981376162788309)
              ·
                refine ⟨3092302519593313503815351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131938240835981376162788309 3092302519593313503815351)
                ·
                  refine ⟨4638453779389970255723027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092302519593313503815351 4638453779389970255723027)
                  ·
                    refine ⟨6957680669084955383584541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4638453779389970255723027 6957680669084955383584541)
                    ·
                      refine ⟨2609130250906858268844203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957680669084955383584541 2609130250906858268844203)
                      ·
                        rfl

theorem cell23_5081263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 1, 3].length) (baseStart_5081263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081263 prefixEnd_5081263 := by exact prefixLift 5081263
  have htrace : WordTrace (prefixWord ++ tailWord_5081263) baseStart_5081263 baseEnd_5081263 := by
    simpa [prefixWord, tailWord_5081263, baseEnd_5081263] using wordTrace_append hprefix tailTrace_5081263
  have hstable : (prefixWord ++ tailWord_5081263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081263).length < 2 ^ (prefixWord ++ tailWord_5081263).sum := by decide
  have hdescent : baseEnd_5081263 < baseStart_5081263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081280 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 1, 1, 3]
def baseStart_5081280 : Nat := 118140960795 + 5081280 * 2 ^ 59
def prefixEnd_5081280 : Nat := 4983230072969 + 3 ^ 40 * 5081280 * 2
def baseEnd_5081280 : Nat := 2609138980077984702331625

theorem tailTrace_5081280 : CollatzResearch.WordTrace tailWord_5081280 prefixEnd_5081280 2609138980077984702331625 := by
  unfold tailWord_5081280
  simp only [CollatzResearch.WordTrace]
  refine ⟨92664753515698924189472647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123553004687598565585963529 92664753515698924189472647)
  ·
    refine ⟨138997130273548386284208971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92664753515698924189472647 138997130273548386284208971)
    ·
      refine ⟨208495695410322579426313457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138997130273548386284208971 208495695410322579426313457)
      ·
        refine ⟨156371771557741934569735093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208495695410322579426313457 156371771557741934569735093)
        ·
          refine ⟨14659853583538306365912665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156371771557741934569735093 14659853583538306365912665)
          ·
            refine ⟨10994890187653729774434499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14659853583538306365912665 10994890187653729774434499)
            ·
              refine ⟨16492335281480594661651749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10994890187653729774434499 16492335281480594661651749)
              ·
                refine ⟨3092312865277611499059703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16492335281480594661651749 3092312865277611499059703)
                ·
                  refine ⟨4638469297916417248589555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092312865277611499059703 4638469297916417248589555)
                  ·
                    refine ⟨6957703946874625872884333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4638469297916417248589555 6957703946874625872884333)
                    ·
                      refine ⟨2609138980077984702331625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957703946874625872884333 2609138980077984702331625)
                      ·
                        rfl

theorem cell23_5081280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_5081280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081280 prefixEnd_5081280 := by exact prefixLift 5081280
  have htrace : WordTrace (prefixWord ++ tailWord_5081280) baseStart_5081280 baseEnd_5081280 := by
    simpa [prefixWord, tailWord_5081280, baseEnd_5081280] using wordTrace_append hprefix tailTrace_5081280
  have hstable : (prefixWord ++ tailWord_5081280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081280).length < 2 ^ (prefixWord ++ tailWord_5081280).sum := by decide
  have hdescent : baseEnd_5081280 < baseStart_5081280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081306 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_5081306 : Nat := 118140960795 + 5081306 * 2 ^ 59
def prefixEnd_5081306 : Nat := 4983230072969 + 3 ^ 40 * 5081306 * 2
def baseEnd_5081306 : Nat := 2609152330575001600606505

theorem tailTrace_5081306 : CollatzResearch.WordTrace tailWord_5081306 prefixEnd_5081306 2609152330575001600606505 := by
  unfold tailWord_5081306
  simp only [CollatzResearch.WordTrace]
  refine ⟨46332613832325913704847943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123553636886202436546261181 46332613832325913704847943)
  ·
    refine ⟨69498920748488870557271915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46332613832325913704847943 69498920748488870557271915)
    ·
      refine ⟨104248381122733305835907873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69498920748488870557271915 104248381122733305835907873)
      ·
        refine ⟨78186285842049979376930905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104248381122733305835907873 78186285842049979376930905)
        ·
          refine ⟨58639714381537484532698179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78186285842049979376930905 58639714381537484532698179)
          ·
            refine ⟨87959571572306226799047269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58639714381537484532698179 87959571572306226799047269)
            ·
              refine ⟨16492419669807417524821363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87959571572306226799047269 16492419669807417524821363)
              ·
                refine ⟨24738629504711126287232045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16492419669807417524821363 24738629504711126287232045)
                ·
                  refine ⟨9276986064266672357712017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24738629504711126287232045 9276986064266672357712017)
                  ·
                    refine ⟨6957739548200004268284013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9276986064266672357712017 6957739548200004268284013)
                    ·
                      refine ⟨2609152330575001600606505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957739548200004268284013 2609152330575001600606505)
                      ·
                        rfl

theorem cell23_5081306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_5081306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081306 prefixEnd_5081306 := by exact prefixLift 5081306
  have htrace : WordTrace (prefixWord ++ tailWord_5081306) baseStart_5081306 baseEnd_5081306 := by
    simpa [prefixWord, tailWord_5081306, baseEnd_5081306] using wordTrace_append hprefix tailTrace_5081306
  have hstable : (prefixWord ++ tailWord_5081306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081306).length < 2 ^ (prefixWord ++ tailWord_5081306).sum := by decide
  have hdescent : baseEnd_5081306 < baseStart_5081306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081320 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_5081320 : Nat := 118140960795 + 5081320 * 2 ^ 59
def prefixEnd_5081320 : Nat := 4983230072969 + 3 ^ 40 * 5081320 * 2
def baseEnd_5081320 : Nat := 2609159519304164545831441

theorem tailTrace_5081320 : CollatzResearch.WordTrace tailWord_5081320 prefixEnd_5081320 2609159519304164545831441 := by
  unfold tailWord_5081320
  simp only [CollatzResearch.WordTrace]
  refine ⟨92665482975626467605200707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123553977300835290140267609 92665482975626467605200707)
  ·
    refine ⟨138998224463439701407801061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92665482975626467605200707 138998224463439701407801061)
    ·
      refine ⟨26062167086894944013962699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138998224463439701407801061 26062167086894944013962699)
      ·
        refine ⟨39093250630342416020944049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26062167086894944013962699 39093250630342416020944049)
        ·
          refine ⟨29319937972756812015708037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39093250630342416020944049 29319937972756812015708037)
          ·
            refine ⟨5497488369891902252945257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29319937972756812015708037 5497488369891902252945257)
            ·
              refine ⟨4123116277418926689708943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497488369891902252945257 4123116277418926689708943)
              ·
                refine ⟨6184674416128390034563415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123116277418926689708943 6184674416128390034563415)
                ·
                  refine ⟨9277011624192585051845123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6184674416128390034563415 9277011624192585051845123)
                  ·
                    refine ⟨13915517436288877577767685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9277011624192585051845123 13915517436288877577767685)
                    ·
                      refine ⟨2609159519304164545831441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13915517436288877577767685 2609159519304164545831441)
                      ·
                        rfl

theorem cell23_5081320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_5081320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081320 prefixEnd_5081320 := by exact prefixLift 5081320
  have htrace : WordTrace (prefixWord ++ tailWord_5081320) baseStart_5081320 baseEnd_5081320 := by
    simpa [prefixWord, tailWord_5081320, baseEnd_5081320] using wordTrace_append hprefix tailTrace_5081320
  have hstable : (prefixWord ++ tailWord_5081320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081320).length < 2 ^ (prefixWord ++ tailWord_5081320).sum := by decide
  have hdescent : baseEnd_5081320 < baseStart_5081320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081330 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_5081330 : Nat := 118140960795 + 5081330 * 2 ^ 59
def prefixEnd_5081330 : Nat := 4983230072969 + 3 ^ 40 * 5081330 * 2
def baseEnd_5081330 : Nat := 869721551370236502235465

theorem tailTrace_5081330 : CollatzResearch.WordTrace tailWord_5081330 prefixEnd_5081330 869721551370236502235465 := by
  unfold tailWord_5081330
  simp only [CollatzResearch.WordTrace]
  refine ⟨46332832670304176729566361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123554220454144471278843629 46332832670304176729566361)
  ·
    refine ⟨34749624502728132547174771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46332832670304176729566361 34749624502728132547174771)
    ·
      refine ⟨52124436754092198820762157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34749624502728132547174771 52124436754092198820762157)
      ·
        refine ⟨19546663782784574557785809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52124436754092198820762157 19546663782784574557785809)
        ·
          refine ⟨14659997837088430918339357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19546663782784574557785809 14659997837088430918339357)
          ·
            refine ⟨5497499188908161594377259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14659997837088430918339357 5497499188908161594377259)
            ·
              refine ⟨8246248783362242391565889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497499188908161594377259 8246248783362242391565889)
              ·
                refine ⟨6184686587521681793674417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246248783362242391565889 6184686587521681793674417)
                ·
                  refine ⟨4638514940641261345255813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6184686587521681793674417 4638514940641261345255813)
                  ·
                    refine ⟨869721551370236502235465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4638514940641261345255813 869721551370236502235465)
                    ·
                      rfl

theorem cell23_5081330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_5081330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081330 prefixEnd_5081330 := by exact prefixLift 5081330
  have htrace : WordTrace (prefixWord ++ tailWord_5081330) baseStart_5081330 baseEnd_5081330 := by
    simpa [prefixWord, tailWord_5081330, baseEnd_5081330] using wordTrace_append hprefix tailTrace_5081330
  have hstable : (prefixWord ++ tailWord_5081330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081330).length < 2 ^ (prefixWord ++ tailWord_5081330).sum := by decide
  have hdescent : baseEnd_5081330 < baseStart_5081330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081353 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 3]
def baseStart_5081353 : Nat := 118140960795 + 5081353 * 2 ^ 59
def prefixEnd_5081353 : Nat := 4983230072969 + 3 ^ 40 * 5081353 * 2
def baseEnd_5081353 : Nat := 2609176464165762916718789

theorem tailTrace_5081353 : CollatzResearch.WordTrace tailWord_5081353 prefixEnd_5081353 2609176464165762916718789 := by
  unfold tailWord_5081353
  simp only [CollatzResearch.WordTrace]
  refine ⟨185332169560133381846352713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123554779706755587897568475 185332169560133381846352713)
  ·
    refine ⟨138999127170100036384764535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185332169560133381846352713 138999127170100036384764535)
    ·
      refine ⟨208498690755150054577146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138999127170100036384764535 208498690755150054577146803)
      ·
        refine ⟨312748036132725081865720205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208498690755150054577146803 312748036132725081865720205)
        ·
          refine ⟨117280513549771905699645077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312748036132725081865720205 117280513549771905699645077)
          ·
            refine ⟨5497524072645558079670863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117280513549771905699645077 5497524072645558079670863)
            ·
              refine ⟨8246286108968337119506295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497524072645558079670863 8246286108968337119506295)
              ·
                refine ⟨12369429163452505679259443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8246286108968337119506295 12369429163452505679259443)
                ·
                  refine ⟨18554143745178758518889165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12369429163452505679259443 18554143745178758518889165)
                  ·
                    refine ⟨6957803904442034444583437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18554143745178758518889165 6957803904442034444583437)
                    ·
                      refine ⟨2609176464165762916718789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957803904442034444583437 2609176464165762916718789)
                      ·
                        rfl

theorem cell23_5081353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_5081353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081353 prefixEnd_5081353 := by exact prefixLift 5081353
  have htrace : WordTrace (prefixWord ++ tailWord_5081353) baseStart_5081353 baseEnd_5081353 := by
    simpa [prefixWord, tailWord_5081353, baseEnd_5081353] using wordTrace_append hprefix tailTrace_5081353
  have hstable : (prefixWord ++ tailWord_5081353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081353).length < 2 ^ (prefixWord ++ tailWord_5081353).sum := by decide
  have hdescent : baseEnd_5081353 < baseStart_5081353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081359 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_5081359 : Nat := 118140960795 + 5081359 * 2 ^ 59
def prefixEnd_5081359 : Nat := 4983230072969 + 3 ^ 40 * 5081359 * 2
def baseEnd_5081359 : Nat := 2609179545049689893243761

theorem tailTrace_5081359 : CollatzResearch.WordTrace tailWord_5081359 prefixEnd_5081359 2609179545049689893243761 := by
  unfold tailWord_5081359
  simp only [CollatzResearch.WordTrace]
  refine ⟨185332388398111644871071131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123554925598741096580714087 185332388398111644871071131)
  ·
    refine ⟨277998582597167467306606697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185332388398111644871071131 277998582597167467306606697)
    ·
      refine ⟨208498936947875600479955023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277998582597167467306606697 208498936947875600479955023)
      ·
        refine ⟨312748405421813400719932535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208498936947875600479955023 312748405421813400719932535)
        ·
          refine ⟨469122608132720101079898803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312748405421813400719932535 469122608132720101079898803)
          ·
            refine ⟨703683912199080151619848205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469122608132720101079898803 703683912199080151619848205)
            ·
              refine ⟨263881467074655056857443077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703683912199080151619848205 263881467074655056857443077)
              ·
                refine ⟨49477775076497823160770577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263881467074655056857443077 49477775076497823160770577)
                ·
                  refine ⟨37108331307373367370577933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49477775076497823160770577 37108331307373367370577933)
                  ·
                    refine ⟨13915624240265012763966725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37108331307373367370577933 13915624240265012763966725)
                    ·
                      refine ⟨2609179545049689893243761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13915624240265012763966725 2609179545049689893243761)
                      ·
                        rfl

theorem cell23_5081359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_5081359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081359 prefixEnd_5081359 := by exact prefixLift 5081359
  have htrace : WordTrace (prefixWord ++ tailWord_5081359) baseStart_5081359 baseEnd_5081359 := by
    simpa [prefixWord, tailWord_5081359, baseEnd_5081359] using wordTrace_append hprefix tailTrace_5081359
  have hstable : (prefixWord ++ tailWord_5081359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081359).length < 2 ^ (prefixWord ++ tailWord_5081359).sum := by decide
  have hdescent : baseEnd_5081359 < baseStart_5081359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081380 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_5081380 : Nat := 118140960795 + 5081380 * 2 ^ 59
def prefixEnd_5081380 : Nat := 4983230072969 + 3 ^ 40 * 5081380 * 2
def baseEnd_5081380 : Nat := 2609190328143434311081165

theorem tailTrace_5081380 : CollatzResearch.WordTrace tailWord_5081380 prefixEnd_5081380 2609190328143434311081165 := by
  unfold tailWord_5081380
  simp only [CollatzResearch.WordTrace]
  refine ⟨92666577165517782728792797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123555436220690376971723729 92666577165517782728792797)
  ·
    refine ⟨34749966437069168523297299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92666577165517782728792797 34749966437069168523297299)
    ·
      refine ⟨52124949655603752784945949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34749966437069168523297299 52124949655603752784945949)
      ·
        refine ⟨19546856120851407294354731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52124949655603752784945949 19546856120851407294354731)
        ·
          refine ⟨29320284181277110941532097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19546856120851407294354731 29320284181277110941532097)
          ·
            refine ⟨21990213135957833206149073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29320284181277110941532097 21990213135957833206149073)
            ·
              refine ⟨16492659851968374904611805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21990213135957833206149073 16492659851968374904611805)
              ·
                refine ⟨6184747444488140589229427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16492659851968374904611805 6184747444488140589229427)
                ·
                  refine ⟨9277121166732210883844141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6184747444488140589229427 9277121166732210883844141)
                  ·
                    refine ⟨3478920437524579081441553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9277121166732210883844141 3478920437524579081441553)
                    ·
                      refine ⟨2609190328143434311081165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478920437524579081441553 2609190328143434311081165)
                      ·
                        rfl

theorem cell23_5081380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_5081380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081380 prefixEnd_5081380 := by exact prefixLift 5081380
  have htrace : WordTrace (prefixWord ++ tailWord_5081380) baseStart_5081380 baseEnd_5081380 := by
    simpa [prefixWord, tailWord_5081380, baseEnd_5081380] using wordTrace_append hprefix tailTrace_5081380
  have hstable : (prefixWord ++ tailWord_5081380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081380).length < 2 ^ (prefixWord ++ tailWord_5081380).sum := by decide
  have hdescent : baseEnd_5081380 < baseStart_5081380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081438 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5081438 : Nat := 118140960795 + 5081438 * 2 ^ 59
def prefixEnd_5081438 : Nat := 4983230072969 + 3 ^ 40 * 5081438 * 2
def baseEnd_5081438 : Nat := 2609220110021395084155899

theorem tailTrace_5081438 : CollatzResearch.WordTrace tailWord_5081438 prefixEnd_5081438 2609220110021395084155899 := by
  unfold tailWord_5081438
  simp only [CollatzResearch.WordTrace]
  refine ⟨23166908720603180170399621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123556846509883627575464645 23166908720603180170399621)
  ·
    refine ⟨4343795385113096281949929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23166908720603180170399621 4343795385113096281949929)
    ·
      refine ⟨3257846538834822211462447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4343795385113096281949929 3257846538834822211462447)
      ·
        refine ⟨4886769808252233317193671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257846538834822211462447 4886769808252233317193671)
        ·
          refine ⟨7330154712378349975790507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886769808252233317193671 7330154712378349975790507)
          ·
            refine ⟨10995232068567524963685761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7330154712378349975790507 10995232068567524963685761)
            ·
              refine ⟨8246424051425643722764321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10995232068567524963685761 8246424051425643722764321)
              ·
                refine ⟨6184818038569232792073241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246424051425643722764321 6184818038569232792073241)
                ·
                  refine ⟨4638613528926924594054931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6184818038569232792073241 4638613528926924594054931)
                  ·
                    refine ⟨6957920293390386891082397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4638613528926924594054931 6957920293390386891082397)
                    ·
                      refine ⟨2609220110021395084155899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6957920293390386891082397 2609220110021395084155899)
                      ·
                        rfl

theorem cell23_5081438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5081438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081438 prefixEnd_5081438 := by exact prefixLift 5081438
  have htrace : WordTrace (prefixWord ++ tailWord_5081438) baseStart_5081438 baseEnd_5081438 := by
    simpa [prefixWord, tailWord_5081438, baseEnd_5081438] using wordTrace_append hprefix tailTrace_5081438
  have hstable : (prefixWord ++ tailWord_5081438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081438).length < 2 ^ (prefixWord ++ tailWord_5081438).sum := by decide
  have hdescent : baseEnd_5081438 < baseStart_5081438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081450 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_5081450 : Nat := 118140960795 + 5081450 * 2 ^ 59
def prefixEnd_5081450 : Nat := 4983230072969 + 3 ^ 40 * 5081450 * 2
def baseEnd_5081450 : Nat := 289914030198805448578427

theorem tailTrace_5081450 : CollatzResearch.WordTrace tailWord_5081450 prefixEnd_5081450 289914030198805448578427 := by
  unfold tailWord_5081450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46333926860195491853158451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123557138293854644941755869 46333926860195491853158451)
  ·
    refine ⟨69500890290293237779737677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46333926860195491853158451 69500890290293237779737677)
    ·
      refine ⟨26062833858859964167401629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69500890290293237779737677 26062833858859964167401629)
      ·
        refine ⟨9773562697072486562775611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26062833858859964167401629 9773562697072486562775611)
        ·
          refine ⟨14660344045608729844163417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9773562697072486562775611 14660344045608729844163417)
          ·
            refine ⟨10995258034206547383122563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14660344045608729844163417 10995258034206547383122563)
            ·
              refine ⟨16492887051309821074683845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10995258034206547383122563 16492887051309821074683845)
              ·
                refine ⟨3092416322120591451503221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16492887051309821074683845 3092416322120591451503221)
                ·
                  refine ⟨289914030198805448578427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3092416322120591451503221 289914030198805448578427)
                  ·
                    rfl

theorem cell23_5081450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_5081450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081450 prefixEnd_5081450 := by exact prefixLift 5081450
  have htrace : WordTrace (prefixWord ++ tailWord_5081450) baseStart_5081450 baseEnd_5081450 := by
    simpa [prefixWord, tailWord_5081450, baseEnd_5081450] using wordTrace_append hprefix tailTrace_5081450
  have hstable : (prefixWord ++ tailWord_5081450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081450).length < 2 ^ (prefixWord ++ tailWord_5081450).sum := by decide
  have hdescent : baseEnd_5081450 < baseStart_5081450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081453 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5081453 : Nat := 118140960795 + 5081453 * 2 ^ 59
def prefixEnd_5081453 : Nat := 4983230072969 + 3 ^ 40 * 5081453 * 2
def baseEnd_5081453 : Nat := 2609227812231212525468329

theorem tailTrace_5081453 : CollatzResearch.WordTrace tailWord_5081453 prefixEnd_5081453 2609227812231212525468329 := by
  unfold tailWord_5081453
  simp only [CollatzResearch.WordTrace]
  refine ⟨185335816859771098924993013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123557211239847399283328675 185335816859771098924993013)
  ·
    refine ⟨17375232830603540524218095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185335816859771098924993013 17375232830603540524218095)
    ·
      refine ⟨26062849245905310786327143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17375232830603540524218095 26062849245905310786327143)
      ·
        refine ⟨39094273868857966179490715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26062849245905310786327143 39094273868857966179490715)
        ·
          refine ⟨58641410803286949269236073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39094273868857966179490715 58641410803286949269236073)
          ·
            refine ⟨43981058102465211951927055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58641410803286949269236073 43981058102465211951927055)
            ·
              refine ⟨65971587153697817927890583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43981058102465211951927055 65971587153697817927890583)
              ·
                refine ⟨98957380730546726891835875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65971587153697817927890583 98957380730546726891835875)
                ·
                  refine ⟨148436071095820090337753813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98957380730546726891835875 148436071095820090337753813)
                  ·
                    refine ⟨3478970416308283367291105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148436071095820090337753813 3478970416308283367291105)
                    ·
                      refine ⟨2609227812231212525468329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3478970416308283367291105 2609227812231212525468329)
                      ·
                        rfl

theorem cell23_5081453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5081453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081453 prefixEnd_5081453 := by exact prefixLift 5081453
  have htrace : WordTrace (prefixWord ++ tailWord_5081453) baseStart_5081453 baseEnd_5081453 := by
    simpa [prefixWord, tailWord_5081453, baseEnd_5081453] using wordTrace_append hprefix tailTrace_5081453
  have hstable : (prefixWord ++ tailWord_5081453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081453).length < 2 ^ (prefixWord ++ tailWord_5081453).sum := by decide
  have hdescent : baseEnd_5081453 < baseStart_5081453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081456 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_5081456 : Nat := 118140960795 + 5081456 * 2 ^ 59
def prefixEnd_5081456 : Nat := 4983230072969 + 3 ^ 40 * 5081456 * 2
def baseEnd_5081456 : Nat := 2609229352673176013730815

theorem tailTrace_5081456 : CollatzResearch.WordTrace tailWord_5081456 prefixEnd_5081456 2609229352673176013730815 := by
  unfold tailWord_5081456
  simp only [CollatzResearch.WordTrace]
  refine ⟨92667963139380115218676111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123557284185840153624901481 92667963139380115218676111)
  ·
    refine ⟨139001944709070172828014167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92667963139380115218676111 139001944709070172828014167)
    ·
      refine ⟨208502917063605259242021251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139001944709070172828014167 208502917063605259242021251)
      ·
        refine ⟨312754375595407888863031877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208502917063605259242021251 312754375595407888863031877)
        ·
          refine ⟨58641445424138979161818477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312754375595407888863031877 58641445424138979161818477)
          ·
            refine ⟨21990542034052117185681929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58641445424138979161818477 21990542034052117185681929)
            ·
              refine ⟨16492906525539087889261447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21990542034052117185681929 16492906525539087889261447)
              ·
                refine ⟨24739359788308631833892171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16492906525539087889261447 24739359788308631833892171)
                ·
                  refine ⟨37109039682462947750838257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24739359788308631833892171 37109039682462947750838257)
                  ·
                    refine ⟨27831779761847210813128693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37109039682462947750838257 27831779761847210813128693)
                    ·
                      refine ⟨2609229352673176013730815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27831779761847210813128693 2609229352673176013730815)
                      ·
                        rfl

theorem cell23_5081456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_5081456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081456 prefixEnd_5081456 := by exact prefixLift 5081456
  have htrace : WordTrace (prefixWord ++ tailWord_5081456) baseStart_5081456 baseEnd_5081456 := by
    simpa [prefixWord, tailWord_5081456, baseEnd_5081456] using wordTrace_append hprefix tailTrace_5081456
  have hstable : (prefixWord ++ tailWord_5081456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081456).length < 2 ^ (prefixWord ++ tailWord_5081456).sum := by decide
  have hdescent : baseEnd_5081456 < baseStart_5081456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081483 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 4]
def baseStart_5081483 : Nat := 118140960795 + 5081483 * 2 ^ 59
def prefixEnd_5081483 : Nat := 4983230072969 + 3 ^ 40 * 5081483 * 2
def baseEnd_5081483 : Nat := 2609243216650847408093191

theorem tailTrace_5081483 : CollatzResearch.WordTrace tailWord_5081483 prefixEnd_5081483 2609243216650847408093191 := by
  unfold tailWord_5081483
  simp only [CollatzResearch.WordTrace]
  refine ⟨185336911049662414048585103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123557940699774942699056735 185336911049662414048585103)
  ·
    refine ⟨278005366574493621072877655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185336911049662414048585103 278005366574493621072877655)
    ·
      refine ⟨417008049861740431609316483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278005366574493621072877655 417008049861740431609316483)
      ·
        refine ⟨625512074792610647413974725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417008049861740431609316483 625512074792610647413974725)
        ·
          refine ⟨117283514023614496390120261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 625512074792610647413974725 117283514023614496390120261)
          ·
            refine ⟨21990658879427718073147549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117283514023614496390120261 21990658879427718073147549)
            ·
              refine ⟨8246497079785394277430331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21990658879427718073147549 8246497079785394277430331)
              ·
                refine ⟨12369745619678091416145497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8246497079785394277430331 12369745619678091416145497)
                ·
                  refine ⟨9277309214758568562109123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12369745619678091416145497 9277309214758568562109123)
                  ·
                    refine ⟨13915963822137852843163685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9277309214758568562109123 13915963822137852843163685)
                    ·
                      refine ⟨2609243216650847408093191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13915963822137852843163685 2609243216650847408093191)
                      ·
                        rfl

theorem cell23_5081483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 4].length) (baseStart_5081483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081483 prefixEnd_5081483 := by exact prefixLift 5081483
  have htrace : WordTrace (prefixWord ++ tailWord_5081483) baseStart_5081483 baseEnd_5081483 := by
    simpa [prefixWord, tailWord_5081483, baseEnd_5081483] using wordTrace_append hprefix tailTrace_5081483
  have hstable : (prefixWord ++ tailWord_5081483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081483).length < 2 ^ (prefixWord ++ tailWord_5081483).sum := by decide
  have hdescent : baseEnd_5081483 < baseStart_5081483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081503 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_5081503 : Nat := 118140960795 + 5081503 * 2 ^ 59
def prefixEnd_5081503 : Nat := 4983230072969 + 3 ^ 40 * 5081503 * 2
def baseEnd_5081503 : Nat := 2609253486263937329843099

theorem tailTrace_5081503 : CollatzResearch.WordTrace tailWord_5081503 prefixEnd_5081503 2609253486263937329843099 := by
  unfold tailWord_5081503
  simp only [CollatzResearch.WordTrace]
  refine ⟨185337640509589957464313163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123558427006393304976208775 185337640509589957464313163)
  ·
    refine ⟨278006460764384936196469745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185337640509589957464313163 278006460764384936196469745)
    ·
      refine ⟨208504845573288702147352309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278006460764384936196469745 208504845573288702147352309)
      ·
        refine ⟨19547329272495815826314279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208504845573288702147352309 19547329272495815826314279)
        ·
          refine ⟨29320993908743723739471419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19547329272495815826314279 29320993908743723739471419)
          ·
            refine ⟨43981490863115585609207129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29320993908743723739471419 43981490863115585609207129)
            ·
              refine ⟨32986118147336689206905347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43981490863115585609207129 32986118147336689206905347)
              ·
                refine ⟨49479177221005033810358021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32986118147336689206905347 49479177221005033810358021)
                ·
                  refine ⟨9277345728938443839442129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49479177221005033810358021 9277345728938443839442129)
                  ·
                    refine ⟨6958009296703832879581597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9277345728938443839442129 6958009296703832879581597)
                    ·
                      refine ⟨2609253486263937329843099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958009296703832879581597 2609253486263937329843099)
                      ·
                        rfl

theorem cell23_5081503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_5081503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081503 prefixEnd_5081503 := by exact prefixLift 5081503
  have htrace : WordTrace (prefixWord ++ tailWord_5081503) baseStart_5081503 baseEnd_5081503 := by
    simpa [prefixWord, tailWord_5081503, baseEnd_5081503] using wordTrace_append hprefix tailTrace_5081503
  have hstable : (prefixWord ++ tailWord_5081503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081503).length < 2 ^ (prefixWord ++ tailWord_5081503).sum := by decide
  have hdescent : baseEnd_5081503 < baseStart_5081503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081567 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 3]
def baseStart_5081567 : Nat := 118140960795 + 5081567 * 2 ^ 59
def prefixEnd_5081567 : Nat := 4983230072969 + 3 ^ 40 * 5081567 * 2
def baseEnd_5081567 : Nat := 2609286349025825079442805

theorem tailTrace_5081567 : CollatzResearch.WordTrace tailWord_5081567 prefixEnd_5081567 2609286349025825079442805 := by
  unfold tailWord_5081567
  simp only [CollatzResearch.WordTrace]
  refine ⟨185339974781358096394642955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123559983187572064263095303 185339974781358096394642955)
  ·
    refine ⟨278009962172037144591964433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185339974781358096394642955 278009962172037144591964433)
    ·
      refine ⟨208507471629027858443973325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278009962172037144591964433 208507471629027858443973325)
      ·
        refine ⟨78190301860885446916489997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208507471629027858443973325 78190301860885446916489997)
        ·
          refine ⟨29321363197832042593683749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78190301860885446916489997 29321363197832042593683749)
          ·
            refine ⟨5497755599593507986315703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29321363197832042593683749 5497755599593507986315703)
            ·
              refine ⟨8246633399390261979473555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497755599593507986315703 8246633399390261979473555)
              ·
                refine ⟨12369950099085392969210333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8246633399390261979473555 12369950099085392969210333)
                ·
                  refine ⟨4638731287157022363453875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12369950099085392969210333 4638731287157022363453875)
                  ·
                    refine ⟨6958096930735533545180813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4638731287157022363453875 6958096930735533545180813)
                    ·
                      refine ⟨2609286349025825079442805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958096930735533545180813 2609286349025825079442805)
                      ·
                        rfl

theorem cell23_5081567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_5081567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081567 prefixEnd_5081567 := by exact prefixLift 5081567
  have htrace : WordTrace (prefixWord ++ tailWord_5081567) baseStart_5081567 baseEnd_5081567 := by
    simpa [prefixWord, tailWord_5081567, baseEnd_5081567] using wordTrace_append hprefix tailTrace_5081567
  have hstable : (prefixWord ++ tailWord_5081567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081567).length < 2 ^ (prefixWord ++ tailWord_5081567).sum := by decide
  have hdescent : baseEnd_5081567 < baseStart_5081567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081590 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_5081590 : Nat := 118140960795 + 5081590 * 2 ^ 59
def prefixEnd_5081590 : Nat := 4983230072969 + 3 ^ 40 * 5081590 * 2
def baseEnd_5081590 : Nat := 2609298159080878489455199

theorem tailTrace_5081590 : CollatzResearch.WordTrace tailWord_5081590 prefixEnd_5081590 2609298159080878489455199 := by
  unfold tailWord_5081590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11583800853767173207670639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123560542440183180881820149 11583800853767173207670639)
  ·
    refine ⟨17375701280650759811505959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11583800853767173207670639 17375701280650759811505959)
    ·
      refine ⟨26063551920976139717258939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17375701280650759811505959 26063551920976139717258939)
      ·
        refine ⟨39095327881464209575888409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26063551920976139717258939 39095327881464209575888409)
        ·
          refine ⟨29321495911098157181916307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39095327881464209575888409 29321495911098157181916307)
          ·
            refine ⟨43982243866647235772874461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29321495911098157181916307 43982243866647235772874461)
            ·
              refine ⟨16493341449992713414827923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43982243866647235772874461 16493341449992713414827923)
              ·
                refine ⟨24740012174989070122241885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16493341449992713414827923 24740012174989070122241885)
                ·
                  refine ⟨9277504565620901295840707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24740012174989070122241885 9277504565620901295840707)
                  ·
                    refine ⟨13916256848431351943761061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9277504565620901295840707 13916256848431351943761061)
                    ·
                      refine ⟨2609298159080878489455199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13916256848431351943761061 2609298159080878489455199)
                      ·
                        rfl

theorem cell23_5081590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_5081590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081590 prefixEnd_5081590 := by exact prefixLift 5081590
  have htrace : WordTrace (prefixWord ++ tailWord_5081590) baseStart_5081590 baseEnd_5081590 := by
    simpa [prefixWord, tailWord_5081590, baseEnd_5081590] using wordTrace_append hprefix tailTrace_5081590
  have hstable : (prefixWord ++ tailWord_5081590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081590).length < 2 ^ (prefixWord ++ tailWord_5081590).sum := by decide
  have hdescent : baseEnd_5081590 < baseStart_5081590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081603 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4]
def baseStart_5081603 : Nat := 118140960795 + 5081603 * 2 ^ 59
def prefixEnd_5081603 : Nat := 4983230072969 + 3 ^ 40 * 5081603 * 2
def baseEnd_5081603 : Nat := 2609304834329386938592639

theorem tailTrace_5081603 : CollatzResearch.WordTrace tailWord_5081603 prefixEnd_5081603 2609304834329386938592639 := by
  unfold tailWord_5081603
  simp only [CollatzResearch.WordTrace]
  refine ⟨185341287809227674542953463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123560858539485116361968975 185341287809227674542953463)
  ·
    refine ⟨278011931713841511814430195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185341287809227674542953463 278011931713841511814430195)
    ·
      refine ⟨417017897570762267721645293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278011931713841511814430195 417017897570762267721645293)
      ·
        refine ⟨156381711589035850395616985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417017897570762267721645293 156381711589035850395616985)
        ·
          refine ⟨117286283691776887796712739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156381711589035850395616985 117286283691776887796712739)
          ·
            refine ⟨175929425537665331695069109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117286283691776887796712739 175929425537665331695069109)
            ·
              refine ⟨16493383644156124846412729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175929425537665331695069109 16493383644156124846412729)
              ·
                refine ⟨12370037733117093634809547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16493383644156124846412729 12370037733117093634809547)
                ·
                  refine ⟨18555056599675640452214321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12370037733117093634809547 18555056599675640452214321)
                  ·
                    refine ⟨13916292449756730339160741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18555056599675640452214321 13916292449756730339160741)
                    ·
                      refine ⟨2609304834329386938592639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13916292449756730339160741 2609304834329386938592639)
                      ·
                        rfl

theorem cell23_5081603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_5081603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081603 prefixEnd_5081603 := by exact prefixLift 5081603
  have htrace : WordTrace (prefixWord ++ tailWord_5081603) baseStart_5081603 baseEnd_5081603 := by
    simpa [prefixWord, tailWord_5081603, baseEnd_5081603] using wordTrace_append hprefix tailTrace_5081603
  have hstable : (prefixWord ++ tailWord_5081603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081603).length < 2 ^ (prefixWord ++ tailWord_5081603).sum := by decide
  have hdescent : baseEnd_5081603 < baseStart_5081603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081616 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_5081616 : Nat := 118140960795 + 5081616 * 2 ^ 59
def prefixEnd_5081616 : Nat := 4983230072969 + 3 ^ 40 * 5081616 * 2
def baseEnd_5081616 : Nat := 2609311509577895387730079

theorem tailTrace_5081616 : CollatzResearch.WordTrace tailWord_5081616 prefixEnd_5081616 2609311509577895387730079 := by
  unfold tailWord_5081616
  simp only [CollatzResearch.WordTrace]
  refine ⟨92670880979090288881588351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123561174638787051842117801 92670880979090288881588351)
  ·
    refine ⟨139006321468635433322382527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92670880979090288881588351 139006321468635433322382527)
    ·
      refine ⟨208509482202953149983573791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139006321468635433322382527 208509482202953149983573791)
      ·
        refine ⟨312764223304429724975360687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208509482202953149983573791 312764223304429724975360687)
        ·
          refine ⟨469146334956644587463041031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312764223304429724975360687 469146334956644587463041031)
          ·
            refine ⟨703719502434966881194561547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469146334956644587463041031 703719502434966881194561547)
            ·
              refine ⟨1055579253652450321791842321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703719502434966881194561547 1055579253652450321791842321)
              ·
                refine ⟨791684440239337741343881741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055579253652450321791842321 791684440239337741343881741)
                ·
                  refine ⟨296881665089751653003955653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791684440239337741343881741 296881665089751653003955653)
                  ·
                    refine ⟨55665312204328434938241685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296881665089751653003955653 55665312204328434938241685)
                    ·
                      refine ⟨2609311509577895387730079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55665312204328434938241685 2609311509577895387730079)
                      ·
                        rfl

theorem cell23_5081616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_5081616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081616 prefixEnd_5081616 := by exact prefixLift 5081616
  have htrace : WordTrace (prefixWord ++ tailWord_5081616) baseStart_5081616 baseEnd_5081616 := by
    simpa [prefixWord, tailWord_5081616, baseEnd_5081616] using wordTrace_append hprefix tailTrace_5081616
  have hstable : (prefixWord ++ tailWord_5081616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081616).length < 2 ^ (prefixWord ++ tailWord_5081616).sum := by decide
  have hdescent : baseEnd_5081616 < baseStart_5081616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081645 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5081645 : Nat := 118140960795 + 5081645 * 2 ^ 59
def prefixEnd_5081645 : Nat := 4983230072969 + 3 ^ 40 * 5081645 * 2
def baseEnd_5081645 : Nat := 2609326400516875774267447

theorem tailTrace_5081645 : CollatzResearch.WordTrace tailWord_5081645 prefixEnd_5081645 2609326400516875774267447 := by
  unfold tailWord_5081645
  simp only [CollatzResearch.WordTrace]
  refine ⟨185342819675075515715982389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123561879783383677143988259 185342819675075515715982389)
  ·
    refine ⟨17375889344538329598373349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185342819675075515715982389 17375889344538329598373349)
    ·
      refine ⟨3257979252100936799695003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17375889344538329598373349 3257979252100936799695003)
      ·
        refine ⟨4886968878151405199542505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257979252100936799695003 4886968878151405199542505)
        ·
          refine ⟨3665226658613553899656879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4886968878151405199542505 3665226658613553899656879)
          ·
            refine ⟨5497839987920330849485319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665226658613553899656879 5497839987920330849485319)
            ·
              refine ⟨8246759981880496274227979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497839987920330849485319 8246759981880496274227979)
              ·
                refine ⟨12370139972820744411341969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8246759981880496274227979 12370139972820744411341969)
                ·
                  refine ⟨9277604979615558308506477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12370139972820744411341969 9277604979615558308506477)
                  ·
                    refine ⟨3479101867355834365689929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9277604979615558308506477 3479101867355834365689929)
                    ·
                      refine ⟨2609326400516875774267447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479101867355834365689929 2609326400516875774267447)
                      ·
                        rfl

theorem cell23_5081645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5081645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081645 prefixEnd_5081645 := by exact prefixLift 5081645
  have htrace : WordTrace (prefixWord ++ tailWord_5081645) baseStart_5081645 baseEnd_5081645 := by
    simpa [prefixWord, tailWord_5081645, baseEnd_5081645] using wordTrace_append hprefix tailTrace_5081645
  have hstable : (prefixWord ++ tailWord_5081645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081645).length < 2 ^ (prefixWord ++ tailWord_5081645).sum := by decide
  have hdescent : baseEnd_5081645 < baseStart_5081645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081653 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5081653 : Nat := 118140960795 + 5081653 * 2 ^ 59
def prefixEnd_5081653 : Nat := 4983230072969 + 3 ^ 40 * 5081653 * 2
def baseEnd_5081653 : Nat := 2609330508362111742967409

theorem tailTrace_5081653 : CollatzResearch.WordTrace tailWord_5081653 prefixEnd_5081653 2609330508362111742967409 := by
  unfold tailWord_5081653
  simp only [CollatzResearch.WordTrace]
  refine ⟨185343111459046533082273613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123562074306031022054849075 185343111459046533082273613)
  ·
    refine ⟨69503666797142449905852605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185343111459046533082273613 69503666797142449905852605)
    ·
      refine ⟨26063875048928418714694727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69503666797142449905852605 26063875048928418714694727)
      ·
        refine ⟨39095812573392628072042091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26063875048928418714694727 39095812573392628072042091)
        ·
          refine ⟨58643718860088942108063137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39095812573392628072042091 58643718860088942108063137)
          ·
            refine ⟨43982789145066706581047353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58643718860088942108063137 43982789145066706581047353)
            ·
              refine ⟨32987091858800029935785515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43982789145066706581047353 32987091858800029935785515)
              ·
                refine ⟨49480637788200044903678273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32987091858800029935785515 49480637788200044903678273)
                ·
                  refine ⟨37110478341150033677758705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49480637788200044903678273 37110478341150033677758705)
                  ·
                    refine ⟨27832858755862525258319029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37110478341150033677758705 27832858755862525258319029)
                    ·
                      refine ⟨2609330508362111742967409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27832858755862525258319029 2609330508362111742967409)
                      ·
                        rfl

theorem cell23_5081653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5081653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081653 prefixEnd_5081653 := by exact prefixLift 5081653
  have htrace : WordTrace (prefixWord ++ tailWord_5081653) baseStart_5081653 baseEnd_5081653 := by
    simpa [prefixWord, tailWord_5081653, baseEnd_5081653] using wordTrace_append hprefix tailTrace_5081653
  have hstable : (prefixWord ++ tailWord_5081653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081653).length < 2 ^ (prefixWord ++ tailWord_5081653).sum := by decide
  have hdescent : baseEnd_5081653 < baseStart_5081653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081668 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5081668 : Nat := 118140960795 + 5081668 * 2 ^ 59
def prefixEnd_5081668 : Nat := 4983230072969 + 3 ^ 40 * 5081668 * 2
def baseEnd_5081668 : Nat := 869779403523976394759947

theorem tailTrace_5081668 : CollatzResearch.WordTrace tailWord_5081668 prefixEnd_5081668 869779403523976394759947 := by
  unfold tailWord_5081668
  simp only [CollatzResearch.WordTrace]
  refine ⟨92671829276996095322034829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123562439035994793762713105 92671829276996095322034829)
  ·
    refine ⟨34751935978873535745763061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92671829276996095322034829 34751935978873535745763061)
    ·
      refine ⟨3257993998019393976165287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34751935978873535745763061 3257993998019393976165287)
      ·
        refine ⟨4886990997029090964247931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257993998019393976165287 4886990997029090964247931)
        ·
          refine ⟨7330486495543636446371897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886990997029090964247931 7330486495543636446371897)
          ·
            refine ⟨5497864871657727334778923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7330486495543636446371897 5497864871657727334778923)
            ·
              refine ⟨8246797307486591002168385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497864871657727334778923 8246797307486591002168385)
              ·
                refine ⟨6185097980614943251626289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246797307486591002168385 6185097980614943251626289)
                ·
                  refine ⟨4638823485461207438719717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6185097980614943251626289 4638823485461207438719717)
                  ·
                    refine ⟨869779403523976394759947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4638823485461207438719717 869779403523976394759947)
                    ·
                      rfl

theorem cell23_5081668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5081668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081668 prefixEnd_5081668 := by exact prefixLift 5081668
  have htrace : WordTrace (prefixWord ++ tailWord_5081668) baseStart_5081668 baseEnd_5081668 := by
    simpa [prefixWord, tailWord_5081668, baseEnd_5081668] using wordTrace_append hprefix tailTrace_5081668
  have hstable : (prefixWord ++ tailWord_5081668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081668).length < 2 ^ (prefixWord ++ tailWord_5081668).sum := by decide
  have hdescent : baseEnd_5081668 < baseStart_5081668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081674 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_5081674 : Nat := 118140960795 + 5081674 * 2 ^ 59
def prefixEnd_5081674 : Nat := 4983230072969 + 3 ^ 40 * 5081674 * 2
def baseEnd_5081674 : Nat := 2609341291455856160804813

theorem tailTrace_5081674 : CollatzResearch.WordTrace tailWord_5081674 prefixEnd_5081674 2609341291455856160804813 := by
  unfold tailWord_5081674
  simp only [CollatzResearch.WordTrace]
  refine ⟨46335969347992613417197019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123562584927980302445858717 46335969347992613417197019)
  ·
    refine ⟨69503954021988920125795529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46335969347992613417197019 69503954021988920125795529)
    ·
      refine ⟨52127965516491690094346647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69503954021988920125795529 52127965516491690094346647)
      ·
        refine ⟨78191948274737535141519971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52127965516491690094346647 78191948274737535141519971)
        ·
          refine ⟨117287922412106302712279957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78191948274737535141519971 117287922412106302712279957)
          ·
            refine ⟨5497871363067482939638123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117287922412106302712279957 5497871363067482939638123)
            ·
              refine ⟨8246807044601224409457185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497871363067482939638123 8246807044601224409457185)
              ·
                refine ⟨6185105283450918307092889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246807044601224409457185 6185105283450918307092889)
                ·
                  refine ⟨4638828962588188730319667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6185105283450918307092889 4638828962588188730319667)
                  ·
                    refine ⟨6958243443882283095479501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4638828962588188730319667 6958243443882283095479501)
                    ·
                      refine ⟨2609341291455856160804813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958243443882283095479501 2609341291455856160804813)
                      ·
                        rfl

theorem cell23_5081674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_5081674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081674 prefixEnd_5081674 := by exact prefixLift 5081674
  have htrace : WordTrace (prefixWord ++ tailWord_5081674) baseStart_5081674 baseEnd_5081674 := by
    simpa [prefixWord, tailWord_5081674, baseEnd_5081674] using wordTrace_append hprefix tailTrace_5081674
  have hstable : (prefixWord ++ tailWord_5081674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081674).length < 2 ^ (prefixWord ++ tailWord_5081674).sum := by decide
  have hdescent : baseEnd_5081674 < baseStart_5081674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081697 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_5081697 : Nat := 118140960795 + 5081697 * 2 ^ 59
def prefixEnd_5081697 : Nat := 4983230072969 + 3 ^ 40 * 5081697 * 2
def baseEnd_5081697 : Nat := 2609353101510909570817207

theorem tailTrace_5081697 : CollatzResearch.WordTrace tailWord_5081697 prefixEnd_5081697 2609353101510909570817207 := by
  unfold tailWord_5081697
  simp only [CollatzResearch.WordTrace]
  refine ⟨185344716270887128596875345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123563144180591419064583563 185344716270887128596875345)
  ·
    refine ⟨139008537203165346447656509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185344716270887128596875345 139008537203165346447656509)
    ·
      refine ⟨52128201451187004917871191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139008537203165346447656509 52128201451187004917871191)
      ·
        refine ⟨78192302176780507376806787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52128201451187004917871191 78192302176780507376806787)
        ·
          refine ⟨117288453265170761065210181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78192302176780507376806787 117288453265170761065210181)
          ·
            refine ⟨21991584987219517699726909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117288453265170761065210181 21991584987219517699726909)
            ·
              refine ⟨8246844370207319137397591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21991584987219517699726909 8246844370207319137397591)
              ·
                refine ⟨12370266555310978706096387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8246844370207319137397591 12370266555310978706096387)
                ·
                  refine ⟨18555399832966468059144581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12370266555310978706096387 18555399832966468059144581)
                  ·
                    refine ⟨3479137468681212761089609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18555399832966468059144581 3479137468681212761089609)
                    ·
                      refine ⟨2609353101510909570817207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479137468681212761089609 2609353101510909570817207)
                      ·
                        rfl

theorem cell23_5081697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_5081697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081697 prefixEnd_5081697 := by exact prefixLift 5081697
  have htrace : WordTrace (prefixWord ++ tailWord_5081697) baseStart_5081697 baseEnd_5081697 := by
    simpa [prefixWord, tailWord_5081697, baseEnd_5081697] using wordTrace_append hprefix tailTrace_5081697
  have hstable : (prefixWord ++ tailWord_5081697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081697).length < 2 ^ (prefixWord ++ tailWord_5081697).sum := by decide
  have hdescent : baseEnd_5081697 < baseStart_5081697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081717 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5081717 : Nat := 118140960795 + 5081717 * 2 ^ 59
def prefixEnd_5081717 : Nat := 4983230072969 + 3 ^ 40 * 5081717 * 2
def baseEnd_5081717 : Nat := 2609363371123999492567115

theorem tailTrace_5081717 : CollatzResearch.WordTrace tailWord_5081717 prefixEnd_5081717 2609363371123999492567115 := by
  unfold tailWord_5081717
  simp only [CollatzResearch.WordTrace]
  refine ⟨185345445730814672012603405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123563630487209781341735603 185345445730814672012603405)
  ·
    refine ⟨69504542149055502004726277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185345445730814672012603405 69504542149055502004726277)
    ·
      refine ⟨13032101652947906625886177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69504542149055502004726277 13032101652947906625886177)
      ·
        refine ⟨9774076239710929969414633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13032101652947906625886177 9774076239710929969414633)
        ·
          refine ⟨7330557179783197477060975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9774076239710929969414633 7330557179783197477060975)
          ·
            refine ⟨10995835769674796215591463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7330557179783197477060975 10995835769674796215591463)
            ·
              refine ⟨16493753654512194323387195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10995835769674796215591463 16493753654512194323387195)
              ·
                refine ⟨24740630481768291485080793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16493753654512194323387195 24740630481768291485080793)
                ·
                  refine ⟨18555472861326218613810595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24740630481768291485080793 18555472861326218613810595)
                  ·
                    refine ⟨27833209291989327920715893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18555472861326218613810595 27833209291989327920715893)
                    ·
                      refine ⟨2609363371123999492567115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27833209291989327920715893 2609363371123999492567115)
                      ·
                        rfl

theorem cell23_5081717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5081717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081717 prefixEnd_5081717 := by exact prefixLift 5081717
  have htrace : WordTrace (prefixWord ++ tailWord_5081717) baseStart_5081717 baseEnd_5081717 := by
    simpa [prefixWord, tailWord_5081717, baseEnd_5081717] using wordTrace_append hprefix tailTrace_5081717
  have hstable : (prefixWord ++ tailWord_5081717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081717).length < 2 ^ (prefixWord ++ tailWord_5081717).sum := by decide
  have hdescent : baseEnd_5081717 < baseStart_5081717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081743 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_5081743 : Nat := 118140960795 + 5081743 * 2 ^ 59
def prefixEnd_5081743 : Nat := 4983230072969 + 3 ^ 40 * 5081743 * 2
def baseEnd_5081743 : Nat := 2609376721621016390841995

theorem tailTrace_5081743 : CollatzResearch.WordTrace tailWord_5081743 prefixEnd_5081743 2609376721621016390841995 := by
  unfold tailWord_5081743
  simp only [CollatzResearch.WordTrace]
  refine ⟨185346394028720478453049883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123564262685813652302033255 185346394028720478453049883)
  ·
    refine ⟨278019591043080717679574825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185346394028720478453049883 278019591043080717679574825)
    ·
      refine ⟨208514693282310538259681119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278019591043080717679574825 208514693282310538259681119)
      ·
        refine ⟨312772039923465807389521679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208514693282310538259681119 312772039923465807389521679)
        ·
          refine ⟨469158059885198711084282519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312772039923465807389521679 469158059885198711084282519)
          ·
            refine ⟨703737089827798066626423779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469158059885198711084282519 703737089827798066626423779)
            ·
              refine ⟨1055605634741697099939635669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703737089827798066626423779 1055605634741697099939635669)
              ·
                refine ⟨24740757064258525779835211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1055605634741697099939635669 24740757064258525779835211)
                ·
                  refine ⟨37111135596387788669752817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24740757064258525779835211 37111135596387788669752817)
                  ·
                    refine ⟨27833351697290841502314613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37111135596387788669752817 27833351697290841502314613)
                    ·
                      refine ⟨2609376721621016390841995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27833351697290841502314613 2609376721621016390841995)
                      ·
                        rfl

theorem cell23_5081743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_5081743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081743 prefixEnd_5081743 := by exact prefixLift 5081743
  have htrace : WordTrace (prefixWord ++ tailWord_5081743) baseStart_5081743 baseEnd_5081743 := by
    simpa [prefixWord, tailWord_5081743, baseEnd_5081743] using wordTrace_append hprefix tailTrace_5081743
  have hstable : (prefixWord ++ tailWord_5081743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081743).length < 2 ^ (prefixWord ++ tailWord_5081743).sum := by decide
  have hdescent : baseEnd_5081743 < baseStart_5081743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081748 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5081748 : Nat := 118140960795 + 5081748 * 2 ^ 59
def prefixEnd_5081748 : Nat := 4983230072969 + 3 ^ 40 * 5081748 * 2
def baseEnd_5081748 : Nat := 2609379289024288871279473

theorem tailTrace_5081748 : CollatzResearch.WordTrace tailWord_5081748 prefixEnd_5081748 2609379289024288871279473 := by
  unfold tailWord_5081748
  simp only [CollatzResearch.WordTrace]
  refine ⟨92673288196851182153490949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123564384262468242871321265 92673288196851182153490949)
  ·
    refine ⟨17376241536909596653779553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92673288196851182153490949 17376241536909596653779553)
    ·
      refine ⟨13032181152682197490334665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17376241536909596653779553 13032181152682197490334665)
      ·
        refine ⟨9774135864511648117750999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13032181152682197490334665 9774135864511648117750999)
        ·
          refine ⟨14661203796767472176626499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774135864511648117750999 14661203796767472176626499)
          ·
            refine ⟨21991805695151208264939749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14661203796767472176626499 21991805695151208264939749)
            ·
              refine ⟨4123463567840851549676203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21991805695151208264939749 4123463567840851549676203)
              ·
                refine ⟨6185195351761277324514305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123463567840851549676203 6185195351761277324514305)
                ·
                  refine ⟨4638896513820957993385729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6185195351761277324514305 4638896513820957993385729)
                  ·
                    refine ⟨3479172385365718495039297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638896513820957993385729 3479172385365718495039297)
                    ·
                      refine ⟨2609379289024288871279473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479172385365718495039297 2609379289024288871279473)
                      ·
                        rfl

theorem cell23_5081748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5081748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081748 prefixEnd_5081748 := by exact prefixLift 5081748
  have htrace : WordTrace (prefixWord ++ tailWord_5081748) baseStart_5081748 baseEnd_5081748 := by
    simpa [prefixWord, tailWord_5081748, baseEnd_5081748] using wordTrace_append hprefix tailTrace_5081748
  have hstable : (prefixWord ++ tailWord_5081748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081748).length < 2 ^ (prefixWord ++ tailWord_5081748).sum := by decide
  have hdescent : baseEnd_5081748 < baseStart_5081748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081790 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5081790 : Nat := 118140960795 + 5081790 * 2 ^ 59
def prefixEnd_5081790 : Nat := 4983230072969 + 3 ^ 40 * 5081790 * 2
def baseEnd_5081790 : Nat := 2609400855211777706954279

theorem tailTrace_5081790 : CollatzResearch.WordTrace tailWord_5081790 prefixEnd_5081790 2609400855211777706954279 := by
  unfold tailWord_5081790
  simp only [CollatzResearch.WordTrace]
  refine ⟨23168513532443775685001353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123565405506366803653340549 23168513532443775685001353)
  ·
    refine ⟨17376385149332831763751015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23168513532443775685001353 17376385149332831763751015)
    ·
      refine ⟨26064577723999247645626523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17376385149332831763751015 26064577723999247645626523)
      ·
        refine ⟨39096866585998871468439785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26064577723999247645626523 39096866585998871468439785)
        ·
          refine ⟨29322649939499153601329839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39096866585998871468439785 29322649939499153601329839)
          ·
            refine ⟨43983974909248730401994759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29322649939499153601329839 43983974909248730401994759)
            ·
              refine ⟨65975962363873095602992139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43983974909248730401994759 65975962363873095602992139)
              ·
                refine ⟨98963943545809643404488209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65975962363873095602992139 98963943545809643404488209)
                ·
                  refine ⟨74222957659357232553366157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98963943545809643404488209 74222957659357232553366157)
                  ·
                    refine ⟨27833609122258962207512309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74222957659357232553366157 27833609122258962207512309)
                    ·
                      refine ⟨2609400855211777706954279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27833609122258962207512309 2609400855211777706954279)
                      ·
                        rfl

theorem cell23_5081790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5081790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081790 prefixEnd_5081790 := by exact prefixLift 5081790
  have htrace : WordTrace (prefixWord ++ tailWord_5081790) baseStart_5081790 baseEnd_5081790 := by
    simpa [prefixWord, tailWord_5081790, baseEnd_5081790] using wordTrace_append hprefix tailTrace_5081790
  have hstable : (prefixWord ++ tailWord_5081790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081790).length < 2 ^ (prefixWord ++ tailWord_5081790).sum := by decide
  have hdescent : baseEnd_5081790 < baseStart_5081790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081804 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5081804 : Nat := 118140960795 + 5081804 * 2 ^ 59
def prefixEnd_5081804 : Nat := 4983230072969 + 3 ^ 40 * 5081804 * 2
def baseEnd_5081804 : Nat := 2609408043940940652179215

theorem tailTrace_5081804 : CollatzResearch.WordTrace tailWord_5081804 prefixEnd_5081804 2609408043940940652179215 := by
  unfold tailWord_5081804
  simp only [CollatzResearch.WordTrace]
  refine ⟨92674309440749742935510233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123565745920999657247346977 92674309440749742935510233)
  ·
    refine ⟨69505732080562307201632675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92674309440749742935510233 69505732080562307201632675)
    ·
      refine ⟨104258598120843460802449013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69505732080562307201632675 104258598120843460802449013)
      ·
        refine ⟨9774243573829074450229595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104258598120843460802449013 9774243573829074450229595)
        ·
          refine ⟨14661365360743611675344393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774243573829074450229595 14661365360743611675344393)
          ·
            refine ⟨10996024020557708756508295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14661365360743611675344393 10996024020557708756508295)
            ·
              refine ⟨16494036030836563134762443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996024020557708756508295 16494036030836563134762443)
              ·
                refine ⟨24741054046254844702143665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16494036030836563134762443 24741054046254844702143665)
                ·
                  refine ⟨18555790534691133526607749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24741054046254844702143665 18555790534691133526607749)
                  ·
                    refine ⟨3479210725254587536238953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18555790534691133526607749 3479210725254587536238953)
                    ·
                      refine ⟨2609408043940940652179215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479210725254587536238953 2609408043940940652179215)
                      ·
                        rfl

theorem cell23_5081804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5081804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081804 prefixEnd_5081804 := by exact prefixLift 5081804
  have htrace : WordTrace (prefixWord ++ tailWord_5081804) baseStart_5081804 baseEnd_5081804 := by
    simpa [prefixWord, tailWord_5081804, baseEnd_5081804] using wordTrace_append hprefix tailTrace_5081804
  have hstable : (prefixWord ++ tailWord_5081804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081804).length < 2 ^ (prefixWord ++ tailWord_5081804).sum := by decide
  have hdescent : baseEnd_5081804 < baseStart_5081804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081847 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 4, 3, 2]
def baseStart_5081847 : Nat := 118140960795 + 5081847 * 2 ^ 59
def prefixEnd_5081847 : Nat := 4983230072969 + 3 ^ 40 * 5081847 * 2
def baseEnd_5081847 : Nat := 2609430123609083983941517

theorem tailTrace_5081847 : CollatzResearch.WordTrace tailWord_5081847 prefixEnd_5081847 2609430123609083983941517 := by
  unfold tailWord_5081847
  simp only [CollatzResearch.WordTrace]
  refine ⟨185350187220343704214835795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123566791480229136143223863 185350187220343704214835795)
  ·
    refine ⟨278025280830515556322253693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185350187220343704214835795 278025280830515556322253693)
    ·
      refine ⟨104259480311443333620845135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278025280830515556322253693 104259480311443333620845135)
      ·
        refine ⟨156389220467165000431267703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104259480311443333620845135 156389220467165000431267703)
        ·
          refine ⟨234583830700747500646901555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156389220467165000431267703 234583830700747500646901555)
          ·
            refine ⟨351875746051121250970352333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234583830700747500646901555 351875746051121250970352333)
            ·
              refine ⟨131953404769170469113882125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351875746051121250970352333 131953404769170469113882125)
              ·
                refine ⟨49482526788438925917705797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131953404769170469113882125 49482526788438925917705797)
                ·
                  refine ⟨9277973772832298609569837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49482526788438925917705797 9277973772832298609569837)
                  ·
                    refine ⟨3479240164812111978588689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9277973772832298609569837 3479240164812111978588689)
                    ·
                      refine ⟨2609430123609083983941517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479240164812111978588689 2609430123609083983941517)
                      ·
                        rfl

theorem cell23_5081847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_5081847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081847 prefixEnd_5081847 := by exact prefixLift 5081847
  have htrace : WordTrace (prefixWord ++ tailWord_5081847) baseStart_5081847 baseEnd_5081847 := by
    simpa [prefixWord, tailWord_5081847, baseEnd_5081847] using wordTrace_append hprefix tailTrace_5081847
  have hstable : (prefixWord ++ tailWord_5081847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081847).length < 2 ^ (prefixWord ++ tailWord_5081847).sum := by decide
  have hdescent : baseEnd_5081847 < baseStart_5081847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081877 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_5081877 : Nat := 118140960795 + 5081877 * 2 ^ 59
def prefixEnd_5081877 : Nat := 4983230072969 + 3 ^ 40 * 5081877 * 2
def baseEnd_5081877 : Nat := 2609445528028718866566379

theorem tailTrace_5081877 : CollatzResearch.WordTrace tailWord_5081877 prefixEnd_5081877 2609445528028718866566379 := by
  unfold tailWord_5081877
  simp only [CollatzResearch.WordTrace]
  refine ⟨185351281410235019338427885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123567520940156679558951923 185351281410235019338427885)
  ·
    refine ⟨69506730528838132251910457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185351281410235019338427885 69506730528838132251910457)
    ·
      refine ⟨52130047896628599188932843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69506730528838132251910457 52130047896628599188932843)
      ·
        refine ⟨78195071844942898783399265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52130047896628599188932843 78195071844942898783399265)
        ·
          refine ⟨58646303883707174087549449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78195071844942898783399265 58646303883707174087549449)
          ·
            refine ⟨43984727912780380565662087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58646303883707174087549449 43984727912780380565662087)
            ·
              refine ⟨65977091869170570848493131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43984727912780380565662087 65977091869170570848493131)
              ·
                refine ⟨98965637803755856272739697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65977091869170570848493131 98965637803755856272739697)
                ·
                  refine ⟨74224228352816892204554773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98965637803755856272739697 74224228352816892204554773)
                  ·
                    refine ⟨3479260704038291822088505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74224228352816892204554773 3479260704038291822088505)
                    ·
                      refine ⟨2609445528028718866566379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479260704038291822088505 2609445528028718866566379)
                      ·
                        rfl

theorem cell23_5081877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_5081877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081877 prefixEnd_5081877 := by exact prefixLift 5081877
  have htrace : WordTrace (prefixWord ++ tailWord_5081877) baseStart_5081877 baseEnd_5081877 := by
    simpa [prefixWord, tailWord_5081877, baseEnd_5081877] using wordTrace_append hprefix tailTrace_5081877
  have hstable : (prefixWord ++ tailWord_5081877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081877).length < 2 ^ (prefixWord ++ tailWord_5081877).sum := by decide
  have hdescent : baseEnd_5081877 < baseStart_5081877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081880 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5081880 : Nat := 118140960795 + 5081880 * 2 ^ 59
def prefixEnd_5081880 : Nat := 4983230072969 + 3 ^ 40 * 5081880 * 2
def baseEnd_5081880 : Nat := 2609447068470682354828865

theorem tailTrace_5081880 : CollatzResearch.WordTrace tailWord_5081880 prefixEnd_5081880 2609447068470682354828865 := by
  unfold tailWord_5081880
  simp only [CollatzResearch.WordTrace]
  refine ⟨92675695414612075425393547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123567593886149433900524729 92675695414612075425393547)
  ·
    refine ⟨139013543121918113138090321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92675695414612075425393547 139013543121918113138090321)
    ·
      refine ⟨104260157341438584853567741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139013543121918113138090321 104260157341438584853567741)
      ·
        refine ⟨39097559003039469320087903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104260157341438584853567741 39097559003039469320087903)
        ·
          refine ⟨58646338504559203980131855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39097559003039469320087903 58646338504559203980131855)
          ·
            refine ⟨87969507756838805970197783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58646338504559203980131855 87969507756838805970197783)
            ·
              refine ⟨131954261635258208955296675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87969507756838805970197783 131954261635258208955296675)
              ·
                refine ⟨197931392452887313432945013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131954261635258208955296675 197931392452887313432945013)
                ·
                  refine ⟨18556068042458185634338595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197931392452887313432945013 18556068042458185634338595)
                  ·
                    refine ⟨27834102063687278451507893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18556068042458185634338595 27834102063687278451507893)
                    ·
                      refine ⟨2609447068470682354828865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27834102063687278451507893 2609447068470682354828865)
                      ·
                        rfl

theorem cell23_5081880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5081880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081880 prefixEnd_5081880 := by exact prefixLift 5081880
  have htrace : WordTrace (prefixWord ++ tailWord_5081880) baseStart_5081880 baseEnd_5081880 := by
    simpa [prefixWord, tailWord_5081880, baseEnd_5081880] using wordTrace_append hprefix tailTrace_5081880
  have hstable : (prefixWord ++ tailWord_5081880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081880).length < 2 ^ (prefixWord ++ tailWord_5081880).sum := by decide
  have hdescent : baseEnd_5081880 < baseStart_5081880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081887 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 4, 4]
def baseStart_5081887 : Nat := 118140960795 + 5081887 * 2 ^ 59
def prefixEnd_5081887 : Nat := 4983230072969 + 3 ^ 40 * 5081887 * 2
def baseEnd_5081887 : Nat := 869816887611754609147111

theorem tailTrace_5081887 : CollatzResearch.WordTrace tailWord_5081887 prefixEnd_5081887 869816887611754609147111 := by
  unfold tailWord_5081887
  simp only [CollatzResearch.WordTrace]
  refine ⟨185351646140198791046291915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123567764093465860697527943 185351646140198791046291915)
  ·
    refine ⟨278027469210298186569437873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185351646140198791046291915 278027469210298186569437873)
    ·
      refine ⟨208520601907723639927078405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278027469210298186569437873 208520601907723639927078405)
      ·
        refine ⟨39097612857698182486327201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208520601907723639927078405 39097612857698182486327201)
        ·
          refine ⟨29323209643273636864745401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39097612857698182486327201 29323209643273636864745401)
          ·
            refine ⟨21992407232455227648559051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29323209643273636864745401 21992407232455227648559051)
            ·
              refine ⟨32988610848682841472838577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21992407232455227648559051 32988610848682841472838577)
              ·
                refine ⟨24741458136512131104628933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32988610848682841472838577 24741458136512131104628933)
                ·
                  refine ⟨4639023400596024582117925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24741458136512131104628933 4639023400596024582117925)
                  ·
                    refine ⟨869816887611754609147111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639023400596024582117925 869816887611754609147111)
                    ·
                      rfl

theorem cell23_5081887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_5081887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081887 prefixEnd_5081887 := by exact prefixLift 5081887
  have htrace : WordTrace (prefixWord ++ tailWord_5081887) baseStart_5081887 baseEnd_5081887 := by
    simpa [prefixWord, tailWord_5081887, baseEnd_5081887] using wordTrace_append hprefix tailTrace_5081887
  have hstable : (prefixWord ++ tailWord_5081887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081887).length < 2 ^ (prefixWord ++ tailWord_5081887).sum := by decide
  have hdescent : baseEnd_5081887 < baseStart_5081887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081888 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 1, 1, 3]
def baseStart_5081888 : Nat := 118140960795 + 5081888 * 2 ^ 59
def prefixEnd_5081888 : Nat := 4983230072969 + 3 ^ 40 * 5081888 * 2
def baseEnd_5081888 : Nat := 2609451176315918323528829

theorem tailTrace_5081888 : CollatzResearch.WordTrace tailWord_5081888 prefixEnd_5081888 2609451176315918323528829 := by
  unfold tailWord_5081888
  simp only [CollatzResearch.WordTrace]
  refine ⟨92675841306597584108539159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123567788408796778811385545 92675841306597584108539159)
  ·
    refine ⟨139013761959896376162808739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92675841306597584108539159 139013761959896376162808739)
    ·
      refine ⟨208520642939844564244213109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139013761959896376162808739 208520642939844564244213109)
      ·
        refine ⟨19548810275610427897894979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208520642939844564244213109 19548810275610427897894979)
        ·
          refine ⟨29323215413415641846842469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19548810275610427897894979 29323215413415641846842469)
          ·
            refine ⟨5498102890015432846282963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29323215413415641846842469 5498102890015432846282963)
            ·
              refine ⟨8247154335023149269424445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498102890015432846282963 8247154335023149269424445)
              ·
                refine ⟨3092682875633680976034167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8247154335023149269424445 3092682875633680976034167)
                ·
                  refine ⟨4639024313450521464051251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092682875633680976034167 4639024313450521464051251)
                  ·
                    refine ⟨6958536470175782196076877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4639024313450521464051251 6958536470175782196076877)
                    ·
                      refine ⟨2609451176315918323528829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958536470175782196076877 2609451176315918323528829)
                      ·
                        rfl

theorem cell23_5081888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_5081888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081888 prefixEnd_5081888 := by exact prefixLift 5081888
  have htrace : WordTrace (prefixWord ++ tailWord_5081888) baseStart_5081888 baseEnd_5081888 := by
    simpa [prefixWord, tailWord_5081888, baseEnd_5081888] using wordTrace_append hprefix tailTrace_5081888
  have hstable : (prefixWord ++ tailWord_5081888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081888).length < 2 ^ (prefixWord ++ tailWord_5081888).sum := by decide
  have hdescent : baseEnd_5081888 < baseStart_5081888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081898 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5081898 : Nat := 118140960795 + 5081898 * 2 ^ 59
def prefixEnd_5081898 : Nat := 4983230072969 + 3 ^ 40 * 5081898 * 2
def baseEnd_5081898 : Nat := 2609456311122463284403783

theorem tailTrace_5081898 : CollatzResearch.WordTrace tailWord_5081898 prefixEnd_5081898 2609456311122463284403783 := by
  unfold tailWord_5081898
  simp only [CollatzResearch.WordTrace]
  refine ⟨46338011835789734981235587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123568031562105959949961565 46338011835789734981235587)
  ·
    refine ⟨69507017753684602471853381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46338011835789734981235587 69507017753684602471853381)
    ·
      refine ⟨13032565828815862963472509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69507017753684602471853381 13032565828815862963472509)
      ·
        refine ⟨4887212185805948611302191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13032565828815862963472509 4887212185805948611302191)
        ·
          refine ⟨7330818278708922916953287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887212185805948611302191 7330818278708922916953287)
          ·
            refine ⟨10996227418063384375429931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7330818278708922916953287 10996227418063384375429931)
            ·
              refine ⟨16494341127095076563144897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996227418063384375429931 16494341127095076563144897)
              ·
                refine ⟨12370755845321307422358673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16494341127095076563144897 12370755845321307422358673)
                ·
                  refine ⟨9278066883990980566769005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12370755845321307422358673 9278066883990980566769005)
                  ·
                    refine ⟨3479275081496617712538377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9278066883990980566769005 3479275081496617712538377)
                    ·
                      refine ⟨2609456311122463284403783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479275081496617712538377 2609456311122463284403783)
                      ·
                        rfl

theorem cell23_5081898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5081898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081898 prefixEnd_5081898 := by exact prefixLift 5081898
  have htrace : WordTrace (prefixWord ++ tailWord_5081898) baseStart_5081898 baseEnd_5081898 := by
    simpa [prefixWord, tailWord_5081898, baseEnd_5081898] using wordTrace_append hprefix tailTrace_5081898
  have hstable : (prefixWord ++ tailWord_5081898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081898).length < 2 ^ (prefixWord ++ tailWord_5081898).sum := by decide
  have hdescent : baseEnd_5081898 < baseStart_5081898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081927 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_5081927 : Nat := 118140960795 + 5081927 * 2 ^ 59
def prefixEnd_5081927 : Nat := 4983230072969 + 3 ^ 40 * 5081927 * 2
def baseEnd_5081927 : Nat := 2609471202061443670941149

theorem tailTrace_5081927 : CollatzResearch.WordTrace tailWord_5081927 prefixEnd_5081927 2609471202061443670941149 := by
  unfold tailWord_5081927
  simp only [CollatzResearch.WordTrace]
  refine ⟨185353105060053877877748035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123568736706702585251832023 185353105060053877877748035)
  ·
    refine ⟨278029657590080816816622053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185353105060053877877748035 278029657590080816816622053)
    ·
      refine ⟨52130560798140153153116635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278029657590080816816622053 52130560798140153153116635)
      ·
        refine ⟨78195841197210229729674953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52130560798140153153116635 78195841197210229729674953)
        ·
          refine ⟨58646880897907672297256215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78195841197210229729674953 58646880897907672297256215)
          ·
            refine ⟨87970321346861508445884323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58646880897907672297256215 87970321346861508445884323)
            ·
              refine ⟨131955482020292262668826485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87970321346861508445884323 131955482020292262668826485)
              ·
                refine ⟨12370826439402399625202483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131955482020292262668826485 12370826439402399625202483)
                ·
                  refine ⟨18556239659103599437803725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12370826439402399625202483 18556239659103599437803725)
                  ·
                    refine ⟨6958589872163849789176397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18556239659103599437803725 6958589872163849789176397)
                    ·
                      refine ⟨2609471202061443670941149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958589872163849789176397 2609471202061443670941149)
                      ·
                        rfl

theorem cell23_5081927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_5081927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081927 prefixEnd_5081927 := by exact prefixLift 5081927
  have htrace : WordTrace (prefixWord ++ tailWord_5081927) baseStart_5081927 baseEnd_5081927 := by
    simpa [prefixWord, tailWord_5081927, baseEnd_5081927] using wordTrace_append hprefix tailTrace_5081927
  have hstable : (prefixWord ++ tailWord_5081927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081927).length < 2 ^ (prefixWord ++ tailWord_5081927).sum := by decide
  have hdescent : baseEnd_5081927 < baseStart_5081927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081930 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_5081930 : Nat := 118140960795 + 5081930 * 2 ^ 59
def prefixEnd_5081930 : Nat := 4983230072969 + 3 ^ 40 * 5081930 * 2
def baseEnd_5081930 : Nat := 869824247501135719734545

theorem tailTrace_5081930 : CollatzResearch.WordTrace tailWord_5081930 prefixEnd_5081930 869824247501135719734545 := by
  unfold tailWord_5081930
  simp only [CollatzResearch.WordTrace]
  refine ⟨46338303619760752347526811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123568809652695339593404829 46338303619760752347526811)
  ·
    refine ⟨69507455429641128521290217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46338303619760752347526811 69507455429641128521290217)
    ·
      refine ⟨52130591572230846390967663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69507455429641128521290217 52130591572230846390967663)
      ·
        refine ⟨78195887358346269586451495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52130591572230846390967663 78195887358346269586451495)
        ·
          refine ⟨117293831037519404379677243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78195887358346269586451495 117293831037519404379677243)
          ·
            refine ⟨175940746556279106569515865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117293831037519404379677243 175940746556279106569515865)
            ·
              refine ⟨131955559917209329927136899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175940746556279106569515865 131955559917209329927136899)
              ·
                refine ⟨197933339875813994890705349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131955559917209329927136899 197933339875813994890705349)
                ·
                  refine ⟨37112501226715124042007253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197933339875813994890705349 37112501226715124042007253)
                  ·
                    refine ⟨869824247501135719734545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37112501226715124042007253 869824247501135719734545)
                    ·
                      rfl

theorem cell23_5081930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_5081930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081930 prefixEnd_5081930 := by exact prefixLift 5081930
  have htrace : WordTrace (prefixWord ++ tailWord_5081930) baseStart_5081930 baseEnd_5081930 := by
    simpa [prefixWord, tailWord_5081930, baseEnd_5081930] using wordTrace_append hprefix tailTrace_5081930
  have hstable : (prefixWord ++ tailWord_5081930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081930).length < 2 ^ (prefixWord ++ tailWord_5081930).sum := by decide
  have hdescent : baseEnd_5081930 < baseStart_5081930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081948 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5081948 : Nat := 118140960795 + 5081948 * 2 ^ 59
def prefixEnd_5081948 : Nat := 4983230072969 + 3 ^ 40 * 5081948 * 2
def baseEnd_5081948 : Nat := 2609481985155188088778553

theorem tailTrace_5081948 : CollatzResearch.WordTrace tailWord_5081948 prefixEnd_5081948 2609481985155188088778553 := by
  unfold tailWord_5081948
  simp only [CollatzResearch.WordTrace]
  refine ⟨92676935496488899232131249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123569247328651865642841665 92676935496488899232131249)
  ·
    refine ⟨69507701622366674424098437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92676935496488899232131249 69507701622366674424098437)
    ·
      refine ⟨13032694054193751454518457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69507701622366674424098437 13032694054193751454518457)
      ·
        refine ⟨9774520540645313590888843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13032694054193751454518457 9774520540645313590888843)
        ·
          refine ⟨14661780810967970386333265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774520540645313590888843 14661780810967970386333265)
          ·
            refine ⟨10996335608225977789749949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14661780810967970386333265 10996335608225977789749949)
            ·
              refine ⟨4123625853084741671156231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10996335608225977789749949 4123625853084741671156231)
              ·
                refine ⟨6185438779627112506734347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123625853084741671156231 6185438779627112506734347)
                ·
                  refine ⟨9278158169440668760101521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6185438779627112506734347 9278158169440668760101521)
                  ·
                    refine ⟨6958618627080501570076141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9278158169440668760101521 6958618627080501570076141)
                    ·
                      refine ⟨2609481985155188088778553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958618627080501570076141 2609481985155188088778553)
                      ·
                        rfl

theorem cell23_5081948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5081948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081948 prefixEnd_5081948 := by exact prefixLift 5081948
  have htrace : WordTrace (prefixWord ++ tailWord_5081948) baseStart_5081948 baseEnd_5081948 := by
    simpa [prefixWord, tailWord_5081948, baseEnd_5081948] using wordTrace_append hprefix tailTrace_5081948
  have hstable : (prefixWord ++ tailWord_5081948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081948).length < 2 ^ (prefixWord ++ tailWord_5081948).sum := by decide
  have hdescent : baseEnd_5081948 < baseStart_5081948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081977 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_5081977 : Nat := 118140960795 + 5081977 * 2 ^ 59
def prefixEnd_5081977 : Nat := 4983230072969 + 3 ^ 40 * 5081977 * 2
def baseEnd_5081977 : Nat := 869832292031389491771973

theorem tailTrace_5081977 : CollatzResearch.WordTrace tailWord_5081977 prefixEnd_5081977 869832292031389491771973 := by
  unfold tailWord_5081977
  simp only [CollatzResearch.WordTrace]
  refine ⟨185354928709872736417068185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123569952473248490944712123 185354928709872736417068185)
  ·
    refine ⟨139016196532404552312801139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185354928709872736417068185 139016196532404552312801139)
    ·
      refine ⟨208524294798606828469201709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139016196532404552312801139 208524294798606828469201709)
      ·
        refine ⟨78196610549477560675950641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208524294798606828469201709 78196610549477560675950641)
        ·
          refine ⟨58647457912108170506962981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78196610549477560675950641 58647457912108170506962981)
          ·
            refine ⟨10996398358520281970055559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58647457912108170506962981 10996398358520281970055559)
            ·
              refine ⟨16494597537780422955083339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996398358520281970055559 16494597537780422955083339)
              ·
                refine ⟨24741896306670634432625009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16494597537780422955083339 24741896306670634432625009)
                ·
                  refine ⟨18556422230002975824468757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24741896306670634432625009 18556422230002975824468757)
                  ·
                    refine ⟨869832292031389491771973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18556422230002975824468757 869832292031389491771973)
                    ·
                      rfl

theorem cell23_5081977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_5081977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081977 prefixEnd_5081977 := by exact prefixLift 5081977
  have htrace : WordTrace (prefixWord ++ tailWord_5081977) baseStart_5081977 baseEnd_5081977 := by
    simpa [prefixWord, tailWord_5081977, baseEnd_5081977] using wordTrace_append hprefix tailTrace_5081977
  have hstable : (prefixWord ++ tailWord_5081977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081977).length < 2 ^ (prefixWord ++ tailWord_5081977).sum := by decide
  have hdescent : baseEnd_5081977 < baseStart_5081977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5081987 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 3]
def baseStart_5081987 : Nat := 118140960795 + 5081987 * 2 ^ 59
def prefixEnd_5081987 : Nat := 4983230072969 + 3 ^ 40 * 5081987 * 2
def baseEnd_5081987 : Nat := 2609502010900713436190873

theorem tailTrace_5081987 : CollatzResearch.WordTrace tailWord_5081987 prefixEnd_5081987 2609502010900713436190873 := by
  unfold tailWord_5081987
  simp only [CollatzResearch.WordTrace]
  refine ⟨185355293439836508124932215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123570195626557672083288143 185355293439836508124932215)
  ·
    refine ⟨278032940159754762187398323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185355293439836508124932215 278032940159754762187398323)
    ·
      refine ⟨417049410239632143281097485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278032940159754762187398323 417049410239632143281097485)
      ·
        refine ⟨156393528839862053730411557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417049410239632143281097485 156393528839862053730411557)
        ·
          refine ⟨29323786657474135074452167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156393528839862053730411557 29323786657474135074452167)
          ·
            refine ⟨43985679986211202611678251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29323786657474135074452167 43985679986211202611678251)
            ·
              refine ⟨65978519979316803917517377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43985679986211202611678251 65978519979316803917517377)
              ·
                refine ⟨49483889984487602938138033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65978519979316803917517377 49483889984487602938138033)
                ·
                  refine ⟨37112917488365702203603525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49483889984487602938138033 37112917488365702203603525)
                  ·
                    refine ⟨6958672029068569163175661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37112917488365702203603525 6958672029068569163175661)
                    ·
                      refine ⟨2609502010900713436190873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958672029068569163175661 2609502010900713436190873)
                      ·
                        rfl

theorem cell23_5081987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_5081987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5081987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5081987 prefixEnd_5081987 := by exact prefixLift 5081987
  have htrace : WordTrace (prefixWord ++ tailWord_5081987) baseStart_5081987 baseEnd_5081987 := by
    simpa [prefixWord, tailWord_5081987, baseEnd_5081987] using wordTrace_append hprefix tailTrace_5081987
  have hstable : (prefixWord ++ tailWord_5081987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5081987).length < 2 ^ (prefixWord ++ tailWord_5081987).sum := by decide
  have hdescent : baseEnd_5081987 < baseStart_5081987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5081987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082018 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_5082018 : Nat := 118140960795 + 5082018 * 2 ^ 59
def prefixEnd_5082018 : Nat := 4983230072969 + 3 ^ 40 * 5082018 * 2
def baseEnd_5082018 : Nat := 2609517928801002814903231

theorem tailTrace_5082018 : CollatzResearch.WordTrace tailWord_5082018 prefixEnd_5082018 2609517928801002814903231 := by
  unfold tailWord_5082018
  simp only [CollatzResearch.WordTrace]
  refine ⟨46339106025681050104827677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123570949401816133612873805 46339106025681050104827677)
  ·
    refine ⟨17377164759630393789310379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46339106025681050104827677 17377164759630393789310379)
    ·
      refine ⟨26065747139445590683965569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17377164759630393789310379 26065747139445590683965569)
      ·
        refine ⟨19549310354584193012974177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26065747139445590683965569 19549310354584193012974177)
        ·
          refine ⟨14661982765938144759730633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19549310354584193012974177 14661982765938144759730633)
          ·
            refine ⟨10996487074453608569797975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14661982765938144759730633 10996487074453608569797975)
            ·
              refine ⟨16494730611680412854696963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996487074453608569797975 16494730611680412854696963)
              ·
                refine ⟨24742095917520619282045445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16494730611680412854696963 24742095917520619282045445)
                ·
                  refine ⟨4639142984535116115383521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24742095917520619282045445 4639142984535116115383521)
                  ·
                    refine ⟨3479357238401337086537641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4639142984535116115383521 3479357238401337086537641)
                    ·
                      refine ⟨2609517928801002814903231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479357238401337086537641 2609517928801002814903231)
                      ·
                        rfl

theorem cell23_5082018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_5082018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082018 prefixEnd_5082018 := by exact prefixLift 5082018
  have htrace : WordTrace (prefixWord ++ tailWord_5082018) baseStart_5082018 baseEnd_5082018 := by
    simpa [prefixWord, tailWord_5082018, baseEnd_5082018] using wordTrace_append hprefix tailTrace_5082018
  have hstable : (prefixWord ++ tailWord_5082018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082018).length < 2 ^ (prefixWord ++ tailWord_5082018).sum := by decide
  have hdescent : baseEnd_5082018 < baseStart_5082018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082037 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_5082037 : Nat := 118140960795 + 5082037 * 2 ^ 59
def prefixEnd_5082037 : Nat := 4983230072969 + 3 ^ 40 * 5082037 * 2
def baseEnd_5082037 : Nat := 869842561644479413521881

theorem tailTrace_5082037 : CollatzResearch.WordTrace tailWord_5082037 prefixEnd_5082037 869842561644479413521881 := by
  unfold tailWord_5082037
  simp only [CollatzResearch.WordTrace]
  refine ⟨185357117089655366664252365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123571411393103577776168243 185357117089655366664252365)
  ·
    refine ⟨69508918908620762499094637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185357117089655366664252365 69508918908620762499094637)
    ·
      refine ⟨26065844590732785937160489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69508918908620762499094637 26065844590732785937160489)
      ·
        refine ⟨19549383443049589452870367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26065844590732785937160489 19549383443049589452870367)
        ·
          refine ⟨29324075164574384179305551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19549383443049589452870367 29324075164574384179305551)
          ·
            refine ⟨43986112746861576268958327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29324075164574384179305551 43986112746861576268958327)
            ·
              refine ⟨65979169120292364403437491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43986112746861576268958327 65979169120292364403437491)
              ·
                refine ⟨98968753680438546605156237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65979169120292364403437491 98968753680438546605156237)
                ·
                  refine ⟨37113282630164454976933589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98968753680438546605156237 37113282630164454976933589)
                  ·
                    refine ⟨869842561644479413521881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37113282630164454976933589 869842561644479413521881)
                    ·
                      rfl

theorem cell23_5082037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_5082037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082037 prefixEnd_5082037 := by exact prefixLift 5082037
  have htrace : WordTrace (prefixWord ++ tailWord_5082037) baseStart_5082037 baseEnd_5082037 := by
    simpa [prefixWord, tailWord_5082037, baseEnd_5082037] using wordTrace_append hprefix tailTrace_5082037
  have hstable : (prefixWord ++ tailWord_5082037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082037).length < 2 ^ (prefixWord ++ tailWord_5082037).sum := by decide
  have hdescent : baseEnd_5082037 < baseStart_5082037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082074 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_5082074 : Nat := 118140960795 + 5082074 * 2 ^ 59
def prefixEnd_5082074 : Nat := 4983230072969 + 3 ^ 40 * 5082074 * 2
def baseEnd_5082074 : Nat := 2609546683717654595802973

theorem tailTrace_5082074 : CollatzResearch.WordTrace tailWord_5082074 prefixEnd_5082074 2609546683717654595802973 := by
  unfold tailWord_5082074
  simp only [CollatzResearch.WordTrace]
  refine ⟨46339616647630330495837319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123572311060347547988899517 46339616647630330495837319)
  ·
    refine ⟨69509424971445495743755979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46339616647630330495837319 69509424971445495743755979)
    ·
      refine ⟨104264137457168243615633969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69509424971445495743755979 104264137457168243615633969)
      ·
        refine ⟨78198103092876182711725477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104264137457168243615633969 78198103092876182711725477)
        ·
          refine ⟨14662144329914284258448527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78198103092876182711725477 14662144329914284258448527)
          ·
            refine ⟨21993216494871426387672791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14662144329914284258448527 21993216494871426387672791)
            ·
              refine ⟨32989824742307139581509187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21993216494871426387672791 32989824742307139581509187)
              ·
                refine ⟨49484737113460709372263781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32989824742307139581509187 49484737113460709372263781)
                ·
                  refine ⟨9278388208773883007299459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49484737113460709372263781 9278388208773883007299459)
                  ·
                    refine ⟨13917582313160824510949189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9278388208773883007299459 13917582313160824510949189)
                    ·
                      refine ⟨2609546683717654595802973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13917582313160824510949189 2609546683717654595802973)
                      ·
                        rfl

theorem cell23_5082074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_5082074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082074 prefixEnd_5082074 := by exact prefixLift 5082074
  have htrace : WordTrace (prefixWord ++ tailWord_5082074) baseStart_5082074 baseEnd_5082074 := by
    simpa [prefixWord, tailWord_5082074, baseEnd_5082074] using wordTrace_append hprefix tailTrace_5082074
  have hstable : (prefixWord ++ tailWord_5082074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082074).length < 2 ^ (prefixWord ++ tailWord_5082074).sum := by decide
  have hdescent : baseEnd_5082074 < baseStart_5082074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082084 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_5082084 : Nat := 118140960795 + 5082084 * 2 ^ 59
def prefixEnd_5082084 : Nat := 4983230072969 + 3 ^ 40 * 5082084 * 2
def baseEnd_5082084 : Nat := 869850606174733185559309

theorem tailTrace_5082084 : CollatzResearch.WordTrace tailWord_5082084 prefixEnd_5082084 869850606174733185559309 := by
  unfold tailWord_5082084
  simp only [CollatzResearch.WordTrace]
  refine ⟨92679415660242546845606653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123572554213656729127475537 92679415660242546845606653)
  ·
    refine ⟨34754780872590955067102495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92679415660242546845606653 34754780872590955067102495)
    ·
      refine ⟨52132171308886432600653743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34754780872590955067102495 52132171308886432600653743)
      ·
        refine ⟨78198256963329648900980615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52132171308886432600653743 78198256963329648900980615)
        ·
          refine ⟨117297385444994473351470923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78198256963329648900980615 117297385444994473351470923)
          ·
            refine ⟨175946078167491710027206385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117297385444994473351470923 175946078167491710027206385)
            ·
              refine ⟨131959558625618782520404789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175946078167491710027206385 131959558625618782520404789)
              ·
                refine ⟨12371208621151760861287949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131959558625618782520404789 12371208621151760861287949)
                ·
                  refine ⟨4639203232931910322982981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12371208621151760861287949 4639203232931910322982981)
                  ·
                    refine ⟨869850606174733185559309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639203232931910322982981 869850606174733185559309)
                    ·
                      rfl

theorem cell23_5082084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_5082084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082084 prefixEnd_5082084 := by exact prefixLift 5082084
  have htrace : WordTrace (prefixWord ++ tailWord_5082084) baseStart_5082084 baseEnd_5082084 := by
    simpa [prefixWord, tailWord_5082084, baseEnd_5082084] using wordTrace_append hprefix tailTrace_5082084
  have hstable : (prefixWord ++ tailWord_5082084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082084).length < 2 ^ (prefixWord ++ tailWord_5082084).sum := by decide
  have hdescent : baseEnd_5082084 < baseStart_5082084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082135 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 1, 4]
def baseStart_5082135 : Nat := 118140960795 + 5082135 * 2 ^ 59
def prefixEnd_5082135 : Nat := 4983230072969 + 3 ^ 40 * 5082135 * 2
def baseEnd_5082135 : Nat := 869859335345859619046731

theorem tailTrace_5082135 : CollatzResearch.WordTrace tailWord_5082135 prefixEnd_5082135 869859335345859619046731 := by
  unfold tailWord_5082135
  simp only [CollatzResearch.WordTrace]
  refine ⟨185360691443300329401319859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123573794295533552934213239 185360691443300329401319859)
  ·
    refine ⟨278041037164950494101979789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185360691443300329401319859 278041037164950494101979789)
    ·
      refine ⟨104265388936856435288242421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278041037164950494101979789 104265388936856435288242421)
      ·
        refine ⟨9774880212830290808272727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104265388936856435288242421 9774880212830290808272727)
        ·
          refine ⟨14662320319245436212409091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774880212830290808272727 14662320319245436212409091)
          ·
            refine ⟨21993480478868154318613637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14662320319245436212409091 21993480478868154318613637)
            ·
              refine ⟨4123777589787778934740057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21993480478868154318613637 4123777589787778934740057)
              ·
                refine ⟨3092833192340834201055043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4123777589787778934740057 3092833192340834201055043)
                ·
                  refine ⟨4639249788511251301582565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092833192340834201055043 4639249788511251301582565)
                  ·
                    refine ⟨869859335345859619046731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639249788511251301582565 869859335345859619046731)
                    ·
                      rfl

theorem cell23_5082135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_5082135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082135 prefixEnd_5082135 := by exact prefixLift 5082135
  have htrace : WordTrace (prefixWord ++ tailWord_5082135) baseStart_5082135 baseEnd_5082135 := by
    simpa [prefixWord, tailWord_5082135, baseEnd_5082135] using wordTrace_append hprefix tailTrace_5082135
  have hstable : (prefixWord ++ tailWord_5082135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082135).length < 2 ^ (prefixWord ++ tailWord_5082135).sum := by decide
  have hdescent : baseEnd_5082135 < baseStart_5082135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082158 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5082158 : Nat := 118140960795 + 5082158 * 2 ^ 59
def prefixEnd_5082158 : Nat := 4983230072969 + 3 ^ 40 * 5082158 * 2
def baseEnd_5082158 : Nat := 2609589816092632267152587

theorem tailTrace_5082158 : CollatzResearch.WordTrace tailWord_5082158 prefixEnd_5082158 2609589816092632267152587 := by
  unfold tailWord_5082158
  simp only [CollatzResearch.WordTrace]
  refine ⟨23170191290277125541175891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123574353548144669552938085 23170191290277125541175891)
  ·
    refine ⟨34755286935415688311763837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23170191290277125541175891 34755286935415688311763837)
    ·
      refine ⟨13033232600780883116911439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34755286935415688311763837 13033232600780883116911439)
      ·
        refine ⟨19549848901171324675367159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13033232600780883116911439 19549848901171324675367159)
        ·
          refine ⟨29324773351756987013050739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19549848901171324675367159 29324773351756987013050739)
          ·
            refine ⟨43987160027635480519576109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29324773351756987013050739 43987160027635480519576109)
            ·
              refine ⟨16495185010363305194841041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43987160027635480519576109 16495185010363305194841041)
              ·
                refine ⟨12371388757772478896130781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16495185010363305194841041 12371388757772478896130781)
                ·
                  refine ⟨4639270784164679586049043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12371388757772478896130781 4639270784164679586049043)
                  ·
                    refine ⟨6958906176247019379073565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4639270784164679586049043 6958906176247019379073565)
                    ·
                      refine ⟨2609589816092632267152587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958906176247019379073565 2609589816092632267152587)
                      ·
                        rfl

theorem cell23_5082158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5082158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082158 prefixEnd_5082158 := by exact prefixLift 5082158
  have htrace : WordTrace (prefixWord ++ tailWord_5082158) baseStart_5082158 baseEnd_5082158 := by
    simpa [prefixWord, tailWord_5082158, baseEnd_5082158] using wordTrace_append hprefix tailTrace_5082158
  have hstable : (prefixWord ++ tailWord_5082158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082158).length < 2 ^ (prefixWord ++ tailWord_5082158).sum := by decide
  have hdescent : baseEnd_5082158 < baseStart_5082158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082168 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 2, 3, 2]
def baseStart_5082168 : Nat := 118140960795 + 5082168 * 2 ^ 59
def prefixEnd_5082168 : Nat := 4983230072969 + 3 ^ 40 * 5082168 * 2
def baseEnd_5082168 : Nat := 2609594950899177228027541

theorem tailTrace_5082168 : CollatzResearch.WordTrace tailWord_5082168 prefixEnd_5082168 2609594950899177228027541 := by
  unfold tailWord_5082168
  simp only [CollatzResearch.WordTrace]
  refine ⟨92680947526090388018635579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123574596701453850691514105 92680947526090388018635579)
  ·
    refine ⟨139021421289135582027953369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92680947526090388018635579 139021421289135582027953369)
    ·
      refine ⟨104266065966851686520965027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139021421289135582027953369 104266065966851686520965027)
      ·
        refine ⟨156399098950277529781447541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104266065966851686520965027 156399098950277529781447541)
        ·
          refine ⟨14662415526588518417010707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156399098950277529781447541 14662415526588518417010707)
          ·
            refine ⟨21993623289882777625516061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14662415526588518417010707 21993623289882777625516061)
            ·
              refine ⟨8247608733706041609568523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21993623289882777625516061 8247608733706041609568523)
              ·
                refine ⟨12371413100559062414352785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247608733706041609568523 12371413100559062414352785)
                ·
                  refine ⟨9278559825419296810764589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12371413100559062414352785 9278559825419296810764589)
                  ·
                    refine ⟨3479459934532236304036721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9278559825419296810764589 3479459934532236304036721)
                    ·
                      refine ⟨2609594950899177228027541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479459934532236304036721 2609594950899177228027541)
                      ·
                        rfl

theorem cell23_5082168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_5082168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082168 prefixEnd_5082168 := by exact prefixLift 5082168
  have htrace : WordTrace (prefixWord ++ tailWord_5082168) baseStart_5082168 baseEnd_5082168 := by
    simpa [prefixWord, tailWord_5082168, baseEnd_5082168] using wordTrace_append hprefix tailTrace_5082168
  have hstable : (prefixWord ++ tailWord_5082168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082168).length < 2 ^ (prefixWord ++ tailWord_5082168).sum := by decide
  have hdescent : baseEnd_5082168 < baseStart_5082168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082184 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_5082184 : Nat := 118140960795 + 5082184 * 2 ^ 59
def prefixEnd_5082184 : Nat := 4983230072969 + 3 ^ 40 * 5082184 * 2
def baseEnd_5082184 : Nat := 2609603166589649165427467

theorem tailTrace_5082184 : CollatzResearch.WordTrace tailWord_5082184 prefixEnd_5082184 2609603166589649165427467 := by
  unfold tailWord_5082184
  simp only [CollatzResearch.WordTrace]
  refine ⟨92681239310061405384926803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123574985746748540513235737 92681239310061405384926803)
  ·
    refine ⟨139021858965092108077390205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92681239310061405384926803 139021858965092108077390205)
    ·
      refine ⟨52133197111909540529021327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139021858965092108077390205 52133197111909540529021327)
      ·
        refine ⟨78199795667864310793531991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52133197111909540529021327 78199795667864310793531991)
        ·
          refine ⟨117299693501796466190297987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78199795667864310793531991 117299693501796466190297987)
          ·
            refine ⟨175949540252694699285446981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117299693501796466190297987 175949540252694699285446981)
            ·
              refine ⟨32990538797380256116021309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175949540252694699285446981 32990538797380256116021309)
              ·
                refine ⟨12371452049017596043507991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32990538797380256116021309 12371452049017596043507991)
                ·
                  refine ⟨18557178073526394065261987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12371452049017596043507991 18557178073526394065261987)
                  ·
                    refine ⟨27835767110289591097892981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18557178073526394065261987 27835767110289591097892981)
                    ·
                      refine ⟨2609603166589649165427467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27835767110289591097892981 2609603166589649165427467)
                      ·
                        rfl

theorem cell23_5082184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_5082184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082184 prefixEnd_5082184 := by exact prefixLift 5082184
  have htrace : WordTrace (prefixWord ++ tailWord_5082184) baseStart_5082184 baseEnd_5082184 := by
    simpa [prefixWord, tailWord_5082184, baseEnd_5082184] using wordTrace_append hprefix tailTrace_5082184
  have hstable : (prefixWord ++ tailWord_5082184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082184).length < 2 ^ (prefixWord ++ tailWord_5082184).sum := by decide
  have hdescent : baseEnd_5082184 < baseStart_5082184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082204 : List Nat := [2, 2, 4, 1, 1, 1, 2, 10]
def baseStart_5082204 : Nat := 118140960795 + 5082204 * 2 ^ 59
def prefixEnd_5082204 : Nat := 4983230072969 + 3 ^ 40 * 5082204 * 2
def baseEnd_5082204 : Nat := 96652349488990336562125

theorem tailTrace_5082204 : CollatzResearch.WordTrace tailWord_5082204 prefixEnd_5082204 96652349488990336562125 := by
  unfold tailWord_5082204
  simp only [CollatzResearch.WordTrace]
  refine ⟨92681604040025177092790833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123575472053366902790387777 92681604040025177092790833)
  ·
    refine ⟨69511203030018882819593125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92681604040025177092790833 69511203030018882819593125)
    ·
      refine ⟨13033350568128540528673711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69511203030018882819593125 13033350568128540528673711)
      ·
        refine ⟨19550025852192810793010567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13033350568128540528673711 19550025852192810793010567)
        ·
          refine ⟨29325038778289216189515851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19550025852192810793010567 29325038778289216189515851)
          ·
            refine ⟨43987558167433824284273777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29325038778289216189515851 43987558167433824284273777)
            ·
              refine ⟨32990668625575368213205333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43987558167433824284273777 32990668625575368213205333)
              ·
                refine ⟨96652349488990336562125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32990668625575368213205333 96652349488990336562125)
                ·
                  rfl

theorem cell23_5082204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 10].length) (baseStart_5082204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082204 prefixEnd_5082204 := by exact prefixLift 5082204
  have htrace : WordTrace (prefixWord ++ tailWord_5082204) baseStart_5082204 baseEnd_5082204 := by
    simpa [prefixWord, tailWord_5082204, baseEnd_5082204] using wordTrace_append hprefix tailTrace_5082204
  have hstable : (prefixWord ++ tailWord_5082204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082204).length < 2 ^ (prefixWord ++ tailWord_5082204).sum := by decide
  have hdescent : baseEnd_5082204 < baseStart_5082204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082208 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 2, 4]
def baseStart_5082208 : Nat := 118140960795 + 5082208 * 2 ^ 59
def prefixEnd_5082208 : Nat := 4983230072969 + 3 ^ 40 * 5082208 * 2
def baseEnd_5082208 : Nat := 869871830041785690509119

theorem tailTrace_5082208 : CollatzResearch.WordTrace tailWord_5082208 prefixEnd_5082208 869871830041785690509119 := by
  unfold tailWord_5082208
  simp only [CollatzResearch.WordTrace]
  refine ⟨92681676986017931434363639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123575569314690575245818185 92681676986017931434363639)
  ·
    refine ⟨139022515479026897151545459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92681676986017931434363639 139022515479026897151545459)
    ·
      refine ⟨208533773218540345727318189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139022515479026897151545459 208533773218540345727318189)
      ·
        refine ⟨78200164956952629647744321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208533773218540345727318189 78200164956952629647744321)
        ·
          refine ⟨58650123717714472235808241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78200164956952629647744321 58650123717714472235808241)
          ·
            refine ⟨43987592788285854176856181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58650123717714472235808241 43987592788285854176856181)
            ·
              refine ⟨4123836823901798829080267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43987592788285854176856181 4123836823901798829080267)
              ·
                refine ⟨6185755235852698243620401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123836823901798829080267 6185755235852698243620401)
                ·
                  refine ⟨4639316426889523682715301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6185755235852698243620401 4639316426889523682715301)
                  ·
                    refine ⟨869871830041785690509119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639316426889523682715301 869871830041785690509119)
                    ·
                      rfl

theorem cell23_5082208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 4].length) (baseStart_5082208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082208 prefixEnd_5082208 := by exact prefixLift 5082208
  have htrace : WordTrace (prefixWord ++ tailWord_5082208) baseStart_5082208 baseEnd_5082208 := by
    simpa [prefixWord, tailWord_5082208, baseEnd_5082208] using wordTrace_append hprefix tailTrace_5082208
  have hstable : (prefixWord ++ tailWord_5082208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082208).length < 2 ^ (prefixWord ++ tailWord_5082208).sum := by decide
  have hdescent : baseEnd_5082208 < baseStart_5082208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082218 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_5082218 : Nat := 118140960795 + 5082218 * 2 ^ 59
def prefixEnd_5082218 : Nat := 4983230072969 + 3 ^ 40 * 5082218 * 2
def baseEnd_5082218 : Nat := 2609620624931902032402311

theorem tailTrace_5082218 : CollatzResearch.WordTrace tailWord_5082218 prefixEnd_5082218 2609620624931902032402311 := by
  unfold tailWord_5082218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46340929675499908644147827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123575812467999756384394205 46340929675499908644147827)
  ·
    refine ⟨69511394513249862966221741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46340929675499908644147827 69511394513249862966221741)
    ·
      refine ⟨26066772942468698612333153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69511394513249862966221741 26066772942468698612333153)
      ·
        refine ⟨19550079706851523959249865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26066772942468698612333153 19550079706851523959249865)
        ·
          refine ⟨14662559780138642969437399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19550079706851523959249865 14662559780138642969437399)
          ·
            refine ⟨21993839670207964454156099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14662559780138642969437399 21993839670207964454156099)
            ·
              refine ⟨32990759505311946681234149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21993839670207964454156099 32990759505311946681234149)
              ·
                refine ⟨6185767407245990002731403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32990759505311946681234149 6185767407245990002731403)
                ·
                  refine ⟨9278651110868985004097105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6185767407245990002731403 9278651110868985004097105)
                  ·
                    refine ⟨6958988333151738753072829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9278651110868985004097105 6958988333151738753072829)
                    ·
                      refine ⟨2609620624931902032402311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6958988333151738753072829 2609620624931902032402311)
                      ·
                        rfl

theorem cell23_5082218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_5082218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082218 prefixEnd_5082218 := by exact prefixLift 5082218
  have htrace : WordTrace (prefixWord ++ tailWord_5082218) baseStart_5082218 baseEnd_5082218 := by
    simpa [prefixWord, tailWord_5082218, baseEnd_5082218] using wordTrace_append hprefix tailTrace_5082218
  have hstable : (prefixWord ++ tailWord_5082218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082218).length < 2 ^ (prefixWord ++ tailWord_5082218).sum := by decide
  have hdescent : baseEnd_5082218 < baseStart_5082218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082221 : List Nat := [1, 5, 1, 1, 2, 2, 4, 7]
def baseStart_5082221 : Nat := 118140960795 + 5082221 * 2 ^ 59
def prefixEnd_5082221 : Nat := 4983230072969 + 3 ^ 40 * 5082221 * 2
def baseEnd_5082221 : Nat := 96652672791624648913511

theorem tailTrace_5082221 : CollatzResearch.WordTrace tailWord_5082221 prefixEnd_5082221 96652672791624648913511 := by
  unfold tailWord_5082221
  simp only [CollatzResearch.WordTrace]
  refine ⟨185363828120988766088950517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123575885413992510725967011 185363828120988766088950517)
  ·
    refine ⟨17377858886342696820839111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185363828120988766088950517 17377858886342696820839111)
    ·
      refine ⟨26066788329514045231258667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17377858886342696820839111 26066788329514045231258667)
      ·
        refine ⟨39100182494271067846888001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26066788329514045231258667 39100182494271067846888001)
        ·
          refine ⟨29325136870703300885166001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39100182494271067846888001 29325136870703300885166001)
          ·
            refine ⟨21993852653027475663874501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29325136870703300885166001 21993852653027475663874501)
            ·
              refine ⟨4123847372442651686976469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21993852653027475663874501 4123847372442651686976469)
              ·
                refine ⟨96652672791624648913511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4123847372442651686976469 96652672791624648913511)
                ·
                  rfl

theorem cell23_5082221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 7].length) (baseStart_5082221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082221 prefixEnd_5082221 := by exact prefixLift 5082221
  have htrace : WordTrace (prefixWord ++ tailWord_5082221) baseStart_5082221 baseEnd_5082221 := by
    simpa [prefixWord, tailWord_5082221, baseEnd_5082221] using wordTrace_append hprefix tailTrace_5082221
  have hstable : (prefixWord ++ tailWord_5082221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082221).length < 2 ^ (prefixWord ++ tailWord_5082221).sum := by decide
  have hdescent : baseEnd_5082221 < baseStart_5082221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082231 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_5082231 : Nat := 118140960795 + 5082231 * 2 ^ 59
def prefixEnd_5082231 : Nat := 4983230072969 + 3 ^ 40 * 5082231 * 2
def baseEnd_5082231 : Nat := 2609627300180410481539751

theorem tailTrace_5082231 : CollatzResearch.WordTrace tailWord_5082231 prefixEnd_5082231 2609627300180410481539751 := by
  unfold tailWord_5082231
  simp only [CollatzResearch.WordTrace]
  refine ⟨185364192850952537796814547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123576128567301691864543031 185364192850952537796814547)
  ·
    refine ⟨278046289276428806695221821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185364192850952537796814547 278046289276428806695221821)
    ·
      refine ⟨104267358478660802510708183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278046289276428806695221821 104267358478660802510708183)
      ·
        refine ⟨156401037717991203766062275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104267358478660802510708183 156401037717991203766062275)
        ·
          refine ⟨234601556576986805649093413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156401037717991203766062275 234601556576986805649093413)
          ·
            refine ⟨43987791858185026059205015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234601556576986805649093413 43987791858185026059205015)
            ·
              refine ⟨65981687787277539088807523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43987791858185026059205015 65981687787277539088807523)
              ·
                refine ⟨98972531680916308633211285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65981687787277539088807523 98972531680916308633211285)
                ·
                  refine ⟨4639337422542951967181779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98972531680916308633211285 4639337422542951967181779)
                  ·
                    refine ⟨6959006133814427950772669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4639337422542951967181779 6959006133814427950772669)
                    ·
                      refine ⟨2609627300180410481539751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6959006133814427950772669 2609627300180410481539751)
                      ·
                        rfl

theorem cell23_5082231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_5082231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082231 prefixEnd_5082231 := by exact prefixLift 5082231
  have htrace : WordTrace (prefixWord ++ tailWord_5082231) baseStart_5082231 baseEnd_5082231 := by
    simpa [prefixWord, tailWord_5082231, baseEnd_5082231] using wordTrace_append hprefix tailTrace_5082231
  have hstable : (prefixWord ++ tailWord_5082231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082231).length < 2 ^ (prefixWord ++ tailWord_5082231).sum := by decide
  have hdescent : baseEnd_5082231 < baseStart_5082231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082284 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_5082284 : Nat := 118140960795 + 5082284 * 2 ^ 59
def prefixEnd_5082284 : Nat := 4983230072969 + 3 ^ 40 * 5082284 * 2
def baseEnd_5082284 : Nat := 2609654514655098774177007

theorem tailTrace_5082284 : CollatzResearch.WordTrace tailWord_5082284 prefixEnd_5082284 2609654514655098774177007 := by
  unfold tailWord_5082284
  simp only [CollatzResearch.WordTrace]
  refine ⟨92683062959880263924246953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123577417279840351898995937 92683062959880263924246953)
  ·
    refine ⟨69512297219910197943185215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92683062959880263924246953 69512297219910197943185215)
    ·
      refine ⟨104268445829865296914777823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69512297219910197943185215 104268445829865296914777823)
      ·
        refine ⟨156402668744797945372166735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104268445829865296914777823 156402668744797945372166735)
        ·
          refine ⟨234604003117196918058250103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156402668744797945372166735 234604003117196918058250103)
          ·
            refine ⟨351906004675795377087375155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234604003117196918058250103 351906004675795377087375155)
            ·
              refine ⟨527859007013693065631062733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351906004675795377087375155 527859007013693065631062733)
              ·
                refine ⟨197947127630134899611648525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 527859007013693065631062733 197947127630134899611648525)
                ·
                  refine ⟨74230172861300587354368197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197947127630134899611648525 74230172861300587354368197)
                  ·
                    refine ⟨13918157411493860128944037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74230172861300587354368197 13918157411493860128944037)
                    ·
                      refine ⟨2609654514655098774177007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13918157411493860128944037 2609654514655098774177007)
                      ·
                        rfl

theorem cell23_5082284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_5082284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082284 prefixEnd_5082284 := by exact prefixLift 5082284
  have htrace : WordTrace (prefixWord ++ tailWord_5082284) baseStart_5082284 baseEnd_5082284 := by
    simpa [prefixWord, tailWord_5082284, baseEnd_5082284] using wordTrace_append hprefix tailTrace_5082284
  have hstable : (prefixWord ++ tailWord_5082284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082284).length < 2 ^ (prefixWord ++ tailWord_5082284).sum := by decide
  have hdescent : baseEnd_5082284 < baseStart_5082284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082318 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_5082318 : Nat := 118140960795 + 5082318 * 2 ^ 59
def prefixEnd_5082318 : Nat := 4983230072969 + 3 ^ 40 * 5082318 * 2
def baseEnd_5082318 : Nat := 2609671972997351641151851

theorem tailTrace_5082318 : CollatzResearch.WordTrace tailWord_5082318 prefixEnd_5082318 2609671972997351641151851 := by
  unfold tailWord_5082318
  simp only [CollatzResearch.WordTrace]
  refine ⟨23170920750204668956903951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123578244001091567770154405 23170920750204668956903951)
  ·
    refine ⟨34756381125307003435355927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23170920750204668956903951 34756381125307003435355927)
    ·
      refine ⟨52134571687960505153033891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34756381125307003435355927 52134571687960505153033891)
      ·
        refine ⟨78201857531940757729550837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52134571687960505153033891 78201857531940757729550837)
        ·
          refine ⟨7331424143619446037145391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78201857531940757729550837 7331424143619446037145391)
          ·
            refine ⟨10997136215429169055718087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331424143619446037145391 10997136215429169055718087)
            ·
              refine ⟨16495704323143753583577131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10997136215429169055718087 16495704323143753583577131)
              ·
                refine ⟨24743556484715630375365697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16495704323143753583577131 24743556484715630375365697)
                ·
                  refine ⟨18557667363536722781524273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24743556484715630375365697 18557667363536722781524273)
                  ·
                    refine ⟨13918250522652542086143205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18557667363536722781524273 13918250522652542086143205)
                    ·
                      refine ⟨2609671972997351641151851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13918250522652542086143205 2609671972997351641151851)
                      ·
                        rfl

theorem cell23_5082318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_5082318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082318 prefixEnd_5082318 := by exact prefixLift 5082318
  have htrace : WordTrace (prefixWord ++ tailWord_5082318) baseStart_5082318 baseEnd_5082318 := by
    simpa [prefixWord, tailWord_5082318, baseEnd_5082318] using wordTrace_append hprefix tailTrace_5082318
  have hstable : (prefixWord ++ tailWord_5082318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082318).length < 2 ^ (prefixWord ++ tailWord_5082318).sum := by decide
  have hdescent : baseEnd_5082318 < baseStart_5082318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082331 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 7, 2]
def baseStart_5082331 : Nat := 118140960795 + 5082331 * 2 ^ 59
def prefixEnd_5082331 : Nat := 4983230072969 + 3 ^ 40 * 5082331 * 2
def baseEnd_5082331 : Nat := 2609678648245860090289291

theorem tailTrace_5082331 : CollatzResearch.WordTrace tailWord_5082331 prefixEnd_5082331 2609678648245860090289291 := by
  unfold tailWord_5082331
  simp only [CollatzResearch.WordTrace]
  refine ⟨185367840150590254875454847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123578560100393503250303231 185367840150590254875454847)
  ·
    refine ⟨278051760225885382313182271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185367840150590254875454847 278051760225885382313182271)
    ·
      refine ⟨417077640338828073469773407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278051760225885382313182271 417077640338828073469773407)
      ·
        refine ⟨625616460508242110204660111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417077640338828073469773407 625616460508242110204660111)
        ·
          refine ⟨938424690762363165306990167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625616460508242110204660111 938424690762363165306990167)
          ·
            refine ⟨1407637036143544747960485251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938424690762363165306990167 1407637036143544747960485251)
            ·
              refine ⟨2111455554215317121940727877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407637036143544747960485251 2111455554215317121940727877)
              ·
                refine ⟨395897916415371960363886477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2111455554215317121940727877 395897916415371960363886477)
                ·
                  refine ⟨148461718655764485136457429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395897916415371960363886477 148461718655764485136457429)
                  ·
                    refine ⟨3479571530994480120385721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148461718655764485136457429 3479571530994480120385721)
                    ·
                      refine ⟨2609678648245860090289291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479571530994480120385721 2609678648245860090289291)
                      ·
                        rfl

theorem cell23_5082331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7, 2].length) (baseStart_5082331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082331 prefixEnd_5082331 := by exact prefixLift 5082331
  have htrace : WordTrace (prefixWord ++ tailWord_5082331) baseStart_5082331 baseEnd_5082331 := by
    simpa [prefixWord, tailWord_5082331, baseEnd_5082331] using wordTrace_append hprefix tailTrace_5082331
  have hstable : (prefixWord ++ tailWord_5082331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082331).length < 2 ^ (prefixWord ++ tailWord_5082331).sum := by decide
  have hdescent : baseEnd_5082331 < baseStart_5082331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082356 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5082356 : Nat := 118140960795 + 5082356 * 2 ^ 59
def prefixEnd_5082356 : Nat := 4983230072969 + 3 ^ 40 * 5082356 * 2
def baseEnd_5082356 : Nat := 2609691485262222492476677

theorem tailTrace_5082356 : CollatzResearch.WordTrace tailWord_5082356 prefixEnd_5082356 2609691485262222492476677 := by
  unfold tailWord_5082356
  simp only [CollatzResearch.WordTrace]
  refine ⟨92684375987749842072557461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123579167983666456096743281 92684375987749842072557461)
  ·
    refine ⟨4344580124425773847151131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92684375987749842072557461 4344580124425773847151131)
    ·
      refine ⟨6516870186638660770726697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344580124425773847151131 6516870186638660770726697)
      ·
        refine ⟨4887652639978995578045023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6516870186638660770726697 4887652639978995578045023)
        ·
          refine ⟨7331478959968493367067535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887652639978995578045023 7331478959968493367067535)
          ·
            refine ⟨10997218439952740050601303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331478959968493367067535 10997218439952740050601303)
            ·
              refine ⟨16495827659929110075901955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10997218439952740050601303 16495827659929110075901955)
              ·
                refine ⟨24743741489893665113852933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16495827659929110075901955 24743741489893665113852933)
                ·
                  refine ⟨4639451529355062208847425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24743741489893665113852933 4639451529355062208847425)
                  ·
                    refine ⟨3479588647016296656635569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4639451529355062208847425 3479588647016296656635569)
                    ·
                      refine ⟨2609691485262222492476677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479588647016296656635569 2609691485262222492476677)
                      ·
                        rfl

theorem cell23_5082356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5082356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082356 prefixEnd_5082356 := by exact prefixLift 5082356
  have htrace : WordTrace (prefixWord ++ tailWord_5082356) baseStart_5082356 baseEnd_5082356 := by
    simpa [prefixWord, tailWord_5082356, baseEnd_5082356] using wordTrace_append hprefix tailTrace_5082356
  have hstable : (prefixWord ++ tailWord_5082356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082356).length < 2 ^ (prefixWord ++ tailWord_5082356).sum := by decide
  have hdescent : baseEnd_5082356 < baseStart_5082356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082361 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_5082361 : Nat := 118140960795 + 5082361 * 2 ^ 59
def prefixEnd_5082361 : Nat := 4983230072969 + 3 ^ 40 * 5082361 * 2
def baseEnd_5082361 : Nat := 2609694052665494972914153

theorem tailTrace_5082361 : CollatzResearch.WordTrace tailWord_5082361 prefixEnd_5082361 2609694052665494972914153 := by
  unfold tailWord_5082361
  simp only [CollatzResearch.WordTrace]
  refine ⟨185368934340481569999046937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123579289560321046666031291 185368934340481569999046937)
  ·
    refine ⟨139026700755361177499285203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185368934340481569999046937 139026700755361177499285203)
    ·
      refine ⟨208540051133041766248927805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139026700755361177499285203 208540051133041766248927805)
      ·
        refine ⟨78202519174890662343347927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208540051133041766248927805 78202519174890662343347927)
        ·
          refine ⟨117303778762335993515021891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78202519174890662343347927 117303778762335993515021891)
          ·
            refine ⟨175955668143503990272532837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117303778762335993515021891 175955668143503990272532837)
            ·
              refine ⟨32991687776906998176099907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175955668143503990272532837 32991687776906998176099907)
              ·
                refine ⟨49487531665360497264149861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32991687776906998176099907 49487531665360497264149861)
                ·
                  refine ⟨9278912187255093237028099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49487531665360497264149861 9278912187255093237028099)
                  ·
                    refine ⟨13918368280882639855542149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9278912187255093237028099 13918368280882639855542149)
                    ·
                      refine ⟨2609694052665494972914153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13918368280882639855542149 2609694052665494972914153)
                      ·
                        rfl

theorem cell23_5082361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_5082361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082361 prefixEnd_5082361 := by exact prefixLift 5082361
  have htrace : WordTrace (prefixWord ++ tailWord_5082361) baseStart_5082361 baseEnd_5082361 := by
    simpa [prefixWord, tailWord_5082361, baseEnd_5082361] using wordTrace_append hprefix tailTrace_5082361
  have hstable : (prefixWord ++ tailWord_5082361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082361).length < 2 ^ (prefixWord ++ tailWord_5082361).sum := by decide
  have hdescent : baseEnd_5082361 < baseStart_5082361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082391 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5082391 : Nat := 118140960795 + 5082391 * 2 ^ 59
def prefixEnd_5082391 : Nat := 4983230072969 + 3 ^ 40 * 5082391 * 2
def baseEnd_5082391 : Nat := 2609709457085129855539015

theorem tailTrace_5082391 : CollatzResearch.WordTrace tailWord_5082391 prefixEnd_5082391 2609709457085129855539015 := by
  unfold tailWord_5082391
  simp only [CollatzResearch.WordTrace]
  refine ⟨185370028530372885122639027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123580019020248590081759351 185370028530372885122639027)
  ·
    refine ⟨278055042795559327683958541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185370028530372885122639027 278055042795559327683958541)
    ·
      refine ⟨104270641048334747881484453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278055042795559327683958541 104270641048334747881484453)
      ·
        refine ⟨19550745196562765227778335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104270641048334747881484453 19550745196562765227778335)
        ·
          refine ⟨29326117794844147841667503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19550745196562765227778335 29326117794844147841667503)
          ·
            refine ⟨43989176692266221762501255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29326117794844147841667503 43989176692266221762501255)
            ·
              refine ⟨65983765038399332643751883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43989176692266221762501255 65983765038399332643751883)
              ·
                refine ⟨98975647557598998965627825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65983765038399332643751883 98975647557598998965627825)
                ·
                  refine ⟨74231735668199249224220869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98975647557598998965627825 74231735668199249224220869)
                  ·
                    refine ⟨13918450437787359229541413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74231735668199249224220869 13918450437787359229541413)
                    ·
                      refine ⟨2609709457085129855539015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13918450437787359229541413 2609709457085129855539015)
                      ·
                        rfl

theorem cell23_5082391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5082391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082391 prefixEnd_5082391 := by exact prefixLift 5082391
  have htrace : WordTrace (prefixWord ++ tailWord_5082391) baseStart_5082391 baseEnd_5082391 := by
    simpa [prefixWord, tailWord_5082391, baseEnd_5082391] using wordTrace_append hprefix tailTrace_5082391
  have hstable : (prefixWord ++ tailWord_5082391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082391).length < 2 ^ (prefixWord ++ tailWord_5082391).sum := by decide
  have hdescent : baseEnd_5082391 < baseStart_5082391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082455 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 2, 3, 2]
def baseStart_5082455 : Nat := 118140960795 + 5082455 * 2 ^ 59
def prefixEnd_5082455 : Nat := 4983230072969 + 3 ^ 40 * 5082455 * 2
def baseEnd_5082455 : Nat := 2609742319847017605138721

theorem tailTrace_5082455 : CollatzResearch.WordTrace tailWord_5082455 prefixEnd_5082455 2609742319847017605138721 := by
  unfold tailWord_5082455
  simp only [CollatzResearch.WordTrace]
  refine ⟨185372362802141024052968819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123581575201427349368645879 185372362802141024052968819)
  ·
    refine ⟨278058544203211536079453229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185372362802141024052968819 278058544203211536079453229)
    ·
      refine ⟨104271954076204326029794961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278058544203211536079453229 104271954076204326029794961)
      ·
        refine ⟨78203965557153244522346221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104271954076204326029794961 78203965557153244522346221)
        ·
          refine ⟨29326487083932466695879833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78203965557153244522346221 29326487083932466695879833)
          ·
            refine ⟨21994865312949350021909875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29326487083932466695879833 21994865312949350021909875)
            ·
              refine ⟨32992297969424025032864813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21994865312949350021909875 32992297969424025032864813)
              ·
                refine ⟨12372111738534009387324305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32992297969424025032864813 12372111738534009387324305)
                ·
                  refine ⟨9279083803900507040493229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12372111738534009387324305 9279083803900507040493229)
                  ·
                    refine ⟨3479656426462690140184961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9279083803900507040493229 3479656426462690140184961)
                    ·
                      refine ⟨2609742319847017605138721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479656426462690140184961 2609742319847017605138721)
                      ·
                        rfl

theorem cell23_5082455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_5082455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082455 prefixEnd_5082455 := by exact prefixLift 5082455
  have htrace : WordTrace (prefixWord ++ tailWord_5082455) baseStart_5082455 baseEnd_5082455 := by
    simpa [prefixWord, tailWord_5082455, baseEnd_5082455] using wordTrace_append hprefix tailTrace_5082455
  have hstable : (prefixWord ++ tailWord_5082455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082455).length < 2 ^ (prefixWord ++ tailWord_5082455).sum := by decide
  have hdescent : baseEnd_5082455 < baseStart_5082455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082481 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_5082481 : Nat := 118140960795 + 5082481 * 2 ^ 59
def prefixEnd_5082481 : Nat := 4983230072969 + 3 ^ 40 * 5082481 * 2
def baseEnd_5082481 : Nat := 2609755670344034503413601

theorem tailTrace_5082481 : CollatzResearch.WordTrace tailWord_5082481 prefixEnd_5082481 2609755670344034503413601 := by
  unfold tailWord_5082481
  simp only [CollatzResearch.WordTrace]
  refine ⟨185373311100046830493415297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123582207400031220328943531 185373311100046830493415297)
  ·
    refine ⟨139029983325035122870061473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185373311100046830493415297 139029983325035122870061473)
    ·
      refine ⟨104272487493776342152546105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139029983325035122870061473 104272487493776342152546105)
      ·
        refine ⟨78204365620332256614409579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104272487493776342152546105 78204365620332256614409579)
        ·
          refine ⟨117306548430498384921614369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78204365620332256614409579 117306548430498384921614369)
          ·
            refine ⟨87979911322873788691210777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117306548430498384921614369 87979911322873788691210777)
            ·
              refine ⟨65984933492155341518408083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87979911322873788691210777 65984933492155341518408083)
              ·
                refine ⟨98977400238233012277612125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65984933492155341518408083 98977400238233012277612125)
                ·
                  refine ⟨37116525089337379604104547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98977400238233012277612125 37116525089337379604104547)
                  ·
                    refine ⟨55674787634006069406156821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37116525089337379604104547 55674787634006069406156821)
                    ·
                      refine ⟨2609755670344034503413601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55674787634006069406156821 2609755670344034503413601)
                      ·
                        rfl

theorem cell23_5082481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_5082481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082481 prefixEnd_5082481 := by exact prefixLift 5082481
  have htrace : WordTrace (prefixWord ++ tailWord_5082481) baseStart_5082481 baseEnd_5082481 := by
    simpa [prefixWord, tailWord_5082481, baseEnd_5082481] using wordTrace_append hprefix tailTrace_5082481
  have hstable : (prefixWord ++ tailWord_5082481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082481).length < 2 ^ (prefixWord ++ tailWord_5082481).sum := by decide
  have hdescent : baseEnd_5082481 < baseStart_5082481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082508 : List Nat := [2, 2, 1, 2, 1, 3, 5, 7]
def baseStart_5082508 : Nat := 118140960795 + 5082508 * 2 ^ 59
def prefixEnd_5082508 : Nat := 4983230072969 + 3 ^ 40 * 5082508 * 2
def baseEnd_5082508 : Nat := 96658130900803922139851

theorem tailTrace_5082508 : CollatzResearch.WordTrace tailWord_5082508 prefixEnd_5082508 96658130900803922139851 := by
  unfold tailWord_5082508
  simp only [CollatzResearch.WordTrace]
  refine ⟨92687147935474507052324089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123582863913966009403098785 92687147935474507052324089)
  ·
    refine ⟨69515360951605880289243067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92687147935474507052324089 69515360951605880289243067)
    ·
      refine ⟨104273041427408820433864601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69515360951605880289243067 104273041427408820433864601)
      ·
        refine ⟨78204781070556615325398451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104273041427408820433864601 78204781070556615325398451)
        ·
          refine ⟨117307171605834922988097677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78204781070556615325398451 117307171605834922988097677)
          ·
            refine ⟨43990189352188096120536629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117307171605834922988097677 43990189352188096120536629)
            ·
              refine ⟨4124080251767634011300309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43990189352188096120536629 4124080251767634011300309)
              ·
                refine ⟨96658130900803922139851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4124080251767634011300309 96658130900803922139851)
                ·
                  rfl

theorem cell23_5082508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 7].length) (baseStart_5082508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082508 prefixEnd_5082508 := by exact prefixLift 5082508
  have htrace : WordTrace (prefixWord ++ tailWord_5082508) baseStart_5082508 baseEnd_5082508 := by
    simpa [prefixWord, tailWord_5082508, baseEnd_5082508] using wordTrace_append hprefix tailTrace_5082508
  have hstable : (prefixWord ++ tailWord_5082508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082508).length < 2 ^ (prefixWord ++ tailWord_5082508).sum := by decide
  have hdescent : baseEnd_5082508 < baseStart_5082508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082536 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5082536 : Nat := 118140960795 + 5082536 * 2 ^ 59
def prefixEnd_5082536 : Nat := 4983230072969 + 3 ^ 40 * 5082536 * 2
def baseEnd_5082536 : Nat := 2609783911780031788225849

theorem tailTrace_5082536 : CollatzResearch.WordTrace tailWord_5082536 prefixEnd_5082536 2609783911780031788225849 := by
  unfold tailWord_5082536
  simp only [CollatzResearch.WordTrace]
  refine ⟨92687658557423787443333731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123583544743231716591111641 92687658557423787443333731)
  ·
    refine ⟨139031487836135681165000597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92687658557423787443333731 139031487836135681165000597)
    ·
      refine ⟨6517100992318860054609403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139031487836135681165000597 6517100992318860054609403)
      ·
        refine ⟨9775651488478290081914105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517100992318860054609403 9775651488478290081914105)
        ·
          refine ⟨7331738616358717561435579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9775651488478290081914105 7331738616358717561435579)
          ·
            refine ⟨10997607924538076342153369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7331738616358717561435579 10997607924538076342153369)
            ·
              refine ⟨8248205943403557256615027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10997607924538076342153369 8248205943403557256615027)
              ·
                refine ⟨12372308915105335884922541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8248205943403557256615027 12372308915105335884922541)
                ·
                  refine ⟨4639615843164500956845953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12372308915105335884922541 4639615843164500956845953)
                  ·
                    refine ⟨3479711882373375717634465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4639615843164500956845953 3479711882373375717634465)
                    ·
                      refine ⟨2609783911780031788225849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479711882373375717634465 2609783911780031788225849)
                      ·
                        rfl

theorem cell23_5082536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5082536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082536 prefixEnd_5082536 := by exact prefixLift 5082536
  have htrace : WordTrace (prefixWord ++ tailWord_5082536) baseStart_5082536 baseEnd_5082536 := by
    simpa [prefixWord, tailWord_5082536, baseEnd_5082536] using wordTrace_append hprefix tailTrace_5082536
  have hstable : (prefixWord ++ tailWord_5082536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082536).length < 2 ^ (prefixWord ++ tailWord_5082536).sum := by decide
  have hdescent : baseEnd_5082536 < baseStart_5082536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082575 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 1, 4, 2]
def baseStart_5082575 : Nat := 118140960795 + 5082575 * 2 ^ 59
def prefixEnd_5082575 : Nat := 4983230072969 + 3 ^ 40 * 5082575 * 2
def baseEnd_5082575 : Nat := 2609803937525557135638169

theorem tailTrace_5082575 : CollatzResearch.WordTrace tailWord_5082575 prefixEnd_5082575 2609803937525557135638169 := by
  unfold tailWord_5082575
  simp only [CollatzResearch.WordTrace]
  refine ⟨185376739561706284547337179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123584493041137523031558119 185376739561706284547337179)
  ·
    refine ⟨278065109342559426821005769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185376739561706284547337179 278065109342559426821005769)
    ·
      refine ⟨208548832006919570115754327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278065109342559426821005769 208548832006919570115754327)
      ·
        refine ⟨312823248010379355173631491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208548832006919570115754327 312823248010379355173631491)
        ·
          refine ⟨469234872015569032760447237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312823248010379355173631491 469234872015569032760447237)
          ·
            refine ⟨87981538502919193642583857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 469234872015569032760447237 87981538502919193642583857)
            ·
              refine ⟨65986153877189395231937893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87981538502919193642583857 65986153877189395231937893)
              ·
                refine ⟨12372403851973011605988355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65986153877189395231937893 12372403851973011605988355)
                ·
                  refine ⟨18558605777959517408982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12372403851973011605988355 18558605777959517408982533)
                  ·
                    refine ⟨3479738583367409514184225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18558605777959517408982533 3479738583367409514184225)
                    ·
                      refine ⟨2609803937525557135638169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479738583367409514184225 2609803937525557135638169)
                      ·
                        rfl

theorem cell23_5082575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4, 2].length) (baseStart_5082575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082575 prefixEnd_5082575 := by exact prefixLift 5082575
  have htrace : WordTrace (prefixWord ++ tailWord_5082575) baseStart_5082575 baseEnd_5082575 := by
    simpa [prefixWord, tailWord_5082575, baseEnd_5082575] using wordTrace_append hprefix tailTrace_5082575
  have hstable : (prefixWord ++ tailWord_5082575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082575).length < 2 ^ (prefixWord ++ tailWord_5082575).sum := by decide
  have hdescent : baseEnd_5082575 < baseStart_5082575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082609 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 2, 2, 2]
def baseStart_5082609 : Nat := 118140960795 + 5082609 * 2 ^ 59
def prefixEnd_5082609 : Nat := 4983230072969 + 3 ^ 40 * 5082609 * 2
def baseEnd_5082609 : Nat := 2609821395867810002613013

theorem tailTrace_5082609 : CollatzResearch.WordTrace tailWord_5082609 prefixEnd_5082609 2609821395867810002613013 := by
  unfold tailWord_5082609
  simp only [CollatzResearch.WordTrace]
  refine ⟨185377979643583108354074881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123585319762388738902716587 185377979643583108354074881)
  ·
    refine ⟨139033484732687331265556161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185377979643583108354074881 139033484732687331265556161)
    ·
      refine ⟨104275113549515498449167121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139033484732687331265556161 104275113549515498449167121)
      ·
        refine ⟨78206335162136623836875341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104275113549515498449167121 78206335162136623836875341)
        ·
          refine ⟨29327375685801233938828253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78206335162136623836875341 29327375685801233938828253)
          ·
            refine ⟨10997765882175462727060595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29327375685801233938828253 10997765882175462727060595)
            ·
              refine ⟨16496648823263194090590893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10997765882175462727060595 16496648823263194090590893)
              ·
                refine ⟨6186243308723697783971585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16496648823263194090590893 6186243308723697783971585)
                ·
                  refine ⟨4639682481542773337978689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6186243308723697783971585 4639682481542773337978689)
                  ·
                    refine ⟨3479761861157080003484017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4639682481542773337978689 3479761861157080003484017)
                    ·
                      refine ⟨2609821395867810002613013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479761861157080003484017 2609821395867810002613013)
                      ·
                        rfl

theorem cell23_5082609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_5082609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082609 prefixEnd_5082609 := by exact prefixLift 5082609
  have htrace : WordTrace (prefixWord ++ tailWord_5082609) baseStart_5082609 baseEnd_5082609 := by
    simpa [prefixWord, tailWord_5082609, baseEnd_5082609] using wordTrace_append hprefix tailTrace_5082609
  have hstable : (prefixWord ++ tailWord_5082609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082609).length < 2 ^ (prefixWord ++ tailWord_5082609).sum := by decide
  have hdescent : baseEnd_5082609 < baseStart_5082609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082645 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_5082645 : Nat := 118140960795 + 5082645 * 2 ^ 59
def prefixEnd_5082645 : Nat := 4983230072969 + 3 ^ 40 * 5082645 * 2
def baseEnd_5082645 : Nat := 869946627057123953920949

theorem tailTrace_5082645 : CollatzResearch.WordTrace tailWord_5082645 prefixEnd_5082645 869946627057123953920949 := by
  unfold tailWord_5082645
  simp only [CollatzResearch.WordTrace]
  refine ⟨185379292671452686502385389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123586195114301791001590259 185379292671452686502385389)
  ·
    refine ⟨69517234751794757438394521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185379292671452686502385389 69517234751794757438394521)
    ·
      refine ⟨52137926063846068078795891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69517234751794757438394521 52137926063846068078795891)
      ·
        refine ⟨78206889095769102118193837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52137926063846068078795891 78206889095769102118193837)
        ·
          refine ⟨29327583410913413294322689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78206889095769102118193837 29327583410913413294322689)
          ·
            refine ⟨21995687558185059970742017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29327583410913413294322689 21995687558185059970742017)
            ·
              refine ⟨16496765668638794978056513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21995687558185059970742017 16496765668638794978056513)
              ·
                refine ⟨12372574251479096233542385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16496765668638794978056513 12372574251479096233542385)
                ·
                  refine ⟨9279430688609322175156789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12372574251479096233542385 9279430688609322175156789)
                  ·
                    refine ⟨869946627057123953920949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9279430688609322175156789 869946627057123953920949)
                    ·
                      rfl

theorem cell23_5082645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_5082645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082645 prefixEnd_5082645 := by exact prefixLift 5082645
  have htrace : WordTrace (prefixWord ++ tailWord_5082645) baseStart_5082645 baseEnd_5082645 := by
    simpa [prefixWord, tailWord_5082645, baseEnd_5082645] using wordTrace_append hprefix tailTrace_5082645
  have hstable : (prefixWord ++ tailWord_5082645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082645).length < 2 ^ (prefixWord ++ tailWord_5082645).sum := by decide
  have hdescent : baseEnd_5082645 < baseStart_5082645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082675 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 5, 4]
def baseStart_5082675 : Nat := 118140960795 + 5082675 * 2 ^ 59
def prefixEnd_5082675 : Nat := 4983230072969 + 3 ^ 40 * 5082675 * 2
def baseEnd_5082675 : Nat := 869951761863668914795903

theorem tailTrace_5082675 : CollatzResearch.WordTrace tailWord_5082675 prefixEnd_5082675 869951761863668914795903 := by
  unfold tailWord_5082675
  simp only [CollatzResearch.WordTrace]
  refine ⟨185380386861344001625977479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123586924574229334417318319 185380386861344001625977479)
  ·
    refine ⟨278070580292016002438966219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185380386861344001625977479 278070580292016002438966219)
    ·
      refine ⟨417105870438024003658449329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278070580292016002438966219 417105870438024003658449329)
      ·
        refine ⟨312829402828518002743836997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417105870438024003658449329 312829402828518002743836997)
        ·
          refine ⟨58655513030347125514469437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312829402828518002743836997 58655513030347125514469437)
          ·
            refine ⟨21995817386380172067926039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58655513030347125514469437 21995817386380172067926039)
            ·
              refine ⟨32993726079570258101889059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21995817386380172067926039 32993726079570258101889059)
              ·
                refine ⟨49490589119355387152833589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32993726079570258101889059 49490589119355387152833589)
                ·
                  refine ⟨4639742729939567545578149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49490589119355387152833589 4639742729939567545578149)
                  ·
                    refine ⟨869951761863668914795903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639742729939567545578149 869951761863668914795903)
                    ·
                      rfl

theorem cell23_5082675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 4].length) (baseStart_5082675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082675 prefixEnd_5082675 := by exact prefixLift 5082675
  have htrace : WordTrace (prefixWord ++ tailWord_5082675) baseStart_5082675 baseEnd_5082675 := by
    simpa [prefixWord, tailWord_5082675, baseEnd_5082675] using wordTrace_append hprefix tailTrace_5082675
  have hstable : (prefixWord ++ tailWord_5082675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082675).length < 2 ^ (prefixWord ++ tailWord_5082675).sum := by decide
  have hdescent : baseEnd_5082675 < baseStart_5082675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082688 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 8]
def baseStart_5082688 : Nat := 118140960795 + 5082688 * 2 ^ 59
def prefixEnd_5082688 : Nat := 4983230072969 + 3 ^ 40 * 5082688 * 2
def baseEnd_5082688 : Nat := 289984662315501688169461

theorem tailTrace_5082688 : CollatzResearch.WordTrace tailWord_5082688 prefixEnd_5082688 289984662315501688169461 := by
  unfold tailWord_5082688
  simp only [CollatzResearch.WordTrace]
  refine ⟨92690430505148452423100359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123587240673531269897467145 92690430505148452423100359)
  ·
    refine ⟨139035645757722678634650539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92690430505148452423100359 139035645757722678634650539)
    ·
      refine ⟨208553468636584017951975809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139035645757722678634650539 208553468636584017951975809)
      ·
        refine ⟨156415101477438013463981857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208553468636584017951975809 156415101477438013463981857)
        ·
          refine ⟨117311326108078510097986393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156415101477438013463981857 117311326108078510097986393)
          ·
            refine ⟨87983494581058882573489795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117311326108078510097986393 87983494581058882573489795)
            ·
              refine ⟨131975241871588323860234693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87983494581058882573489795 131975241871588323860234693)
              ·
                refine ⟨24745357850922810723794005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131975241871588323860234693 24745357850922810723794005)
                ·
                  refine ⟨289984662315501688169461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24745357850922810723794005 289984662315501688169461)
                  ·
                    rfl

theorem cell23_5082688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_5082688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082688 prefixEnd_5082688 := by exact prefixLift 5082688
  have htrace : WordTrace (prefixWord ++ tailWord_5082688) baseStart_5082688 baseEnd_5082688 := by
    simpa [prefixWord, tailWord_5082688, baseEnd_5082688] using wordTrace_append hprefix tailTrace_5082688
  have hstable : (prefixWord ++ tailWord_5082688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082688).length < 2 ^ (prefixWord ++ tailWord_5082688).sum := by decide
  have hdescent : baseEnd_5082688 < baseStart_5082688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082755 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 4]
def baseStart_5082755 : Nat := 118140960795 + 5082755 * 2 ^ 59
def prefixEnd_5082755 : Nat := 4983230072969 + 3 ^ 40 * 5082755 * 2
def baseEnd_5082755 : Nat := 2609896364043366431387341

theorem tailTrace_5082755 : CollatzResearch.WordTrace tailWord_5082755 prefixEnd_5082755 2609896364043366431387341 := by
  unfold tailWord_5082755
  simp only [CollatzResearch.WordTrace]
  refine ⟨185383304701054175288889719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123588869800702783525926479 185383304701054175288889719)
  ·
    refine ⟨278074957051581262933334579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185383304701054175288889719 278074957051581262933334579)
    ·
      refine ⟨417112435577371894400001869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278074957051581262933334579 417112435577371894400001869)
      ·
        refine ⟨156417163341514460400000701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417112435577371894400001869 156417163341514460400000701)
        ·
          refine ⟨58656436253067922650000263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156417163341514460400000701 58656436253067922650000263)
          ·
            refine ⟨87984654379601883975000395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58656436253067922650000263 87984654379601883975000395)
            ·
              refine ⟨131976981569402825962500593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87984654379601883975000395 131976981569402825962500593)
              ·
                refine ⟨98982736177052119471875445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131976981569402825962500593 98982736177052119471875445)
                ·
                  refine ⟨9279631516598636200488323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98982736177052119471875445 9279631516598636200488323)
                  ·
                    refine ⟨13919447274897954300732485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9279631516598636200488323 13919447274897954300732485)
                    ·
                      refine ⟨2609896364043366431387341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13919447274897954300732485 2609896364043366431387341)
                      ·
                        rfl

theorem cell23_5082755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_5082755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082755 prefixEnd_5082755 := by exact prefixLift 5082755
  have htrace : WordTrace (prefixWord ++ tailWord_5082755) baseStart_5082755 baseEnd_5082755 := by
    simpa [prefixWord, tailWord_5082755, baseEnd_5082755] using wordTrace_append hprefix tailTrace_5082755
  have hstable : (prefixWord ++ tailWord_5082755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082755).length < 2 ^ (prefixWord ++ tailWord_5082755).sum := by decide
  have hdescent : baseEnd_5082755 < baseStart_5082755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082759 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_5082759 : Nat := 118140960795 + 5082759 * 2 ^ 59
def prefixEnd_5082759 : Nat := 4983230072969 + 3 ^ 40 * 5082759 * 2
def baseEnd_5082759 : Nat := 2609898417965984415737323

theorem tailTrace_5082759 : CollatzResearch.WordTrace tailWord_5082759 prefixEnd_5082759 2609898417965984415737323 := by
  unfold tailWord_5082759
  simp only [CollatzResearch.WordTrace]
  refine ⟨185383450593039683972035331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123588967062026455981356887 185383450593039683972035331)
  ·
    refine ⟨278075175889559525958052997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185383450593039683972035331 278075175889559525958052997)
    ·
      refine ⟨52139095479292411117134937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278075175889559525958052997 52139095479292411117134937)
      ·
        refine ⟨39104321609469308337851203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52139095479292411117134937 39104321609469308337851203)
        ·
          refine ⟨58656482414203962506776805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39104321609469308337851203 58656482414203962506776805)
          ·
            refine ⟨10998090452663242970020651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58656482414203962506776805 10998090452663242970020651)
            ·
              refine ⟨16497135678994864455030977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10998090452663242970020651 16497135678994864455030977)
              ·
                refine ⟨12372851759246148341273233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16497135678994864455030977 12372851759246148341273233)
                ·
                  refine ⟨9279638819434611255954925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12372851759246148341273233 9279638819434611255954925)
                  ·
                    refine ⟨3479864557287979220983097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9279638819434611255954925 3479864557287979220983097)
                    ·
                      refine ⟨2609898417965984415737323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479864557287979220983097 2609898417965984415737323)
                      ·
                        rfl

theorem cell23_5082759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_5082759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082759 prefixEnd_5082759 := by exact prefixLift 5082759
  have htrace : WordTrace (prefixWord ++ tailWord_5082759) baseStart_5082759 baseEnd_5082759 := by
    simpa [prefixWord, tailWord_5082759, baseEnd_5082759] using wordTrace_append hprefix tailTrace_5082759
  have hstable : (prefixWord ++ tailWord_5082759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082759).length < 2 ^ (prefixWord ++ tailWord_5082759).sum := by decide
  have hdescent : baseEnd_5082759 < baseStart_5082759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082766 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_5082766 : Nat := 118140960795 + 5082766 * 2 ^ 59
def prefixEnd_5082766 : Nat := 4983230072969 + 3 ^ 40 * 5082766 * 2
def baseEnd_5082766 : Nat := 2609902012330565888349791

theorem tailTrace_5082766 : CollatzResearch.WordTrace tailWord_5082766 prefixEnd_5082766 2609902012330565888349791 := by
  unfold tailWord_5082766
  simp only [CollatzResearch.WordTrace]
  refine ⟨23172963238001790520942519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123589137269342882778360101 23172963238001790520942519)
  ·
    refine ⟨34759444857002685781413779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23172963238001790520942519 34759444857002685781413779)
    ·
      refine ⟨52139167285504028672120669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34759444857002685781413779 52139167285504028672120669)
      ·
        refine ⟨19552187732064010752045251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52139167285504028672120669 19552187732064010752045251)
        ·
          refine ⟨29328281598096016128067877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19552187732064010752045251 29328281598096016128067877)
          ·
            refine ⟨5499052799643003024012727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29328281598096016128067877 5499052799643003024012727)
            ·
              refine ⟨8248579199464504536019091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499052799643003024012727 8248579199464504536019091)
              ·
                refine ⟨12372868799196756804028637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8248579199464504536019091 12372868799196756804028637)
                ·
                  refine ⟨4639825799698783801510739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12372868799196756804028637 4639825799698783801510739)
                  ·
                    refine ⟨6959738699548175702266109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4639825799698783801510739 6959738699548175702266109)
                    ·
                      refine ⟨2609902012330565888349791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6959738699548175702266109 2609902012330565888349791)
                      ·
                        rfl

theorem cell23_5082766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_5082766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082766 prefixEnd_5082766 := by exact prefixLift 5082766
  have htrace : WordTrace (prefixWord ++ tailWord_5082766) baseStart_5082766 baseEnd_5082766 := by
    simpa [prefixWord, tailWord_5082766, baseEnd_5082766] using wordTrace_append hprefix tailTrace_5082766
  have hstable : (prefixWord ++ tailWord_5082766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082766).length < 2 ^ (prefixWord ++ tailWord_5082766).sum := by decide
  have hdescent : baseEnd_5082766 < baseStart_5082766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082789 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 3, 2, 2]
def baseStart_5082789 : Nat := 118140960795 + 5082789 * 2 ^ 59
def prefixEnd_5082789 : Nat := 4983230072969 + 3 ^ 40 * 5082789 * 2
def baseEnd_5082789 : Nat := 2609913822385619298362185

theorem tailTrace_5082789 : CollatzResearch.WordTrace tailWord_5082789 prefixEnd_5082789 2609913822385619298362185 := by
  unfold tailWord_5082789
  simp only [CollatzResearch.WordTrace]
  refine ⟨185384544782930999095627421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123589696521953999397084947 185384544782930999095627421)
  ·
    refine ⟨69519204293599124660860283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185384544782930999095627421 69519204293599124660860283)
    ·
      refine ⟨104278806440398686991290425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69519204293599124660860283 104278806440398686991290425)
      ·
        refine ⟨78209104830299015243467819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104278806440398686991290425 78209104830299015243467819)
        ·
          refine ⟨117313657245448522865201729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78209104830299015243467819 117313657245448522865201729)
          ·
            refine ⟨87985242934086392148901297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117313657245448522865201729 87985242934086392148901297)
            ·
              refine ⟨65988932200564794111675973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87985242934086392148901297 65988932200564794111675973)
              ·
                refine ⟨12372924787605898895939245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65988932200564794111675973 12372924787605898895939245)
                ·
                  refine ⟨4639846795352212085977217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12372924787605898895939245 4639846795352212085977217)
                  ·
                    refine ⟨3479885096514159064482913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4639846795352212085977217 3479885096514159064482913)
                    ·
                      refine ⟨2609913822385619298362185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479885096514159064482913 2609913822385619298362185)
                      ·
                        rfl

theorem cell23_5082789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_5082789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082789 prefixEnd_5082789 := by exact prefixLift 5082789
  have htrace : WordTrace (prefixWord ++ tailWord_5082789) baseStart_5082789 baseEnd_5082789 := by
    simpa [prefixWord, tailWord_5082789, baseEnd_5082789] using wordTrace_append hprefix tailTrace_5082789
  have hstable : (prefixWord ++ tailWord_5082789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082789).length < 2 ^ (prefixWord ++ tailWord_5082789).sum := by decide
  have hdescent : baseEnd_5082789 < baseStart_5082789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082829 : List Nat := [1, 6, 2, 1, 1, 1, 3, 8]
def baseStart_5082829 : Nat := 118140960795 + 5082829 * 2 ^ 59
def prefixEnd_5082829 : Nat := 4983230072969 + 3 ^ 40 * 5082829 * 2
def baseEnd_5082829 : Nat := 96664235615251820068963

theorem tailTrace_5082829 : CollatzResearch.WordTrace tailWord_5082829 prefixEnd_5082829 96664235615251820068963 := by
  unfold tailWord_5082829
  simp only [CollatzResearch.WordTrace]
  refine ⟨185386003702786085927083541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123590669135190723951389027 185386003702786085927083541)
  ·
    refine ⟨8689968923568097777832041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 185386003702786085927083541 8689968923568097777832041)
    ·
      refine ⟨6517476692676073333374031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8689968923568097777832041 6517476692676073333374031)
      ·
        refine ⟨9776215039014110000061047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517476692676073333374031 9776215039014110000061047)
        ·
          refine ⟨14664322558521165000091571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9776215039014110000061047 14664322558521165000091571)
          ·
            refine ⟨21996483837781747500137357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14664322558521165000091571 21996483837781747500137357)
            ·
              refine ⟨8248681439168155312551509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21996483837781747500137357 8248681439168155312551509)
              ·
                refine ⟨96664235615251820068963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8248681439168155312551509 96664235615251820068963)
                ·
                  rfl

theorem cell23_5082829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 8].length) (baseStart_5082829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082829 prefixEnd_5082829 := by exact prefixLift 5082829
  have htrace : WordTrace (prefixWord ++ tailWord_5082829) baseStart_5082829 baseEnd_5082829 := by
    simpa [prefixWord, tailWord_5082829, baseEnd_5082829] using wordTrace_append hprefix tailTrace_5082829
  have hstable : (prefixWord ++ tailWord_5082829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082829).length < 2 ^ (prefixWord ++ tailWord_5082829).sum := by decide
  have hdescent : baseEnd_5082829 < baseStart_5082829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082839 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_5082839 : Nat := 118140960795 + 5082839 * 2 ^ 59
def prefixEnd_5082839 : Nat := 4983230072969 + 3 ^ 40 * 5082839 * 2
def baseEnd_5082839 : Nat := 2609939496418344102736955

theorem tailTrace_5082839 : CollatzResearch.WordTrace tailWord_5082839 prefixEnd_5082839 2609939496418344102736955 := by
  unfold tailWord_5082839
  simp only [CollatzResearch.WordTrace]
  refine ⟨185386368432749857634947571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123590912288499905089965047 185386368432749857634947571)
  ·
    refine ⟨278079552649124786452421357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185386368432749857634947571 278079552649124786452421357)
    ·
      refine ⟨104279832243421794919658009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278079552649124786452421357 104279832243421794919658009)
      ·
        refine ⟨78209874182566346189743507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104279832243421794919658009 78209874182566346189743507)
        ·
          refine ⟨117314811273849519284615261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78209874182566346189743507 117314811273849519284615261)
          ·
            refine ⟨43993054227693569731730723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117314811273849519284615261 43993054227693569731730723)
            ·
              refine ⟨65989581341540354597596085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43993054227693569731730723 65989581341540354597596085)
              ·
                refine ⟨6186523250769408243524633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65989581341540354597596085 6186523250769408243524633)
                ·
                  refine ⟨4639892438077056182643475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6186523250769408243524633 4639892438077056182643475)
                  ·
                    refine ⟨6959838657115584273965213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4639892438077056182643475 6959838657115584273965213)
                    ·
                      refine ⟨2609939496418344102736955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6959838657115584273965213 2609939496418344102736955)
                      ·
                        rfl

theorem cell23_5082839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_5082839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082839 prefixEnd_5082839 := by exact prefixLift 5082839
  have htrace : WordTrace (prefixWord ++ tailWord_5082839) baseStart_5082839 baseEnd_5082839 := by
    simpa [prefixWord, tailWord_5082839, baseEnd_5082839] using wordTrace_append hprefix tailTrace_5082839
  have hstable : (prefixWord ++ tailWord_5082839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082839).length < 2 ^ (prefixWord ++ tailWord_5082839).sum := by decide
  have hdescent : baseEnd_5082839 < baseStart_5082839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082866 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5082866 : Nat := 118140960795 + 5082866 * 2 ^ 59
def prefixEnd_5082866 : Nat := 4983230072969 + 3 ^ 40 * 5082866 * 2
def baseEnd_5082866 : Nat := 2609953360396015497099331

theorem tailTrace_5082866 : CollatzResearch.WordTrace tailWord_5082866 prefixEnd_5082866 2609953360396015497099331 := by
  unfold tailWord_5082866
  simp only [CollatzResearch.WordTrace]
  refine ⟨46346838300913010311545113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123591568802434694164120301 46346838300913010311545113)
  ·
    refine ⟨34760128725684757733658835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46346838300913010311545113 34760128725684757733658835)
    ·
      refine ⟨52140193088527136600488253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34760128725684757733658835 52140193088527136600488253)
      ·
        refine ⟨19552572408197676225183095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52140193088527136600488253 19552572408197676225183095)
        ·
          refine ⟨29328858612296514337774643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19552572408197676225183095 29328858612296514337774643)
          ·
            refine ⟨43993287918444771506661965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29328858612296514337774643 43993287918444771506661965)
            ·
              refine ⟨16497482969416789314998237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43993287918444771506661965 16497482969416789314998237)
              ·
                refine ⟨6186556113531295993124339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16497482969416789314998237 6186556113531295993124339)
                ·
                  refine ⟨9279834170296943989686509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6186556113531295993124339 9279834170296943989686509)
                  ·
                    refine ⟨3479937813861353996132441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9279834170296943989686509 3479937813861353996132441)
                    ·
                      refine ⟨2609953360396015497099331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3479937813861353996132441 2609953360396015497099331)
                      ·
                        rfl

theorem cell23_5082866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5082866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082866 prefixEnd_5082866 := by exact prefixLift 5082866
  have htrace : WordTrace (prefixWord ++ tailWord_5082866) baseStart_5082866 baseEnd_5082866 := by
    simpa [prefixWord, tailWord_5082866, baseEnd_5082866] using wordTrace_append hprefix tailTrace_5082866
  have hstable : (prefixWord ++ tailWord_5082866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082866).length < 2 ^ (prefixWord ++ tailWord_5082866).sum := by decide
  have hdescent : baseEnd_5082866 < baseStart_5082866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082892 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_5082892 : Nat := 118140960795 + 5082892 * 2 ^ 59
def prefixEnd_5082892 : Nat := 4983230072969 + 3 ^ 40 * 5082892 * 2
def baseEnd_5082892 : Nat := 2609966710893032395374211

theorem tailTrace_5082892 : CollatzResearch.WordTrace tailWord_5082892 prefixEnd_5082892 2609966710893032395374211 := by
  unfold tailWord_5082892
  simp only [CollatzResearch.WordTrace]
  refine ⟨92694150750778923843313465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123592201001038565124417953 92694150750778923843313465)
  ·
    refine ⟨69520613063084192882485099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92694150750778923843313465 69520613063084192882485099)
    ·
      refine ⟨104280919594626289323727649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69520613063084192882485099 104280919594626289323727649)
      ·
        refine ⟨78210689695969716992795737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104280919594626289323727649 78210689695969716992795737)
        ·
          refine ⟨58658017271977287744596803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78210689695969716992795737 58658017271977287744596803)
          ·
            refine ⟨87987025907965931616895205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58658017271977287744596803 87987025907965931616895205)
            ·
              refine ⟨16497567357743612178167851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87987025907965931616895205 16497567357743612178167851)
              ·
                refine ⟨24746351036615418267251777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16497567357743612178167851 24746351036615418267251777)
                ·
                  refine ⟨18559763277461563700438833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24746351036615418267251777 18559763277461563700438833)
                  ·
                    refine ⟨13919822458096172775329125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18559763277461563700438833 13919822458096172775329125)
                    ·
                      refine ⟨2609966710893032395374211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13919822458096172775329125 2609966710893032395374211)
                      ·
                        rfl

theorem cell23_5082892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_5082892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082892 prefixEnd_5082892 := by exact prefixLift 5082892
  have htrace : WordTrace (prefixWord ++ tailWord_5082892) baseStart_5082892 baseEnd_5082892 := by
    simpa [prefixWord, tailWord_5082892, baseEnd_5082892] using wordTrace_append hprefix tailTrace_5082892
  have hstable : (prefixWord ++ tailWord_5082892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082892).length < 2 ^ (prefixWord ++ tailWord_5082892).sum := by decide
  have hdescent : baseEnd_5082892 < baseStart_5082892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082905 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_5082905 : Nat := 118140960795 + 5082905 * 2 ^ 59
def prefixEnd_5082905 : Nat := 4983230072969 + 3 ^ 40 * 5082905 * 2
def baseEnd_5082905 : Nat := 2609973386141540844511651

theorem tailTrace_5082905 : CollatzResearch.WordTrace tailWord_5082905 prefixEnd_5082905 2609973386141540844511651 := by
  unfold tailWord_5082905
  simp only [CollatzResearch.WordTrace]
  refine ⟨185388775650510750906850169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123592517100340500604566779 185388775650510750906850169)
  ·
    refine ⟨139041581737883063180137627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185388775650510750906850169 139041581737883063180137627)
    ·
      refine ⟨208562372606824594770206441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139041581737883063180137627 208562372606824594770206441)
      ·
        refine ⟨156421779455118446077654831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208562372606824594770206441 156421779455118446077654831)
        ·
          refine ⟨234632669182677669116482247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156421779455118446077654831 234632669182677669116482247)
          ·
            refine ⟨351949003774016503674723371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234632669182677669116482247 351949003774016503674723371)
            ·
              refine ⟨527923505661024755512085057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351949003774016503674723371 527923505661024755512085057)
              ·
                refine ⟨395942629245768566634063793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527923505661024755512085057 395942629245768566634063793)
                ·
                  refine ⟨296956971934326424975547845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395942629245768566634063793 296956971934326424975547845)
                  ·
                    refine ⟨55679432237686204682915221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296956971934326424975547845 55679432237686204682915221)
                    ·
                      refine ⟨2609973386141540844511651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55679432237686204682915221 2609973386141540844511651)
                      ·
                        rfl

theorem cell23_5082905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_5082905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082905 prefixEnd_5082905 := by exact prefixLift 5082905
  have htrace : WordTrace (prefixWord ++ tailWord_5082905) baseStart_5082905 baseEnd_5082905 := by
    simpa [prefixWord, tailWord_5082905, baseEnd_5082905] using wordTrace_append hprefix tailTrace_5082905
  have hstable : (prefixWord ++ tailWord_5082905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082905).length < 2 ^ (prefixWord ++ tailWord_5082905).sum := by decide
  have hdescent : baseEnd_5082905 < baseStart_5082905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082936 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 5]
def baseStart_5082936 : Nat := 118140960795 + 5082936 * 2 ^ 59
def prefixEnd_5082936 : Nat := 4983230072969 + 3 ^ 40 * 5082936 * 2
def baseEnd_5082936 : Nat := 289998811560203358136001

theorem tailTrace_5082936 : CollatzResearch.WordTrace tailWord_5082936 prefixEnd_5082936 289998811560203358136001 := by
  unfold tailWord_5082936
  simp only [CollatzResearch.WordTrace]
  refine ⟨92694953156699221600614331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123593270875598962134152441 92694953156699221600614331)
  ·
    refine ⟨139042429735048832400921497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92694953156699221600614331 139042429735048832400921497)
    ·
      refine ⟨104281822301286624300691123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139042429735048832400921497 104281822301286624300691123)
      ·
        refine ⟨156422733451929936451036685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104281822301286624300691123 156422733451929936451036685)
        ·
          refine ⟨58658525044473726169138757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156422733451929936451036685 58658525044473726169138757)
          ·
            refine ⟨10998473445838823656713517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58658525044473726169138757 10998473445838823656713517)
            ·
              refine ⟨4124427542189558871267569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10998473445838823656713517 4124427542189558871267569)
              ·
                refine ⟨3093320656642169153450677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4124427542189558871267569 3093320656642169153450677)
                ·
                  refine ⟨289998811560203358136001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3093320656642169153450677 289998811560203358136001)
                  ·
                    rfl

theorem cell23_5082936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 5].length) (baseStart_5082936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082936 prefixEnd_5082936 := by exact prefixLift 5082936
  have htrace : WordTrace (prefixWord ++ tailWord_5082936) baseStart_5082936 baseEnd_5082936 := by
    simpa [prefixWord, tailWord_5082936, baseEnd_5082936] using wordTrace_append hprefix tailTrace_5082936
  have hstable : (prefixWord ++ tailWord_5082936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082936).length < 2 ^ (prefixWord ++ tailWord_5082936).sum := by decide
  have hdescent : baseEnd_5082936 < baseStart_5082936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5082969 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_5082969 : Nat := 118140960795 + 5082969 * 2 ^ 59
def prefixEnd_5082969 : Nat := 4983230072969 + 3 ^ 40 * 5082969 * 2
def baseEnd_5082969 : Nat := 2610006248903428594111357

theorem tailTrace_5082969 : CollatzResearch.WordTrace tailWord_5082969 prefixEnd_5082969 2610006248903428594111357 := by
  unfold tailWord_5082969
  simp only [CollatzResearch.WordTrace]
  refine ⟨185391109922278889837179961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123594073281519259891453307 185391109922278889837179961)
  ·
    refine ⟨139043332441709167377884971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185391109922278889837179961 139043332441709167377884971)
    ·
      refine ⟨208564998662563751066827457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139043332441709167377884971 208564998662563751066827457)
      ·
        refine ⟨156423748996922813300120593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208564998662563751066827457 156423748996922813300120593)
        ·
          refine ⟨117317811747692109975090445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156423748996922813300120593 117317811747692109975090445)
          ·
            refine ⟨43994179405384541240658917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117317811747692109975090445 43994179405384541240658917)
            ·
              refine ⟨8248908638509601482623547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43994179405384541240658917 8248908638509601482623547)
              ·
                refine ⟨12373362957764402223935321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8248908638509601482623547 12373362957764402223935321)
                ·
                  refine ⟨9280022218323301667951491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12373362957764402223935321 9280022218323301667951491)
                  ·
                    refine ⟨13920033327484952501927237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9280022218323301667951491 13920033327484952501927237)
                    ·
                      refine ⟨2610006248903428594111357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13920033327484952501927237 2610006248903428594111357)
                      ·
                        rfl

theorem cell23_5082969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_5082969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5082969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5082969 prefixEnd_5082969 := by exact prefixLift 5082969
  have htrace : WordTrace (prefixWord ++ tailWord_5082969) baseStart_5082969 baseEnd_5082969 := by
    simpa [prefixWord, tailWord_5082969, baseEnd_5082969] using wordTrace_append hprefix tailTrace_5082969
  have hstable : (prefixWord ++ tailWord_5082969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5082969).length < 2 ^ (prefixWord ++ tailWord_5082969).sum := by decide
  have hdescent : baseEnd_5082969 < baseStart_5082969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5082969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083060 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 6]
def baseStart_5083060 : Nat := 118140960795 + 5083060 * 2 ^ 59
def prefixEnd_5083060 : Nat := 4983230072969 + 3 ^ 40 * 5083060 * 2
def baseEnd_5083060 : Nat := 290005886182554193119271

theorem tailTrace_5083060 : CollatzResearch.WordTrace tailWord_5083060 prefixEnd_5083060 290005886182554193119271 := by
  unfold tailWord_5083060
  simp only [CollatzResearch.WordTrace]
  refine ⟨92697214482474606189371317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123596285976632808252495089 92697214482474606189371317)
  ·
    refine ⟨8690363857731994330253561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92697214482474606189371317 8690363857731994330253561)
    ·
      refine ⟨6517772893298995747690171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8690363857731994330253561 6517772893298995747690171)
      ·
        refine ⟨9776659339948493621535257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517772893298995747690171 9776659339948493621535257)
        ·
          refine ⟨7332494504961370216151443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9776659339948493621535257 7332494504961370216151443)
          ·
            refine ⟨10998741757442055324227165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7332494504961370216151443 10998741757442055324227165)
            ·
              refine ⟨4124528159040770746585187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10998741757442055324227165 4124528159040770746585187)
              ·
                refine ⟨6186792238561156119877781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124528159040770746585187 6186792238561156119877781)
                ·
                  refine ⟨290005886182554193119271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6186792238561156119877781 290005886182554193119271)
                  ·
                    rfl

theorem cell23_5083060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_5083060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083060 prefixEnd_5083060 := by exact prefixLift 5083060
  have htrace : WordTrace (prefixWord ++ tailWord_5083060) baseStart_5083060 baseEnd_5083060 := by
    simpa [prefixWord, tailWord_5083060, baseEnd_5083060] using wordTrace_append hprefix tailTrace_5083060
  have hstable : (prefixWord ++ tailWord_5083060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083060).length < 2 ^ (prefixWord ++ tailWord_5083060).sum := by decide
  have hdescent : baseEnd_5083060 < baseStart_5083060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083096 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_5083096 : Nat := 118140960795 + 5083096 * 2 ^ 59
def prefixEnd_5083096 : Nat := 4983230072969 + 3 ^ 40 * 5083096 * 2
def baseEnd_5083096 : Nat := 2610071460946549597223273

theorem tailTrace_5083096 : CollatzResearch.WordTrace tailWord_5083096 prefixEnd_5083096 2610071460946549597223273 := by
  unfold tailWord_5083096
  simp only [CollatzResearch.WordTrace]
  refine ⟨92697870996409395263526571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123597161328545860351368761 92697870996409395263526571)
  ·
    refine ⟨139046806494614092895289857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92697870996409395263526571 139046806494614092895289857)
    ·
      refine ⟨104285104870960569671467393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139046806494614092895289857 104285104870960569671467393)
      ·
        refine ⟨78213828653220427253600545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104285104870960569671467393 78213828653220427253600545)
        ·
          refine ⟨58660371489915320440200409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78213828653220427253600545 58660371489915320440200409)
          ·
            refine ⟨43995278617436490330150307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58660371489915320440200409 43995278617436490330150307)
            ·
              refine ⟨65992917926154735495225461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43995278617436490330150307 65992917926154735495225461)
              ·
                refine ⟨6186836055577006452677387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65992917926154735495225461 6186836055577006452677387)
                ·
                  refine ⟨9280254083365509679016081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6186836055577006452677387 9280254083365509679016081)
                  ·
                    refine ⟨6960190562524132259262061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9280254083365509679016081 6960190562524132259262061)
                    ·
                      refine ⟨2610071460946549597223273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6960190562524132259262061 2610071460946549597223273)
                      ·
                        rfl

theorem cell23_5083096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_5083096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083096 prefixEnd_5083096 := by exact prefixLift 5083096
  have htrace : WordTrace (prefixWord ++ tailWord_5083096) baseStart_5083096 baseEnd_5083096 := by
    simpa [prefixWord, tailWord_5083096, baseEnd_5083096] using wordTrace_append hprefix tailTrace_5083096
  have hstable : (prefixWord ++ tailWord_5083096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083096).length < 2 ^ (prefixWord ++ tailWord_5083096).sum := by decide
  have hdescent : baseEnd_5083096 < baseStart_5083096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083189 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 9]
def baseStart_5083189 : Nat := 118140960795 + 5083189 * 2 ^ 59
def prefixEnd_5083189 : Nat := 4983230072969 + 3 ^ 40 * 5083189 * 2
def baseEnd_5083189 : Nat := 290013246071935303706705

theorem tailTrace_5083189 : CollatzResearch.WordTrace tailWord_5083189 prefixEnd_5083189 290013246071935303706705 := by
  unfold tailWord_5083189
  simp only [CollatzResearch.WordTrace]
  refine ⟨185399133981481867410188621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123599422654321244940125747 185399133981481867410188621)
  ·
    refine ⟨69524675243055700278820733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185399133981481867410188621 69524675243055700278820733)
    ·
      refine ⟨26071753216145887604557775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69524675243055700278820733 26071753216145887604557775)
      ·
        refine ⟨39107629824218831406836663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26071753216145887604557775 39107629824218831406836663)
        ·
          refine ⟨58661444736328247110254995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39107629824218831406836663 58661444736328247110254995)
          ·
            refine ⟨87992167104492370665382493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58661444736328247110254995 87992167104492370665382493)
            ·
              refine ⟨32997062664184638999518435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87992167104492370665382493 32997062664184638999518435)
              ·
                refine ⟨49495593996276958499277653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32997062664184638999518435 49495593996276958499277653)
                ·
                  refine ⟨290013246071935303706705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49495593996276958499277653 290013246071935303706705)
                  ·
                    rfl

theorem cell23_5083189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_5083189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083189 prefixEnd_5083189 := by exact prefixLift 5083189
  have htrace : WordTrace (prefixWord ++ tailWord_5083189) baseStart_5083189 baseEnd_5083189 := by
    simpa [prefixWord, tailWord_5083189, baseEnd_5083189] using wordTrace_append hprefix tailTrace_5083189
  have hstable : (prefixWord ++ tailWord_5083189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083189).length < 2 ^ (prefixWord ++ tailWord_5083189).sum := by decide
  have hdescent : baseEnd_5083189 < baseStart_5083189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083234 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5083234 : Nat := 118140960795 + 5083234 * 2 ^ 59
def prefixEnd_5083234 : Nat := 4983230072969 + 3 ^ 40 * 5083234 * 2
def baseEnd_5083234 : Nat := 2610142321276870057297639

theorem tailTrace_5083234 : CollatzResearch.WordTrace tailWord_5083234 prefixEnd_5083234 2610142321276870057297639 := by
  unfold tailWord_5083234
  simp only [CollatzResearch.WordTrace]
  refine ⟨46350193816579710023894189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123600516844212560063717837 46350193816579710023894189)
  ·
    refine ⟨17381322681217391258960321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46350193816579710023894189 17381322681217391258960321)
    ·
      refine ⟨13035992010913043444220241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17381322681217391258960321 13035992010913043444220241)
      ·
        refine ⟨9776994008184782583165181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13035992010913043444220241 9776994008184782583165181)
        ·
          refine ⟨3666372753069293468686943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9776994008184782583165181 3666372753069293468686943)
          ·
            refine ⟨5499559129603940203030415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666372753069293468686943 5499559129603940203030415)
            ·
              refine ⟨8249338694405910304545623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499559129603940203030415 8249338694405910304545623)
              ·
                refine ⟨12374008041608865456818435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8249338694405910304545623 12374008041608865456818435)
                ·
                  refine ⟨18561012062413298185227653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12374008041608865456818435 18561012062413298185227653)
                  ·
                    refine ⟨3480189761702493409730185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18561012062413298185227653 3480189761702493409730185)
                    ·
                      refine ⟨2610142321276870057297639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480189761702493409730185 2610142321276870057297639)
                      ·
                        rfl

theorem cell23_5083234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5083234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083234 prefixEnd_5083234 := by exact prefixLift 5083234
  have htrace : WordTrace (prefixWord ++ tailWord_5083234) baseStart_5083234 baseEnd_5083234 := by
    simpa [prefixWord, tailWord_5083234, baseEnd_5083234] using wordTrace_append hprefix tailTrace_5083234
  have hstable : (prefixWord ++ tailWord_5083234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083234).length < 2 ^ (prefixWord ++ tailWord_5083234).sum := by decide
  have hdescent : baseEnd_5083234 < baseStart_5083234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083249 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_5083249 : Nat := 118140960795 + 5083249 * 2 ^ 59
def prefixEnd_5083249 : Nat := 4983230072969 + 3 ^ 40 * 5083249 * 2
def baseEnd_5083249 : Nat := 870050007828895832870023

theorem tailTrace_5083249 : CollatzResearch.WordTrace tailWord_5083249 prefixEnd_5083249 870050007828895832870023 := by
  unfold tailWord_5083249
  simp only [CollatzResearch.WordTrace]
  refine ⟨185401322361264497657372801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123600881574176331771581867 185401322361264497657372801)
  ·
    refine ⟨139050991770948373243029601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185401322361264497657372801 139050991770948373243029601)
    ·
      refine ⟨104288243828211279932272201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139050991770948373243029601 104288243828211279932272201)
      ·
        refine ⟨78216182871158459949204151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104288243828211279932272201 78216182871158459949204151)
        ·
          refine ⟨117324274306737689923806227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78216182871158459949204151 117324274306737689923806227)
          ·
            refine ⟨175986411460106534885709341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117324274306737689923806227 175986411460106534885709341)
            ·
              refine ⟨65994904297539950582141003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175986411460106534885709341 65994904297539950582141003)
              ·
                refine ⟨98992356446309925873211505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65994904297539950582141003 98992356446309925873211505)
                ·
                  refine ⟨74244267334732444404908629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98992356446309925873211505 74244267334732444404908629)
                  ·
                    refine ⟨870050007828895832870023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74244267334732444404908629 870050007828895832870023)
                    ·
                      rfl

theorem cell23_5083249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_5083249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083249 prefixEnd_5083249 := by exact prefixLift 5083249
  have htrace : WordTrace (prefixWord ++ tailWord_5083249) baseStart_5083249 baseEnd_5083249 := by
    simpa [prefixWord, tailWord_5083249, baseEnd_5083249] using wordTrace_append hprefix tailTrace_5083249
  have hstable : (prefixWord ++ tailWord_5083249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083249).length < 2 ^ (prefixWord ++ tailWord_5083249).sum := by decide
  have hdescent : baseEnd_5083249 < baseStart_5083249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083256 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_5083256 : Nat := 118140960795 + 5083256 * 2 ^ 59
def prefixEnd_5083256 : Nat := 4983230072969 + 3 ^ 40 * 5083256 * 2
def baseEnd_5083256 : Nat := 2610153617851268971222537

theorem tailTrace_5083256 : CollatzResearch.WordTrace tailWord_5083256 prefixEnd_5083256 2610153617851268971222537 := by
  unfold tailWord_5083256
  simp only [CollatzResearch.WordTrace]
  refine ⟨92700788836119568926438811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123601051781492758568585081 92700788836119568926438811)
  ·
    refine ⟨139051183254179353389658217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92700788836119568926438811 139051183254179353389658217)
    ·
      refine ⟨104288387440634515042243663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139051183254179353389658217 104288387440634515042243663)
      ·
        refine ⟨156432581160951772563365495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104288387440634515042243663 156432581160951772563365495)
        ·
          refine ⟨234648871741427658845048243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156432581160951772563365495 234648871741427658845048243)
          ·
            refine ⟨351973307612141488267572365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234648871741427658845048243 351973307612141488267572365)
            ·
              refine ⟨131989990354553058100339637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351973307612141488267572365 131989990354553058100339637)
              ·
                refine ⟨12374061595739349196906841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131989990354553058100339637 12374061595739349196906841)
                ·
                  refine ⟨9280546196804511897680131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12374061595739349196906841 9280546196804511897680131)
                  ·
                    refine ⟨13920819295206767846520197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9280546196804511897680131 13920819295206767846520197)
                    ·
                      refine ⟨2610153617851268971222537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13920819295206767846520197 2610153617851268971222537)
                      ·
                        rfl

theorem cell23_5083256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_5083256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083256 prefixEnd_5083256 := by exact prefixLift 5083256
  have htrace : WordTrace (prefixWord ++ tailWord_5083256) baseStart_5083256 baseEnd_5083256 := by
    simpa [prefixWord, tailWord_5083256, baseEnd_5083256] using wordTrace_append hprefix tailTrace_5083256
  have hstable : (prefixWord ++ tailWord_5083256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083256).length < 2 ^ (prefixWord ++ tailWord_5083256).sum := by decide
  have hdescent : baseEnd_5083256 < baseStart_5083256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083259 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_5083259 : Nat := 118140960795 + 5083259 * 2 ^ 59
def prefixEnd_5083259 : Nat := 4983230072969 + 3 ^ 40 * 5083259 * 2
def baseEnd_5083259 : Nat := 2610155158293232459485023

theorem tailTrace_5083259 : CollatzResearch.WordTrace tailWord_5083259 prefixEnd_5083259 2610155158293232459485023 := by
  unfold tailWord_5083259
  simp only [CollatzResearch.WordTrace]
  refine ⟨185401687091228269365236831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123601124727485512910157887 185401687091228269365236831)
  ·
    refine ⟨278102530636842404047855247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185401687091228269365236831 278102530636842404047855247)
    ·
      refine ⟨417153795955263606071782871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278102530636842404047855247 417153795955263606071782871)
      ·
        refine ⟨625730693932895409107674307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417153795955263606071782871 625730693932895409107674307)
        ·
          refine ⟨938596040899343113661511461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625730693932895409107674307 938596040899343113661511461)
          ·
            refine ⟨175986757668626833811533399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 938596040899343113661511461 175986757668626833811533399)
            ·
              refine ⟨263980136502940250717300099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175986757668626833811533399 263980136502940250717300099)
              ·
                refine ⟨395970204754410376075950149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263980136502940250717300099 395970204754410376075950149)
                ·
                  refine ⟨74244413391451945514240653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395970204754410376075950149 74244413391451945514240653)
                  ·
                    refine ⟨27841655021794479567840245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74244413391451945514240653 27841655021794479567840245)
                    ·
                      refine ⟨2610155158293232459485023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27841655021794479567840245 2610155158293232459485023)
                      ·
                        rfl

theorem cell23_5083259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_5083259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083259 prefixEnd_5083259 := by exact prefixLift 5083259
  have htrace : WordTrace (prefixWord ++ tailWord_5083259) baseStart_5083259 baseEnd_5083259 := by
    simpa [prefixWord, tailWord_5083259, baseEnd_5083259] using wordTrace_append hprefix tailTrace_5083259
  have hstable : (prefixWord ++ tailWord_5083259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083259).length < 2 ^ (prefixWord ++ tailWord_5083259).sum := by decide
  have hdescent : baseEnd_5083259 < baseStart_5083259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083357 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5083357 : Nat := 118140960795 + 5083357 * 2 ^ 59
def prefixEnd_5083357 : Nat := 4983230072969 + 3 ^ 40 * 5083357 * 2
def baseEnd_5083357 : Nat := 2610205479397373076059573

theorem tailTrace_5083357 : CollatzResearch.WordTrace tailWord_5083357 prefixEnd_5083357 2610205479397373076059573 := by
  unfold tailWord_5083357
  simp only [CollatzResearch.WordTrace]
  refine ⟨185405261444873232102304325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123603507629915488068202883 185405261444873232102304325)
  ·
    refine ⟨34763486520913731019182061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185405261444873232102304325 34763486520913731019182061)
    ·
      refine ⟨13036307445342649132193273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34763486520913731019182061 13036307445342649132193273)
      ·
        refine ⟨9777230584006986849144955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13036307445342649132193273 9777230584006986849144955)
        ·
          refine ⟨14665845876010480273717433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777230584006986849144955 14665845876010480273717433)
          ·
            refine ⟨10999384407007860205288075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14665845876010480273717433 10999384407007860205288075)
            ·
              refine ⟨16499076610511790307932113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10999384407007860205288075 16499076610511790307932113)
              ·
                refine ⟨12374307457883842730949085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16499076610511790307932113 12374307457883842730949085)
                ·
                  refine ⟨4640365296706441024105907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12374307457883842730949085 4640365296706441024105907)
                  ·
                    refine ⟨6960547945059661536158861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640365296706441024105907 6960547945059661536158861)
                    ·
                      refine ⟨2610205479397373076059573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6960547945059661536158861 2610205479397373076059573)
                      ·
                        rfl

theorem cell23_5083357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5083357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083357 prefixEnd_5083357 := by exact prefixLift 5083357
  have htrace : WordTrace (prefixWord ++ tailWord_5083357) baseStart_5083357 baseEnd_5083357 := by
    simpa [prefixWord, tailWord_5083357, baseEnd_5083357] using wordTrace_append hprefix tailTrace_5083357
  have hstable : (prefixWord ++ tailWord_5083357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083357).length < 2 ^ (prefixWord ++ tailWord_5083357).sum := by decide
  have hdescent : baseEnd_5083357 < baseStart_5083357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083367 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5083367 : Nat := 118140960795 + 5083367 * 2 ^ 59
def prefixEnd_5083367 : Nat := 4983230072969 + 3 ^ 40 * 5083367 * 2
def baseEnd_5083367 : Nat := 2610210614203918036934527

theorem tailTrace_5083367 : CollatzResearch.WordTrace tailWord_5083367 prefixEnd_5083367 2610210614203918036934527 := by
  unfold tailWord_5083367
  simp only [CollatzResearch.WordTrace]
  refine ⟨185405626174837003810168355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123603750783224669206778903 185405626174837003810168355)
  ·
    refine ⟨278108439262255505715252533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185405626174837003810168355 278108439262255505715252533)
    ·
      refine ⟨26072666180836453660804925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278108439262255505715252533 26072666180836453660804925)
      ·
        refine ⟨9777249817813670122801847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26072666180836453660804925 9777249817813670122801847)
        ·
          refine ⟨14665874726720505184202771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777249817813670122801847 14665874726720505184202771)
          ·
            refine ⟨21998812090080757776304157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14665874726720505184202771 21998812090080757776304157)
            ·
              refine ⟨8249554533780284166114059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21998812090080757776304157 8249554533780284166114059)
              ·
                refine ⟨12374331800670426249171089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8249554533780284166114059 12374331800670426249171089)
                ·
                  refine ⟨9280748850502819686878317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12374331800670426249171089 9280748850502819686878317)
                  ·
                    refine ⟨3480280818938557382579369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9280748850502819686878317 3480280818938557382579369)
                    ·
                      refine ⟨2610210614203918036934527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480280818938557382579369 2610210614203918036934527)
                      ·
                        rfl

theorem cell23_5083367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5083367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083367 prefixEnd_5083367 := by exact prefixLift 5083367
  have htrace : WordTrace (prefixWord ++ tailWord_5083367) baseStart_5083367 baseEnd_5083367 := by
    simpa [prefixWord, tailWord_5083367, baseEnd_5083367] using wordTrace_append hprefix tailTrace_5083367
  have hstable : (prefixWord ++ tailWord_5083367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083367).length < 2 ^ (prefixWord ++ tailWord_5083367).sum := by decide
  have hdescent : baseEnd_5083367 < baseStart_5083367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083386 : List Nat := [3, 1, 1, 1, 1, 6, 10]
def baseStart_5083386 : Nat := 118140960795 + 5083386 * 2 ^ 59
def prefixEnd_5083386 : Nat := 4983230072969 + 3 ^ 40 * 5083386 * 2
def baseEnd_5083386 : Nat := 32224942843658684723419

theorem tailTrace_5083386 : CollatzResearch.WordTrace tailWord_5083386 prefixEnd_5083386 32224942843658684723419 := by
  unfold tailWord_5083386
  simp only [CollatzResearch.WordTrace]
  refine ⟨46351579790442042513777503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123604212774512113370073341 46351579790442042513777503)
  ·
    refine ⟨69527369685663063770666255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46351579790442042513777503 69527369685663063770666255)
    ·
      refine ⟨104291054528494595655999383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69527369685663063770666255 104291054528494595655999383)
      ·
        refine ⟨156436581792741893483999075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104291054528494595655999383 156436581792741893483999075)
        ·
          refine ⟨234654872689112840225998613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156436581792741893483999075 234654872689112840225998613)
          ·
            refine ⟨10999447157302164385593685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 234654872689112840225998613 10999447157302164385593685)
            ·
              refine ⟨32224942843658684723419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10999447157302164385593685 32224942843658684723419)
              ·
                rfl

theorem cell23_5083386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 10].length) (baseStart_5083386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083386 prefixEnd_5083386 := by exact prefixLift 5083386
  have htrace : WordTrace (prefixWord ++ tailWord_5083386) baseStart_5083386 baseEnd_5083386 := by
    simpa [prefixWord, tailWord_5083386, baseEnd_5083386] using wordTrace_append hprefix tailTrace_5083386
  have hstable : (prefixWord ++ tailWord_5083386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083386).length < 2 ^ (prefixWord ++ tailWord_5083386).sum := by decide
  have hdescent : baseEnd_5083386 < baseStart_5083386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083390 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_5083390 : Nat := 118140960795 + 5083390 * 2 ^ 59
def prefixEnd_5083390 : Nat := 4983230072969 + 3 ^ 40 * 5083390 * 2
def baseEnd_5083390 : Nat := 870074141419657148982307

theorem tailTrace_5083390 : CollatzResearch.WordTrace tailWord_5083390 prefixEnd_5083390 870074141419657148982307 := by
  unfold tailWord_5083390
  simp only [CollatzResearch.WordTrace]
  refine ⟨23175808131719209842281953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123604310035835785825503749 23175808131719209842281953)
  ·
    refine ⟨17381856098789407381711465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23175808131719209842281953 17381856098789407381711465)
    ·
      refine ⟨13036392074092055536283599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17381856098789407381711465 13036392074092055536283599)
      ·
        refine ⟨19554588111138083304425399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036392074092055536283599 19554588111138083304425399)
        ·
          refine ⟨29331882166707124956638099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19554588111138083304425399 29331882166707124956638099)
          ·
            refine ⟨43997823250060687434957149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29331882166707124956638099 43997823250060687434957149)
            ·
              refine ⟨16499183718772757788108931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43997823250060687434957149 16499183718772757788108931)
              ·
                refine ⟨24748775578159136682163397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16499183718772757788108931 24748775578159136682163397)
                ·
                  refine ⟨4640395420904838127905637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24748775578159136682163397 4640395420904838127905637)
                  ·
                    refine ⟨870074141419657148982307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4640395420904838127905637 870074141419657148982307)
                    ·
                      rfl

theorem cell23_5083390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_5083390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083390 prefixEnd_5083390 := by exact prefixLift 5083390
  have htrace : WordTrace (prefixWord ++ tailWord_5083390) baseStart_5083390 baseEnd_5083390 := by
    simpa [prefixWord, tailWord_5083390, baseEnd_5083390] using wordTrace_append hprefix tailTrace_5083390
  have hstable : (prefixWord ++ tailWord_5083390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083390).length < 2 ^ (prefixWord ++ tailWord_5083390).sum := by decide
  have hdescent : baseEnd_5083390 < baseStart_5083390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083437 : List Nat := [1, 5, 3, 1, 3, 1, 9]
def baseStart_5083437 : Nat := 118140960795 + 5083437 * 2 ^ 59
def prefixEnd_5083437 : Nat := 4983230072969 + 3 ^ 40 * 5083437 * 2
def baseEnd_5083437 : Nat := 32225266146292997074805

theorem tailTrace_5083437 : CollatzResearch.WordTrace tailWord_5083437 prefixEnd_5083437 32225266146292997074805 := by
  unfold tailWord_5083437
  simp only [CollatzResearch.WordTrace]
  refine ⟨185408179284583405765216565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123605452856388937176811043 185408179284583405765216565)
  ·
    refine ⟨17382016807929694290489053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185408179284583405765216565 17382016807929694290489053)
    ·
      refine ⟨6518256302973635358933395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17382016807929694290489053 6518256302973635358933395)
      ·
        refine ⟨9777384454460453038400093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6518256302973635358933395 9777384454460453038400093)
        ·
          refine ⟨3666519170422669889400035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9777384454460453038400093 3666519170422669889400035)
          ·
            refine ⟨5499778755634004834100053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666519170422669889400035 5499778755634004834100053)
            ·
              refine ⟨32225266146292997074805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5499778755634004834100053 32225266146292997074805)
              ·
                rfl

theorem cell23_5083437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 9].length) (baseStart_5083437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083437 prefixEnd_5083437 := by exact prefixLift 5083437
  have htrace : WordTrace (prefixWord ++ tailWord_5083437) baseStart_5083437 baseEnd_5083437 := by
    simpa [prefixWord, tailWord_5083437, baseEnd_5083437] using wordTrace_append hprefix tailTrace_5083437
  have hstable : (prefixWord ++ tailWord_5083437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083437).length < 2 ^ (prefixWord ++ tailWord_5083437).sum := by decide
  have hdescent : baseEnd_5083437 < baseStart_5083437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083473 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_5083473 : Nat := 118140960795 + 5083473 * 2 ^ 59
def prefixEnd_5083473 : Nat := 4983230072969 + 3 ^ 40 * 5083473 * 2
def baseEnd_5083473 : Nat := 2610265043153294622209039

theorem tailTrace_5083473 : CollatzResearch.WordTrace tailWord_5083473 prefixEnd_5083473 2610265043153294622209039 := by
  unfold tailWord_5083473
  simp only [CollatzResearch.WordTrace]
  refine ⟨185409492312452983913527073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123606328208301989275684715 185409492312452983913527073)
  ·
    refine ⟨139057119234339737935145305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185409492312452983913527073 139057119234339737935145305)
    ·
      refine ⟨104292839425754803451358979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139057119234339737935145305 104292839425754803451358979)
      ·
        refine ⟨156439259138632205177038469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104292839425754803451358979 156439259138632205177038469)
        ·
          refine ⟨29332361088493538470694713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156439259138632205177038469 29332361088493538470694713)
          ·
            refine ⟨21999270816370153853021035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29332361088493538470694713 21999270816370153853021035)
            ·
              refine ⟨32998906224555230779531553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21999270816370153853021035 32998906224555230779531553)
              ·
                refine ⟨24749179668416423084648665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32998906224555230779531553 24749179668416423084648665)
                ·
                  refine ⟨18561884751312317313486499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24749179668416423084648665 18561884751312317313486499)
                  ·
                    refine ⟨27842827126968475970229749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18561884751312317313486499 27842827126968475970229749)
                    ·
                      refine ⟨2610265043153294622209039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27842827126968475970229749 2610265043153294622209039)
                      ·
                        rfl

theorem cell23_5083473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_5083473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083473 prefixEnd_5083473 := by exact prefixLift 5083473
  have htrace : WordTrace (prefixWord ++ tailWord_5083473) baseStart_5083473 baseEnd_5083473 := by
    simpa [prefixWord, tailWord_5083473, baseEnd_5083473] using wordTrace_append hprefix tailTrace_5083473
  have hstable : (prefixWord ++ tailWord_5083473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083473).length < 2 ^ (prefixWord ++ tailWord_5083473).sum := by decide
  have hdescent : baseEnd_5083473 < baseStart_5083473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083490 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5083490 : Nat := 118140960795 + 5083490 * 2 ^ 59
def prefixEnd_5083490 : Nat := 4983230072969 + 3 ^ 40 * 5083490 * 2
def baseEnd_5083490 : Nat := 2610273772324421055696461

theorem tailTrace_5083490 : CollatzResearch.WordTrace tailWord_5083490 prefixEnd_5083490 2610273772324421055696461 := by
  unfold tailWord_5083490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46352528088347848954223981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123606741568927597211263949 46352528088347848954223981)
  ·
    refine ⟨17382198033130443357833993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46352528088347848954223981 17382198033130443357833993)
    ·
      refine ⟨13036648524847832518375495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17382198033130443357833993 13036648524847832518375495)
      ·
        refine ⟨19554972787271748777563243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036648524847832518375495 19554972787271748777563243)
        ·
          refine ⟨29332459180907623166344865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19554972787271748777563243 29332459180907623166344865)
          ·
            refine ⟨21999344385680717374758649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29332459180907623166344865 21999344385680717374758649)
            ·
              refine ⟨16499508289260538031068987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21999344385680717374758649 16499508289260538031068987)
              ·
                refine ⟨24749262433890807046603481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16499508289260538031068987 24749262433890807046603481)
                ·
                  refine ⟨18561946825418105284952611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24749262433890807046603481 18561946825418105284952611)
                  ·
                    refine ⟨27842920238127157927428917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18561946825418105284952611 27842920238127157927428917)
                    ·
                      refine ⟨2610273772324421055696461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27842920238127157927428917 2610273772324421055696461)
                      ·
                        rfl

theorem cell23_5083490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5083490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083490 prefixEnd_5083490 := by exact prefixLift 5083490
  have htrace : WordTrace (prefixWord ++ tailWord_5083490) baseStart_5083490 baseEnd_5083490 := by
    simpa [prefixWord, tailWord_5083490, baseEnd_5083490] using wordTrace_append hprefix tailTrace_5083490
  have hstable : (prefixWord ++ tailWord_5083490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083490).length < 2 ^ (prefixWord ++ tailWord_5083490).sum := by decide
  have hdescent : baseEnd_5083490 < baseStart_5083490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083504 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 2, 2, 2]
def baseStart_5083504 : Nat := 118140960795 + 5083504 * 2 ^ 59
def prefixEnd_5083504 : Nat := 4983230072969 + 3 ^ 40 * 5083504 * 2
def baseEnd_5083504 : Nat := 2610280961053584000921397

theorem tailTrace_5083504 : CollatzResearch.WordTrace tailWord_5083504 prefixEnd_5083504 2610280961053584000921397 := by
  unfold tailWord_5083504
  simp only [CollatzResearch.WordTrace]
  refine ⟨92705311487670338103952783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123607081983560450805270377 92705311487670338103952783)
  ·
    refine ⟨139057967231505507155929175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92705311487670338103952783 139057967231505507155929175)
    ·
      refine ⟨208586950847258260733893763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139057967231505507155929175 208586950847258260733893763)
      ·
        refine ⟨312880426270887391100840645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208586950847258260733893763 312880426270887391100840645)
        ·
          refine ⟨58665079925791385831407621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312880426270887391100840645 58665079925791385831407621)
          ·
            refine ⟨10999702486085884843388929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58665079925791385831407621 10999702486085884843388929)
            ·
              refine ⟨8249776864564413632541697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10999702486085884843388929 8249776864564413632541697)
              ·
                refine ⟨6187332648423310224406273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8249776864564413632541697 6187332648423310224406273)
                ·
                  refine ⟨4640499486317482668304705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6187332648423310224406273 4640499486317482668304705)
                  ·
                    refine ⟨3480374614738112001228529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4640499486317482668304705 3480374614738112001228529)
                    ·
                      refine ⟨2610280961053584000921397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480374614738112001228529 2610280961053584000921397)
                      ·
                        rfl

theorem cell23_5083504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 2, 2].length) (baseStart_5083504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083504 prefixEnd_5083504 := by exact prefixLift 5083504
  have htrace : WordTrace (prefixWord ++ tailWord_5083504) baseStart_5083504 baseEnd_5083504 := by
    simpa [prefixWord, tailWord_5083504, baseEnd_5083504] using wordTrace_append hprefix tailTrace_5083504
  have hstable : (prefixWord ++ tailWord_5083504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083504).length < 2 ^ (prefixWord ++ tailWord_5083504).sum := by decide
  have hdescent : baseEnd_5083504 < baseStart_5083504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083542 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5083542 : Nat := 118140960795 + 5083542 * 2 ^ 59
def prefixEnd_5083542 : Nat := 4983230072969 + 3 ^ 40 * 5083542 * 2
def baseEnd_5083542 : Nat := 2610300473318454852246223

theorem tailTrace_5083542 : CollatzResearch.WordTrace tailWord_5083542 prefixEnd_5083542 2610300473318454852246223 := by
  unfold tailWord_5083542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588250559325188043611805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123608005966135339131859253 11588250559325188043611805)
  ·
    refine ⟨4345593959746945516354427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11588250559325188043611805 4345593959746945516354427)
    ·
      refine ⟨6518390939620418274531641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4345593959746945516354427 6518390939620418274531641)
      ·
        refine ⟨4888793204715313705898731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6518390939620418274531641 4888793204715313705898731)
        ·
          refine ⟨7333189807072970558848097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888793204715313705898731 7333189807072970558848097)
          ·
            refine ⟨5499892355304727919136073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7333189807072970558848097 5499892355304727919136073)
            ·
              refine ⟨4124919266478545939352055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499892355304727919136073 4124919266478545939352055)
              ·
                refine ⟨6187378899717818909028083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124919266478545939352055 6187378899717818909028083)
                ·
                  refine ⟨9281068349576728363542125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6187378899717818909028083 9281068349576728363542125)
                  ·
                    refine ⟨3480400631091273136328297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9281068349576728363542125 3480400631091273136328297)
                    ·
                      refine ⟨2610300473318454852246223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480400631091273136328297 2610300473318454852246223)
                      ·
                        rfl

theorem cell23_5083542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5083542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083542 prefixEnd_5083542 := by exact prefixLift 5083542
  have htrace : WordTrace (prefixWord ++ tailWord_5083542) baseStart_5083542 baseEnd_5083542 := by
    simpa [prefixWord, tailWord_5083542, baseEnd_5083542] using wordTrace_append hprefix tailTrace_5083542
  have hstable : (prefixWord ++ tailWord_5083542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083542).length < 2 ^ (prefixWord ++ tailWord_5083542).sum := by decide
  have hdescent : baseEnd_5083542 < baseStart_5083542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083577 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 2, 4, 2]
def baseStart_5083577 : Nat := 118140960795 + 5083577 * 2 ^ 59
def prefixEnd_5083577 : Nat := 4983230072969 + 3 ^ 40 * 5083577 * 2
def baseEnd_5083577 : Nat := 2610318445141362215308561

theorem tailTrace_5083577 : CollatzResearch.WordTrace tailWord_5083577 prefixEnd_5083577 2610318445141362215308561 := by
  unfold tailWord_5083577
  simp only [CollatzResearch.WordTrace]
  refine ⟨185413285504076209675312985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123608857002717473116875323 185413285504076209675312985)
  ·
    refine ⟨139059964128057157256484739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185413285504076209675312985 139059964128057157256484739)
    ·
      refine ⟨208589946192085735884727109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139059964128057157256484739 208589946192085735884727109)
      ·
        refine ⟨39110614911016075478386333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208589946192085735884727109 39110614911016075478386333)
        ·
          refine ⟨14666480591631028304394875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39110614911016075478386333 14666480591631028304394875)
          ·
            refine ⟨21999720887446542456592313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14666480591631028304394875 21999720887446542456592313)
            ·
              refine ⟨16499790665584906842444235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21999720887446542456592313 16499790665584906842444235)
              ·
                refine ⟨24749685998377360263666353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16499790665584906842444235 24749685998377360263666353)
                ·
                  refine ⟨18562264498783020197749765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24749685998377360263666353 18562264498783020197749765)
                  ·
                    refine ⟨3480424593521816287078081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18562264498783020197749765 3480424593521816287078081)
                    ·
                      refine ⟨2610318445141362215308561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3480424593521816287078081 2610318445141362215308561)
                      ·
                        rfl

theorem cell23_5083577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_5083577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083577 prefixEnd_5083577 := by exact prefixLift 5083577
  have htrace : WordTrace (prefixWord ++ tailWord_5083577) baseStart_5083577 baseEnd_5083577 := by
    simpa [prefixWord, tailWord_5083577, baseEnd_5083577] using wordTrace_append hprefix tailTrace_5083577
  have hstable : (prefixWord ++ tailWord_5083577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083577).length < 2 ^ (prefixWord ++ tailWord_5083577).sum := by decide
  have hdescent : baseEnd_5083577 < baseStart_5083577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083621 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_5083621 : Nat := 118140960795 + 5083621 * 2 ^ 59
def prefixEnd_5083621 : Nat := 4983230072969 + 3 ^ 40 * 5083621 * 2
def baseEnd_5083621 : Nat := 870113679430053347719453

theorem tailTrace_5083621 : CollatzResearch.WordTrace tailWord_5083621 prefixEnd_5083621 870113679430053347719453 := by
  unfold tailWord_5083621
  simp only [CollatzResearch.WordTrace]
  refine ⟨185414890315916805189914717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123609926877277870126609811 185414890315916805189914717)
  ·
    refine ⟨69530583868468801946218019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185414890315916805189914717 69530583868468801946218019)
    ·
      refine ⟨104295875802703202919327029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69530583868468801946218019 104295875802703202919327029)
      ·
        refine ⟨9777738356503425273686909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104295875802703202919327029 9777738356503425273686909)
        ·
          refine ⟨3666651883688784477632591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9777738356503425273686909 3666651883688784477632591)
          ·
            refine ⟨5499977825533176716448887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666651883688784477632591 5499977825533176716448887)
            ·
              refine ⟨8249966738299765074673331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499977825533176716448887 8249966738299765074673331)
              ·
                refine ⟨12374950107449647612009997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8249966738299765074673331 12374950107449647612009997)
                ·
                  refine ⟨4640606290293617854503749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12374950107449647612009997 4640606290293617854503749)
                  ·
                    refine ⟨870113679430053347719453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4640606290293617854503749 870113679430053347719453)
                    ·
                      rfl

theorem cell23_5083621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_5083621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083621 prefixEnd_5083621 := by exact prefixLift 5083621
  have htrace : WordTrace (prefixWord ++ tailWord_5083621) baseStart_5083621 baseEnd_5083621 := by
    simpa [prefixWord, tailWord_5083621, baseEnd_5083621] using wordTrace_append hprefix tailTrace_5083621
  have hstable : (prefixWord ++ tailWord_5083621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083621).length < 2 ^ (prefixWord ++ tailWord_5083621).sum := by decide
  have hdescent : baseEnd_5083621 < baseStart_5083621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083660 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_5083660 : Nat := 118140960795 + 5083660 * 2 ^ 59
def prefixEnd_5083660 : Nat := 4983230072969 + 3 ^ 40 * 5083660 * 2
def baseEnd_5083660 : Nat := 870120354678561796856893

theorem tailTrace_5083660 : CollatzResearch.WordTrace tailWord_5083660 prefixEnd_5083660 870120354678561796856893 := by
  unfold tailWord_5083660
  simp only [CollatzResearch.WordTrace]
  refine ⟨92708156381387757425292217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123610875175183676567056289 92708156381387757425292217)
  ·
    refine ⟨69531117286040818068969163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92708156381387757425292217 69531117286040818068969163)
    ·
      refine ⟨104296675929061227103453745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69531117286040818068969163 104296675929061227103453745)
      ·
        refine ⟨78222506946795920327590309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104296675929061227103453745 78222506946795920327590309)
        ·
          refine ⟨14666720052524235061423183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78222506946795920327590309 14666720052524235061423183)
          ·
            refine ⟨22000080078786352592134775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14666720052524235061423183 22000080078786352592134775)
            ·
              refine ⟨33000120118179528888202163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22000080078786352592134775 33000120118179528888202163)
              ·
                refine ⟨49500180177269293332303245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33000120118179528888202163 49500180177269293332303245)
                ·
                  refine ⟨18562567566475984999613717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49500180177269293332303245 18562567566475984999613717)
                  ·
                    refine ⟨870120354678561796856893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18562567566475984999613717 870120354678561796856893)
                    ·
                      rfl

theorem cell23_5083660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_5083660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083660 prefixEnd_5083660 := by exact prefixLift 5083660
  have htrace : WordTrace (prefixWord ++ tailWord_5083660) baseStart_5083660 baseEnd_5083660 := by
    simpa [prefixWord, tailWord_5083660, baseEnd_5083660] using wordTrace_append hprefix tailTrace_5083660
  have hstable : (prefixWord ++ tailWord_5083660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083660).length < 2 ^ (prefixWord ++ tailWord_5083660).sum := by decide
  have hdescent : baseEnd_5083660 < baseStart_5083660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5083694 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5083694 : Nat := 118140960795 + 5083694 * 2 ^ 59
def prefixEnd_5083694 : Nat := 4983230072969 + 3 ^ 40 * 5083694 * 2
def baseEnd_5083694 : Nat := 870126174125979419181841

theorem tailTrace_5083694 : CollatzResearch.WordTrace tailWord_5083694 prefixEnd_5083694 870126174125979419181841 := by
  unfold tailWord_5083694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23177194105581542332165267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123611701896434892438214757 23177194105581542332165267)
  ·
    refine ⟨34765791158372313498247901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23177194105581542332165267 34765791158372313498247901)
    ·
      refine ⟨13037171684389617561842963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34765791158372313498247901 13037171684389617561842963)
      ·
        refine ⟨19555757526584426342764445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13037171684389617561842963 19555757526584426342764445)
        ·
          refine ⟨7333409072469159878536667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19555757526584426342764445 7333409072469159878536667)
          ·
            refine ⟨11000113608703739817805001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7333409072469159878536667 11000113608703739817805001)
            ·
              refine ⟨8250085206527804863353751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11000113608703739817805001 8250085206527804863353751)
              ·
                refine ⟨12375127809791707295030627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250085206527804863353751 12375127809791707295030627)
                ·
                  refine ⟨18562691714687560942545941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12375127809791707295030627 18562691714687560942545941)
                  ·
                    refine ⟨870126174125979419181841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18562691714687560942545941 870126174125979419181841)
                    ·
                      rfl

theorem cell23_5083694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5083694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5083694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5083694 prefixEnd_5083694 := by exact prefixLift 5083694
  have htrace : WordTrace (prefixWord ++ tailWord_5083694) baseStart_5083694 baseEnd_5083694 := by
    simpa [prefixWord, tailWord_5083694, baseEnd_5083694] using wordTrace_append hprefix tailTrace_5083694
  have hstable : (prefixWord ++ tailWord_5083694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5083694).length < 2 ^ (prefixWord ++ tailWord_5083694).sum := by decide
  have hdescent : baseEnd_5083694 < baseStart_5083694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5083694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
