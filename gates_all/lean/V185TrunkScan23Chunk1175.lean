import V185TrunkScan23Chunk1174

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6961515 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 3]
def baseStart_6961515 : Nat := 118140960795 + 6961515 * 2 ^ 59
def prefixEnd_6961515 : Nat := 4983230072969 + 3 ^ 40 * 6961515 * 2
def baseEnd_6961515 : Nat := 3574603278484435774247081

theorem tailTrace_6961515 : CollatzResearch.WordTrace tailWord_6961515 prefixEnd_6961515 3574603278484435774247081 := by
  unfold tailWord_6961515
  simp only [CollatzResearch.WordTrace]
  refine ⟨253907311374627561951389999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169271540916418374634259999 253907311374627561951389999)
  ·
    refine ⟨380860967061941342927084999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253907311374627561951389999 380860967061941342927084999)
    ·
      refine ⟨571291450592912014390627499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380860967061941342927084999 571291450592912014390627499)
      ·
        refine ⟨856937175889368021585941249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571291450592912014390627499 856937175889368021585941249)
        ·
          refine ⟨642702881917026016189455937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856937175889368021585941249 642702881917026016189455937)
          ·
            refine ⟨482027161437769512142091953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642702881917026016189455937 482027161437769512142091953)
            ·
              refine ⟨361520371078327134106568965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482027161437769512142091953 361520371078327134106568965)
              ·
                refine ⟨67785069577186337644981681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361520371078327134106568965 67785069577186337644981681)
                ·
                  refine ⟨50838802182889753233736261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67785069577186337644981681 50838802182889753233736261)
                  ·
                    refine ⟨9532275409291828731325549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50838802182889753233736261 9532275409291828731325549)
                    ·
                      refine ⟨3574603278484435774247081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532275409291828731325549 3574603278484435774247081)
                      ·
                        rfl

theorem cell23_6961515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 3].length) (baseStart_6961515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961515 prefixEnd_6961515 := by exact prefixLift 6961515
  have htrace : WordTrace (prefixWord ++ tailWord_6961515) baseStart_6961515 baseEnd_6961515 := by
    simpa [prefixWord, tailWord_6961515, baseEnd_6961515] using wordTrace_append hprefix tailTrace_6961515
  have hstable : (prefixWord ++ tailWord_6961515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961515).length < 2 ^ (prefixWord ++ tailWord_6961515).sum := by decide
  have hdescent : baseEnd_6961515 < baseStart_6961515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961562 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_6961562 : Nat := 118140960795 + 6961562 * 2 ^ 59
def prefixEnd_6961562 : Nat := 4983230072969 + 3 ^ 40 * 6961562 * 2
def baseEnd_6961562 : Nat := 3574627412075197090359365

theorem tailTrace_6961562 : CollatzResearch.WordTrace tailWord_6961562 prefixEnd_6961562 3574627412075197090359365 := by
  unfold tailWord_6961562
  simp only [CollatzResearch.WordTrace]
  refine ⟨63477256401364322244587735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169272683736971525985567293 63477256401364322244587735)
  ·
    refine ⟨95215884602046483366881603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63477256401364322244587735 95215884602046483366881603)
    ·
      refine ⟨142823826903069725050322405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95215884602046483366881603 142823826903069725050322405)
      ·
        refine ⟨26779467544325573446935451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142823826903069725050322405 26779467544325573446935451)
        ·
          refine ⟨40169201316488360170403177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26779467544325573446935451 40169201316488360170403177)
          ·
            refine ⟨30126900987366270127802383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40169201316488360170403177 30126900987366270127802383)
            ·
              refine ⟨45190351481049405191703575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30126900987366270127802383 45190351481049405191703575)
              ·
                refine ⟨67785527221574107787555363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45190351481049405191703575 67785527221574107787555363)
                ·
                  refine ⟨101678290832361161681333045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67785527221574107787555363 101678290832361161681333045)
                  ·
                    refine ⟨9532339765533858907624973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101678290832361161681333045 9532339765533858907624973)
                    ·
                      refine ⟨3574627412075197090359365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532339765533858907624973 3574627412075197090359365)
                      ·
                        rfl

theorem cell23_6961562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_6961562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961562 prefixEnd_6961562 := by exact prefixLift 6961562
  have htrace : WordTrace (prefixWord ++ tailWord_6961562) baseStart_6961562 baseEnd_6961562 := by
    simpa [prefixWord, tailWord_6961562, baseEnd_6961562] using wordTrace_append hprefix tailTrace_6961562
  have hstable : (prefixWord ++ tailWord_6961562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961562).length < 2 ^ (prefixWord ++ tailWord_6961562).sum := by decide
  have hdescent : baseEnd_6961562 < baseStart_6961562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961569 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 7]
def baseStart_6961569 : Nat := 118140960795 + 6961569 * 2 ^ 59
def prefixEnd_6961569 : Nat := 4983230072969 + 3 ^ 40 * 6961569 * 2
def baseEnd_6961569 : Nat := 397181222937753173663537

theorem tailTrace_6961569 : CollatzResearch.WordTrace tailWord_6961569 prefixEnd_6961569 397181222937753173663537 := by
  unfold tailWord_6961569
  simp only [CollatzResearch.WordTrace]
  refine ⟨253909280916431929173855761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169272853944287952782570507 253909280916431929173855761)
  ·
    refine ⟨190431960687323946880391821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253909280916431929173855761 190431960687323946880391821)
    ·
      refine ⟨71411985257746480080146933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190431960687323946880391821 71411985257746480080146933)
      ·
        refine ⟨6694873617913732507513775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71411985257746480080146933 6694873617913732507513775)
        ·
          refine ⟨10042310426870598761270663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6694873617913732507513775 10042310426870598761270663)
          ·
            refine ⟨15063465640305898141905995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10042310426870598761270663 15063465640305898141905995)
            ·
              refine ⟨22595198460458847212858993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15063465640305898141905995 22595198460458847212858993)
              ·
                refine ⟨16946398845344135409644245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22595198460458847212858993 16946398845344135409644245)
                ·
                  refine ⟨397181222937753173663537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16946398845344135409644245 397181222937753173663537)
                  ·
                    rfl

theorem cell23_6961569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 7].length) (baseStart_6961569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961569 prefixEnd_6961569 := by exact prefixLift 6961569
  have htrace : WordTrace (prefixWord ++ tailWord_6961569) baseStart_6961569 baseEnd_6961569 := by
    simpa [prefixWord, tailWord_6961569, baseEnd_6961569] using wordTrace_append hprefix tailTrace_6961569
  have hstable : (prefixWord ++ tailWord_6961569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961569).length < 2 ^ (prefixWord ++ tailWord_6961569).sum := by decide
  have hdescent : baseEnd_6961569 < baseStart_6961569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961615 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_6961615 : Nat := 118140960795 + 6961615 * 2 ^ 59
def prefixEnd_6961615 : Nat := 4983230072969 + 3 ^ 40 * 6961615 * 2
def baseEnd_6961615 : Nat := 3574654626549885382996621

theorem tailTrace_6961615 : CollatzResearch.WordTrace tailWord_6961615 prefixEnd_6961615 3574654626549885382996621 := by
  unfold tailWord_6961615
  simp only [CollatzResearch.WordTrace]
  refine ⟨253910958674265279030030299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169273972449510186020020199 253910958674265279030030299)
  ·
    refine ⟨380866438011397918545045449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253910958674265279030030299 380866438011397918545045449)
    ·
      refine ⟨285649828508548438908784087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380866438011397918545045449 285649828508548438908784087)
      ·
        refine ⟨428474742762822658363176131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285649828508548438908784087 428474742762822658363176131)
        ·
          refine ⟨642712114144233987544764197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428474742762822658363176131 642712114144233987544764197)
          ·
            refine ⟨120508521402043872664643287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 642712114144233987544764197 120508521402043872664643287)
            ·
              refine ⟨180762782103065808996964931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120508521402043872664643287 180762782103065808996964931)
              ·
                refine ⟨271144173154598713495447397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180762782103065808996964931 271144173154598713495447397)
                ·
                  refine ⟨50839532466487258780396387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271144173154598713495447397 50839532466487258780396387)
                  ·
                    refine ⟨76259298699730888170594581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50839532466487258780396387 76259298699730888170594581)
                    ·
                      refine ⟨3574654626549885382996621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76259298699730888170594581 3574654626549885382996621)
                      ·
                        rfl

theorem cell23_6961615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_6961615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961615 prefixEnd_6961615 := by exact prefixLift 6961615
  have htrace : WordTrace (prefixWord ++ tailWord_6961615) baseStart_6961615 baseEnd_6961615 := by
    simpa [prefixWord, tailWord_6961615, baseEnd_6961615] using wordTrace_append hprefix tailTrace_6961615
  have hstable : (prefixWord ++ tailWord_6961615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961615).length < 2 ^ (prefixWord ++ tailWord_6961615).sum := by decide
  have hdescent : baseEnd_6961615 < baseStart_6961615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961629 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6961629 : Nat := 118140960795 + 6961629 * 2 ^ 59
def prefixEnd_6961629 : Nat := 4983230072969 + 3 ^ 40 * 6961629 * 2
def baseEnd_6961629 : Nat := 1191553938426349442740519

theorem tailTrace_6961629 : CollatzResearch.WordTrace tailWord_6961629 prefixEnd_6961629 1191553938426349442740519 := by
  unfold tailWord_6961629
  simp only [CollatzResearch.WordTrace]
  refine ⟨253911469296214559421039941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169274312864143039614026627 253911469296214559421039941)
  ·
    refine ⟨47608400493040229891444989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253911469296214559421039941 47608400493040229891444989)
    ·
      refine ⟨17853150184890086209291871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47608400493040229891444989 17853150184890086209291871)
      ·
        refine ⟨26779725277335129313937807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17853150184890086209291871 26779725277335129313937807)
        ·
          refine ⟨40169587916002693970906711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26779725277335129313937807 40169587916002693970906711)
          ·
            refine ⟨60254381874004040956360067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40169587916002693970906711 60254381874004040956360067)
            ·
              refine ⟨90381572811006061434540101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60254381874004040956360067 90381572811006061434540101)
              ·
                refine ⟨16946544902063636518976269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90381572811006061434540101 16946544902063636518976269)
                ·
                  refine ⟨6354954338273863694616101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16946544902063636518976269 6354954338273863694616101)
                  ·
                    refine ⟨1191553938426349442740519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6354954338273863694616101 1191553938426349442740519)
                    ·
                      rfl

theorem cell23_6961629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6961629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961629 prefixEnd_6961629 := by exact prefixLift 6961629
  have htrace : WordTrace (prefixWord ++ tailWord_6961629) baseStart_6961629 baseEnd_6961629 := by
    simpa [prefixWord, tailWord_6961629, baseEnd_6961629] using wordTrace_append hprefix tailTrace_6961629
  have hstable : (prefixWord ++ tailWord_6961629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961629).length < 2 ^ (prefixWord ++ tailWord_6961629).sum := by decide
  have hdescent : baseEnd_6961629 < baseStart_6961629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961639 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_6961639 : Nat := 118140960795 + 6961639 * 2 ^ 59
def prefixEnd_6961639 : Nat := 4983230072969 + 3 ^ 40 * 6961639 * 2
def baseEnd_6961639 : Nat := 3574666950085593289096511

theorem tailTrace_6961639 : CollatzResearch.WordTrace tailWord_6961639 prefixEnd_6961639 3574666950085593289096511 := by
  unfold tailWord_6961639
  simp only [CollatzResearch.WordTrace]
  refine ⟨253911834026178331128903971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169274556017452220752602647 253911834026178331128903971)
  ·
    refine ⟨380867751039267496693355957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253911834026178331128903971 380867751039267496693355957)
    ·
      refine ⟨35706351659931327815002121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 380867751039267496693355957 35706351659931327815002121)
      ·
        refine ⟨26779763744948495861251591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35706351659931327815002121 26779763744948495861251591)
        ·
          refine ⟨40169645617422743791877387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26779763744948495861251591 40169645617422743791877387)
          ·
            refine ⟨60254468426134115687816081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40169645617422743791877387 60254468426134115687816081)
            ·
              refine ⟨45190851319600586765862061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60254468426134115687816081 45190851319600586765862061)
              ·
                refine ⟨16946569244850220037198273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45190851319600586765862061 16946569244850220037198273)
                ·
                  refine ⟨12709926933637665027898705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16946569244850220037198273 12709926933637665027898705)
                  ·
                    refine ⟨9532445200228248770924029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12709926933637665027898705 9532445200228248770924029)
                    ·
                      refine ⟨3574666950085593289096511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532445200228248770924029 3574666950085593289096511)
                      ·
                        rfl

theorem cell23_6961639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_6961639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961639 prefixEnd_6961639 := by exact prefixLift 6961639
  have htrace : WordTrace (prefixWord ++ tailWord_6961639) baseStart_6961639 baseEnd_6961639 := by
    simpa [prefixWord, tailWord_6961639, baseEnd_6961639] using wordTrace_append hprefix tailTrace_6961639
  have hstable : (prefixWord ++ tailWord_6961639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961639).length < 2 ^ (prefixWord ++ tailWord_6961639).sum := by decide
  have hdescent : baseEnd_6961639 < baseStart_6961639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961642 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_6961642 : Nat := 118140960795 + 6961642 * 2 ^ 59
def prefixEnd_6961642 : Nat := 4983230072969 + 3 ^ 40 * 6961642 * 2
def baseEnd_6961642 : Nat := 397185387836395197484333

theorem tailTrace_6961642 : CollatzResearch.WordTrace tailWord_6961642 prefixEnd_6961642 397185387836395197484333 := by
  unfold tailWord_6961642
  simp only [CollatzResearch.WordTrace]
  refine ⟨63477985861291865660315795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169274628963444975094175453 63477985861291865660315795)
  ·
    refine ⟨95216978791937798490473693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63477985861291865660315795 95216978791937798490473693)
    ·
      refine ⟨35706367046976674433927635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95216978791937798490473693 35706367046976674433927635)
      ·
        refine ⟨53559550570465011650891453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35706367046976674433927635 53559550570465011650891453)
        ·
          refine ⟨20084831463924379369084295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53559550570465011650891453 20084831463924379369084295)
          ·
            refine ⟨30127247195886569053626443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20084831463924379369084295 30127247195886569053626443)
            ·
              refine ⟨45190870793829853580439665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30127247195886569053626443 45190870793829853580439665)
              ·
                refine ⟨33893153095372390185329749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45190870793829853580439665 33893153095372390185329749)
                ·
                  refine ⟨397185387836395197484333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33893153095372390185329749 397185387836395197484333)
                  ·
                    rfl

theorem cell23_6961642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_6961642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961642 prefixEnd_6961642 := by exact prefixLift 6961642
  have htrace : WordTrace (prefixWord ++ tailWord_6961642) baseStart_6961642 baseEnd_6961642 := by
    simpa [prefixWord, tailWord_6961642, baseEnd_6961642] using wordTrace_append hprefix tailTrace_6961642
  have hstable : (prefixWord ++ tailWord_6961642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961642).length < 2 ^ (prefixWord ++ tailWord_6961642).sum := by decide
  have hdescent : baseEnd_6961642 < baseStart_6961642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961655 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 11]
def baseStart_6961655 : Nat := 118140960795 + 6961655 * 2 ^ 59
def prefixEnd_6961655 : Nat := 4983230072969 + 3 ^ 40 * 6961655 * 2
def baseEnd_6961655 : Nat := 1191558388592021742165479

theorem tailTrace_6961655 : CollatzResearch.WordTrace tailWord_6961655 prefixEnd_6961655 1191558388592021742165479 := by
  unfold tailWord_6961655
  simp only [CollatzResearch.WordTrace]
  refine ⟨253912417594120365861486419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169274945062746910574324279 253912417594120365861486419)
  ·
    refine ⟨380868626391180548792229629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253912417594120365861486419 380868626391180548792229629)
    ·
      refine ⟨142825734896692705797086111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380868626391180548792229629 142825734896692705797086111)
      ·
        refine ⟨214238602345039058695629167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142825734896692705797086111 214238602345039058695629167)
        ·
          refine ⟨321357903517558588043443751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214238602345039058695629167 321357903517558588043443751)
          ·
            refine ⟨482036855276337882065165627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321357903517558588043443751 482036855276337882065165627)
            ·
              refine ⟨723055282914506823097748441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482036855276337882065165627 723055282914506823097748441)
              ·
                refine ⟨542291462185880117323311331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723055282914506823097748441 542291462185880117323311331)
                ·
                  refine ⟨813437193278820175984966997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542291462185880117323311331 813437193278820175984966997)
                  ·
                    refine ⟨1191558388592021742165479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 813437193278820175984966997 1191558388592021742165479)
                    ·
                      rfl

theorem cell23_6961655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_6961655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961655 prefixEnd_6961655 := by exact prefixLift 6961655
  have htrace : WordTrace (prefixWord ++ tailWord_6961655) baseStart_6961655 baseEnd_6961655 := by
    simpa [prefixWord, tailWord_6961655, baseEnd_6961655] using wordTrace_append hprefix tailTrace_6961655
  have hstable : (prefixWord ++ tailWord_6961655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961655).length < 2 ^ (prefixWord ++ tailWord_6961655).sum := by decide
  have hdescent : baseEnd_6961655 < baseStart_6961655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961672 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_6961672 : Nat := 118140960795 + 6961672 * 2 ^ 59
def prefixEnd_6961672 : Nat := 4983230072969 + 3 ^ 40 * 6961672 * 2
def baseEnd_6961672 : Nat := 1191561298315730553327953

theorem tailTrace_6961672 : CollatzResearch.WordTrace tailWord_6961672 prefixEnd_6961672 1191561298315730553327953 := by
  unfold tailWord_6961672
  simp only [CollatzResearch.WordTrace]
  refine ⟨126956518817529388882427635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169275358423372518509903513 126956518817529388882427635)
  ·
    refine ⟨190434778226294083323641453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126956518817529388882427635 190434778226294083323641453)
    ·
      refine ⟨71413041834860281246365545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190434778226294083323641453 71413041834860281246365545)
      ·
        refine ⟨53559781376145210934774159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71413041834860281246365545 53559781376145210934774159)
        ·
          refine ⟨80339672064217816402161239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53559781376145210934774159 80339672064217816402161239)
          ·
            refine ⟨120509508096326724603241859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80339672064217816402161239 120509508096326724603241859)
            ·
              refine ⟨180764262144490086904862789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120509508096326724603241859 180764262144490086904862789)
              ·
                refine ⟨33893299152091891294661773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180764262144490086904862789 33893299152091891294661773)
                ·
                  refine ⟨12709987182034459235498165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33893299152091891294661773 12709987182034459235498165)
                  ·
                    refine ⟨1191561298315730553327953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12709987182034459235498165 1191561298315730553327953)
                    ·
                      rfl

theorem cell23_6961672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_6961672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961672 prefixEnd_6961672 := by exact prefixLift 6961672
  have htrace : WordTrace (prefixWord ++ tailWord_6961672) baseStart_6961672 baseEnd_6961672 := by
    simpa [prefixWord, tailWord_6961672, baseEnd_6961672] using wordTrace_append hprefix tailTrace_6961672
  have hstable : (prefixWord ++ tailWord_6961672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961672).length < 2 ^ (prefixWord ++ tailWord_6961672).sum := by decide
  have hdescent : baseEnd_6961672 < baseStart_6961672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961676 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 6]
def baseStart_6961676 : Nat := 118140960795 + 6961676 * 2 ^ 59
def prefixEnd_6961676 : Nat := 4983230072969 + 3 ^ 40 * 6961676 * 2
def baseEnd_6961676 : Nat := 397187327652201071592649

theorem tailTrace_6961676 : CollatzResearch.WordTrace tailWord_6961676 prefixEnd_6961676 397187327652201071592649 := by
  unfold tailWord_6961676
  simp only [CollatzResearch.WordTrace]
  refine ⟨126956591763522143224000441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169275455684696190965333921 126956591763522143224000441)
  ·
    refine ⟨95217443822641607418000331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126956591763522143224000441 95217443822641607418000331)
    ·
      refine ⟨142826165733962411127000497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95217443822641607418000331 142826165733962411127000497)
      ·
        refine ⟨107119624300471808345250373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142826165733962411127000497 107119624300471808345250373)
        ·
          refine ⟨20084929556338464064734445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107119624300471808345250373 20084929556338464064734445)
          ·
            refine ⟨7531848583626924024275417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20084929556338464064734445 7531848583626924024275417)
            ·
              refine ⟨5648886437720193018206563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7531848583626924024275417 5648886437720193018206563)
              ·
                refine ⟨8473329656580289527309845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648886437720193018206563 8473329656580289527309845)
                ·
                  refine ⟨397187327652201071592649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8473329656580289527309845 397187327652201071592649)
                  ·
                    rfl

theorem cell23_6961676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_6961676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961676 prefixEnd_6961676 := by exact prefixLift 6961676
  have htrace : WordTrace (prefixWord ++ tailWord_6961676) baseStart_6961676 baseEnd_6961676 := by
    simpa [prefixWord, tailWord_6961676, baseEnd_6961676] using wordTrace_append hprefix tailTrace_6961676
  have hstable : (prefixWord ++ tailWord_6961676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961676).length < 2 ^ (prefixWord ++ tailWord_6961676).sum := by decide
  have hdescent : baseEnd_6961676 < baseStart_6961676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961746 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_6961746 : Nat := 118140960795 + 6961746 * 2 ^ 59
def prefixEnd_6961746 : Nat := 4983230072969 + 3 ^ 40 * 6961746 * 2
def baseEnd_6961746 : Nat := 3574721892515624370458519

theorem tailTrace_6961746 : CollatzResearch.WordTrace tailWord_6961746 prefixEnd_6961746 3574721892515624370458519 := by
  unfold tailWord_6961746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63478934159197672100762273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169277157757860458935366061 63478934159197672100762273)
  ·
    refine ⟨47609200619398254075571705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63478934159197672100762273 47609200619398254075571705)
    ·
      refine ⟨35706900464548690556678779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47609200619398254075571705 35706900464548690556678779)
      ·
        refine ⟨53560350696823035835018169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35706900464548690556678779 53560350696823035835018169)
        ·
          refine ⟨40170263022617276876263627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53560350696823035835018169 40170263022617276876263627)
          ·
            refine ⟨60255394533925915314395441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40170263022617276876263627 60255394533925915314395441)
            ·
              refine ⟨45191545900444436485796581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60255394533925915314395441 45191545900444436485796581)
              ·
                refine ⟨8473414856333331841086859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45191545900444436485796581 8473414856333331841086859)
                ·
                  refine ⟨12710122284499997761630289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8473414856333331841086859 12710122284499997761630289)
                  ·
                    refine ⟨9532591713374998321222717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12710122284499997761630289 9532591713374998321222717)
                    ·
                      refine ⟨3574721892515624370458519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532591713374998321222717 3574721892515624370458519)
                      ·
                        rfl

theorem cell23_6961746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_6961746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961746 prefixEnd_6961746 := by exact prefixLift 6961746
  have htrace : WordTrace (prefixWord ++ tailWord_6961746) baseStart_6961746 baseEnd_6961746 := by
    simpa [prefixWord, tailWord_6961746, baseEnd_6961746] using wordTrace_append hprefix tailTrace_6961746
  have hstable : (prefixWord ++ tailWord_6961746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961746).length < 2 ^ (prefixWord ++ tailWord_6961746).sum := by decide
  have hdescent : baseEnd_6961746 < baseStart_6961746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961816 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 3, 4, 2]
def baseStart_6961816 : Nat := 118140960795 + 6961816 * 2 ^ 59
def prefixEnd_6961816 : Nat := 4983230072969 + 3 ^ 40 * 6961816 * 2
def baseEnd_6961816 : Nat := 3574757836161439096583197

theorem tailTrace_6961816 : CollatzResearch.WordTrace tailWord_6961816 prefixEnd_6961816 3574757836161439096583197 := by
  unfold tailWord_6961816
  simp only [CollatzResearch.WordTrace]
  refine ⟨126959144873268545179048651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169278859831024726905398201 126959144873268545179048651)
  ·
    refine ⟨190438717309902817768572977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126959144873268545179048651 190438717309902817768572977)
    ·
      refine ⟨142829037982427113326429733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190438717309902817768572977 142829037982427113326429733)
      ·
        refine ⟨26780444621705083748705575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142829037982427113326429733 26780444621705083748705575)
        ·
          refine ⟨40170666932557625623058363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26780444621705083748705575 40170666932557625623058363)
          ·
            refine ⟨60256000398836438434587545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40170666932557625623058363 60256000398836438434587545)
            ·
              refine ⟨45192000299127328825940659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60256000398836438434587545 45192000299127328825940659)
              ·
                refine ⟨67788000448690993238910989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45192000299127328825940659 67788000448690993238910989)
                ·
                  refine ⟨25420500168259122464591621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67788000448690993238910989 25420500168259122464591621)
                  ·
                    refine ⟨4766343781548585462110929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25420500168259122464591621 4766343781548585462110929)
                    ·
                      refine ⟨3574757836161439096583197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766343781548585462110929 3574757836161439096583197)
                      ·
                        rfl

theorem cell23_6961816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_6961816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961816 prefixEnd_6961816 := by exact prefixLift 6961816
  have htrace : WordTrace (prefixWord ++ tailWord_6961816) baseStart_6961816 baseEnd_6961816 := by
    simpa [prefixWord, tailWord_6961816, baseEnd_6961816] using wordTrace_append hprefix tailTrace_6961816
  have hstable : (prefixWord ++ tailWord_6961816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961816).length < 2 ^ (prefixWord ++ tailWord_6961816).sum := by decide
  have hdescent : baseEnd_6961816 < baseStart_6961816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961839 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 7]
def baseStart_6961839 : Nat := 118140960795 + 6961839 * 2 ^ 59
def prefixEnd_6961839 : Nat := 4983230072969 + 3 ^ 40 * 6961839 * 2
def baseEnd_6961839 : Nat := 397196627357388056288399

theorem tailTrace_6961839 : CollatzResearch.WordTrace tailWord_6961839 prefixEnd_6961839 397196627357388056288399 := by
  unfold tailWord_6961839
  simp only [CollatzResearch.WordTrace]
  refine ⟨253919128625453765286184571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169279419083635843524123047 253919128625453765286184571)
  ·
    refine ⟨380878692938180647929276857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253919128625453765286184571 380878692938180647929276857)
    ·
      refine ⟨285659019703635485946957643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380878692938180647929276857 285659019703635485946957643)
      ·
        refine ⟨428488529555453228920436465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285659019703635485946957643 428488529555453228920436465)
        ·
          refine ⟨321366397166589921690327349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428488529555453228920436465 321366397166589921690327349)
          ·
            refine ⟨30128099734367805158468189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321366397166589921690327349 30128099734367805158468189)
            ·
              refine ⟨11298037400387926934425571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30128099734367805158468189 11298037400387926934425571)
              ·
                refine ⟨16947056100581890401638357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11298037400387926934425571 16947056100581890401638357)
                ·
                  refine ⟨397196627357388056288399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16947056100581890401638357 397196627357388056288399)
                  ·
                    rfl

theorem cell23_6961839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 7].length) (baseStart_6961839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961839 prefixEnd_6961839 := by exact prefixLift 6961839
  have htrace : WordTrace (prefixWord ++ tailWord_6961839) baseStart_6961839 baseEnd_6961839 := by
    simpa [prefixWord, tailWord_6961839, baseEnd_6961839] using wordTrace_append hprefix tailTrace_6961839
  have hstable : (prefixWord ++ tailWord_6961839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961839).length < 2 ^ (prefixWord ++ tailWord_6961839).sum := by decide
  have hdescent : baseEnd_6961839 < baseStart_6961839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961849 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_6961849 : Nat := 118140960795 + 6961849 * 2 ^ 59
def prefixEnd_6961849 : Nat := 4983230072969 + 3 ^ 40 * 6961849 * 2
def baseEnd_6961849 : Nat := 3574774781023037467470545

theorem tailTrace_6961849 : CollatzResearch.WordTrace tailWord_6961849 prefixEnd_6961849 3574774781023037467470545 := by
  unfold tailWord_6961849
  simp only [CollatzResearch.WordTrace]
  refine ⟨253919493355417536994048601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169279662236945024662699067 253919493355417536994048601)
  ·
    refine ⟨190439620016563152745536451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253919493355417536994048601 190439620016563152745536451)
    ·
      refine ⟨285659430024844729118304677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190439620016563152745536451 285659430024844729118304677)
      ·
        refine ⟨53561143129658386709682127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285659430024844729118304677 53561143129658386709682127)
        ·
          refine ⟨80341714694487580064523191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53561143129658386709682127 80341714694487580064523191)
          ·
            refine ⟨120512572041731370096784787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80341714694487580064523191 120512572041731370096784787)
            ·
              refine ⟨180768858062597055145177181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120512572041731370096784787 180768858062597055145177181)
              ·
                refine ⟨67788321773473895679441443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180768858062597055145177181 67788321773473895679441443)
                ·
                  refine ⟨101682482660210843519162165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67788321773473895679441443 101682482660210843519162165)
                  ·
                    refine ⟨9532732749394766579921453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101682482660210843519162165 9532732749394766579921453)
                    ·
                      refine ⟨3574774781023037467470545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532732749394766579921453 3574774781023037467470545)
                      ·
                        rfl

theorem cell23_6961849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_6961849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961849 prefixEnd_6961849 := by exact prefixLift 6961849
  have htrace : WordTrace (prefixWord ++ tailWord_6961849) baseStart_6961849 baseEnd_6961849 := by
    simpa [prefixWord, tailWord_6961849, baseEnd_6961849] using wordTrace_append hprefix tailTrace_6961849
  have hstable : (prefixWord ++ tailWord_6961849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961849).length < 2 ^ (prefixWord ++ tailWord_6961849).sum := by decide
  have hdescent : baseEnd_6961849 < baseStart_6961849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961879 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_6961879 : Nat := 118140960795 + 6961879 * 2 ^ 59
def prefixEnd_6961879 : Nat := 4983230072969 + 3 ^ 40 * 6961879 * 2
def baseEnd_6961879 : Nat := 3574790185442672350095407

theorem tailTrace_6961879 : CollatzResearch.WordTrace tailWord_6961879 prefixEnd_6961879 3574790185442672350095407 := by
  unfold tailWord_6961879
  simp only [CollatzResearch.WordTrace]
  refine ⟨253920587545308852117640691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169280391696872568078427127 253920587545308852117640691)
  ·
    refine ⟨380880881317963278176461037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253920587545308852117640691 380880881317963278176461037)
    ·
      refine ⟨142830330494236229316172889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380880881317963278176461037 142830330494236229316172889)
      ·
        refine ⟨107122747870677171987129667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142830330494236229316172889 107122747870677171987129667)
        ·
          refine ⟨160684121806015757980694501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107122747870677171987129667 160684121806015757980694501)
          ·
            refine ⟨30128272838627954621380219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160684121806015757980694501 30128272838627954621380219)
            ·
              refine ⟨45192409257941931932070329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30128272838627954621380219 45192409257941931932070329)
              ·
                refine ⟨33894306943456448949052747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45192409257941931932070329 33894306943456448949052747)
                ·
                  refine ⟨50841460415184673423579121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33894306943456448949052747 50841460415184673423579121)
                  ·
                    refine ⟨38131095311388505067684341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50841460415184673423579121 38131095311388505067684341)
                    ·
                      refine ⟨3574790185442672350095407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38131095311388505067684341 3574790185442672350095407)
                      ·
                        rfl

theorem cell23_6961879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_6961879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961879 prefixEnd_6961879 := by exact prefixLift 6961879
  have htrace : WordTrace (prefixWord ++ tailWord_6961879) baseStart_6961879 baseEnd_6961879 := by
    simpa [prefixWord, tailWord_6961879, baseEnd_6961879] using wordTrace_append hprefix tailTrace_6961879
  have hstable : (prefixWord ++ tailWord_6961879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961879).length < 2 ^ (prefixWord ++ tailWord_6961879).sum := by decide
  have hdescent : baseEnd_6961879 < baseStart_6961879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961916 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_6961916 : Nat := 118140960795 + 6961916 * 2 ^ 59
def prefixEnd_6961916 : Nat := 4983230072969 + 3 ^ 40 * 6961916 * 2
def baseEnd_6961916 : Nat := 1191603061408962901777579

theorem tailTrace_6961916 : CollatzResearch.WordTrace tailWord_6961916 prefixEnd_6961916 1191603061408962901777579 := by
  unfold tailWord_6961916
  simp only [CollatzResearch.WordTrace]
  refine ⟨126960968523087403718368801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169281291364116538291158401 126960968523087403718368801)
  ·
    refine ⟨95220726392315552788776601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126960968523087403718368801 95220726392315552788776601)
    ·
      refine ⟨71415544794236664591582451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95220726392315552788776601 71415544794236664591582451)
      ·
        refine ⟨107123317191354996887373677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71415544794236664591582451 107123317191354996887373677)
        ·
          refine ⟨40171243946758123832765129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107123317191354996887373677 40171243946758123832765129)
          ·
            refine ⟨30128432960068592874573847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40171243946758123832765129 30128432960068592874573847)
            ·
              refine ⟨45192649440102889311860771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30128432960068592874573847 45192649440102889311860771)
              ·
                refine ⟨67788974160154333967791157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45192649440102889311860771 67788974160154333967791157)
                ·
                  refine ⟨6355216327514468809480421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67788974160154333967791157 6355216327514468809480421)
                  ·
                    refine ⟨1191603061408962901777579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6355216327514468809480421 1191603061408962901777579)
                    ·
                      rfl

theorem cell23_6961916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_6961916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961916 prefixEnd_6961916 := by exact prefixLift 6961916
  have htrace : WordTrace (prefixWord ++ tailWord_6961916) baseStart_6961916 baseEnd_6961916 := by
    simpa [prefixWord, tailWord_6961916, baseEnd_6961916] using wordTrace_append hprefix tailTrace_6961916
  have hstable : (prefixWord ++ tailWord_6961916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961916).length < 2 ^ (prefixWord ++ tailWord_6961916).sum := by decide
  have hdescent : baseEnd_6961916 < baseStart_6961916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961983 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 1, 5, 2]
def baseStart_6961983 : Nat := 118140960795 + 6961983 * 2 ^ 59
def prefixEnd_6961983 : Nat := 4983230072969 + 3 ^ 40 * 6961983 * 2
def baseEnd_6961983 : Nat := 3574843587430739943194929

theorem tailTrace_6961983 : CollatzResearch.WordTrace tailWord_6961983 prefixEnd_6961983 3574843587430739943194929 := by
  unfold tailWord_6961983
  simp only [CollatzResearch.WordTrace]
  refine ⟨253924380736932077879426603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169282920491288051919617735 253924380736932077879426603)
  ·
    refine ⟨380886571105398116819139905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253924380736932077879426603 380886571105398116819139905)
    ·
      refine ⟨285664928329048587614354929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380886571105398116819139905 285664928329048587614354929)
      ·
        refine ⟨214248696246786440710766197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285664928329048587614354929 214248696246786440710766197)
        ·
          refine ⟨20085815273136228816634331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214248696246786440710766197 20085815273136228816634331)
          ·
            refine ⟨30128722909704343224951497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20085815273136228816634331 30128722909704343224951497)
            ·
              refine ⟨22596542182278257418713623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30128722909704343224951497 22596542182278257418713623)
              ·
                refine ⟨33894813273417386128070435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22596542182278257418713623 33894813273417386128070435)
                ·
                  refine ⟨50842219910126079192105653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33894813273417386128070435 50842219910126079192105653)
                  ·
                    refine ⟨4766458116574319924259905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50842219910126079192105653 4766458116574319924259905)
                    ·
                      refine ⟨3574843587430739943194929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766458116574319924259905 3574843587430739943194929)
                      ·
                        rfl

theorem cell23_6961983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_6961983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961983 prefixEnd_6961983 := by exact prefixLift 6961983
  have htrace : WordTrace (prefixWord ++ tailWord_6961983) baseStart_6961983 baseEnd_6961983 := by
    simpa [prefixWord, tailWord_6961983, baseEnd_6961983] using wordTrace_append hprefix tailTrace_6961983
  have hstable : (prefixWord ++ tailWord_6961983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961983).length < 2 ^ (prefixWord ++ tailWord_6961983).sum := by decide
  have hdescent : baseEnd_6961983 < baseStart_6961983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962016 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_6962016 : Nat := 118140960795 + 6962016 * 2 ^ 59
def prefixEnd_6962016 : Nat := 4983230072969 + 3 ^ 40 * 6962016 * 2
def baseEnd_6962016 : Nat := 3574860532292338314082277

theorem tailTrace_6962016 : CollatzResearch.WordTrace tailWord_6962016 prefixEnd_6962016 3574860532292338314082277 := by
  unfold tailWord_6962016
  simp only [CollatzResearch.WordTrace]
  refine ⟨126962792172906262257688951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169283722897208349676918601 126962792172906262257688951)
  ·
    refine ⟨190444188259359393386533427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126962792172906262257688951 190444188259359393386533427)
    ·
      refine ⟨285666282389039090079800141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190444188259359393386533427 285666282389039090079800141)
      ·
        refine ⟨107124855895889658779925053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285666282389039090079800141 107124855895889658779925053)
        ·
          refine ⟨40171820960958622042471895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107124855895889658779925053 40171820960958622042471895)
          ·
            refine ⟨60257731441437933063707843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40171820960958622042471895 60257731441437933063707843)
            ·
              refine ⟨90386597162156899595561765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60257731441437933063707843 90386597162156899595561765)
              ·
                refine ⟨16947486967904418674167831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90386597162156899595561765 16947486967904418674167831)
                ·
                  refine ⟨25421230451856628011251747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16947486967904418674167831 25421230451856628011251747)
                  ·
                    refine ⟨38131845677784942016877621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25421230451856628011251747 38131845677784942016877621)
                    ·
                      refine ⟨3574860532292338314082277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38131845677784942016877621 3574860532292338314082277)
                      ·
                        rfl

theorem cell23_6962016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_6962016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962016 prefixEnd_6962016 := by exact prefixLift 6962016
  have htrace : WordTrace (prefixWord ++ tailWord_6962016) baseStart_6962016 baseEnd_6962016 := by
    simpa [prefixWord, tailWord_6962016, baseEnd_6962016] using wordTrace_append hprefix tailTrace_6962016
  have hstable : (prefixWord ++ tailWord_6962016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962016).length < 2 ^ (prefixWord ++ tailWord_6962016).sum := by decide
  have hdescent : baseEnd_6962016 < baseStart_6962016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962030 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6962030 : Nat := 118140960795 + 6962030 * 2 ^ 59
def prefixEnd_6962030 : Nat := 4983230072969 + 3 ^ 40 * 6962030 * 2
def baseEnd_6962030 : Nat := 3574867721021501259307213

theorem tailTrace_6962030 : CollatzResearch.WordTrace tailWord_6962030 prefixEnd_6962030 3574867721021501259307213 := by
  unfold tailWord_6962030
  simp only [CollatzResearch.WordTrace]
  refine ⟨31740761870970225613298443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169284063311841203270925029 31740761870970225613298443)
  ·
    refine ⟨47611142806455338419947665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31740761870970225613298443 47611142806455338419947665)
    ·
      refine ⟨35708357104841503814960749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47611142806455338419947665 35708357104841503814960749)
      ·
        refine ⟨13390633914315563930610281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35708357104841503814960749 13390633914315563930610281)
        ·
          refine ⟨10042975435736672947957711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13390633914315563930610281 10042975435736672947957711)
          ·
            refine ⟨15064463153605009421936567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10042975435736672947957711 15064463153605009421936567)
            ·
              refine ⟨22596694730407514132904851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15064463153605009421936567 22596694730407514132904851)
              ·
                refine ⟨33895042095611271199357277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22596694730407514132904851 33895042095611271199357277)
                ·
                  refine ⟨12710640785854226699758979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33895042095611271199357277 12710640785854226699758979)
                  ·
                    refine ⟨19065961178781340049638469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12710640785854226699758979 19065961178781340049638469)
                    ·
                      refine ⟨3574867721021501259307213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19065961178781340049638469 3574867721021501259307213)
                      ·
                        rfl

theorem cell23_6962030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6962030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962030 prefixEnd_6962030 := by exact prefixLift 6962030
  have htrace : WordTrace (prefixWord ++ tailWord_6962030) baseStart_6962030 baseEnd_6962030 := by
    simpa [prefixWord, tailWord_6962030, baseEnd_6962030] using wordTrace_append hprefix tailTrace_6962030
  have hstable : (prefixWord ++ tailWord_6962030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962030).length < 2 ^ (prefixWord ++ tailWord_6962030).sum := by decide
  have hdescent : baseEnd_6962030 < baseStart_6962030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962033 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_6962033 : Nat := 118140960795 + 6962033 * 2 ^ 59
def prefixEnd_6962033 : Nat := 4983230072969 + 3 ^ 40 * 6962033 * 2
def baseEnd_6962033 : Nat := 3574869261463464747569699

theorem tailTrace_6962033 : CollatzResearch.WordTrace tailWord_6962033 prefixEnd_6962033 3574869261463464747569699 := by
  unfold tailWord_6962033
  simp only [CollatzResearch.WordTrace]
  refine ⟨253926204386750936418746753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169284136257833957612497835 253926204386750936418746753)
  ·
    refine ⟨190444653290063202314060065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253926204386750936418746753 190444653290063202314060065)
    ·
      refine ⟨142833489967547401735545049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190444653290063202314060065 142833489967547401735545049)
      ·
        refine ⟨107125117475660551301658787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142833489967547401735545049 107125117475660551301658787)
        ·
          refine ⟨160687676213490826952488181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107125117475660551301658787 160687676213490826952488181)
          ·
            refine ⟨15064469645014765026795767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160687676213490826952488181 15064469645014765026795767)
            ·
              refine ⟨22596704467522147540193651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15064469645014765026795767 22596704467522147540193651)
              ·
                refine ⟨33895056701283221310290477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22596704467522147540193651 33895056701283221310290477)
                ·
                  refine ⟨12710646262981207991358929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33895056701283221310290477 12710646262981207991358929)
                  ·
                    refine ⟨9532984697235905993519197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12710646262981207991358929 9532984697235905993519197)
                    ·
                      refine ⟨3574869261463464747569699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532984697235905993519197 3574869261463464747569699)
                      ·
                        rfl

theorem cell23_6962033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_6962033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962033 prefixEnd_6962033 := by exact prefixLift 6962033
  have htrace : WordTrace (prefixWord ++ tailWord_6962033) baseStart_6962033 baseEnd_6962033 := by
    simpa [prefixWord, tailWord_6962033, baseEnd_6962033] using wordTrace_append hprefix tailTrace_6962033
  have hstable : (prefixWord ++ tailWord_6962033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962033).length < 2 ^ (prefixWord ++ tailWord_6962033).sum := by decide
  have hdescent : baseEnd_6962033 < baseStart_6962033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962080 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 2, 1, 3]
def baseStart_6962080 : Nat := 118140960795 + 6962080 * 2 ^ 59
def prefixEnd_6962080 : Nat := 4983230072969 + 3 ^ 40 * 6962080 * 2
def baseEnd_6962080 : Nat := 3574893395054226063681983

theorem tailTrace_6962080 : CollatzResearch.WordTrace tailWord_6962080 prefixEnd_6962080 3574893395054226063681983 := by
  unfold tailWord_6962080
  simp only [CollatzResearch.WordTrace]
  refine ⟨126963959308790331722853847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169285279078387108963805129 126963959308790331722853847)
  ·
    refine ⟨190445938963185497584280771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126963959308790331722853847 190445938963185497584280771)
    ·
      refine ⟨285668908444778246376421157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190445938963185497584280771 285668908444778246376421157)
      ·
        refine ⟨53562920333395921195578967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285668908444778246376421157 53562920333395921195578967)
        ·
          refine ⟨80344380500093881793368451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53562920333395921195578967 80344380500093881793368451)
          ·
            refine ⟨120516570750140822690052677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80344380500093881793368451 120516570750140822690052677)
            ·
              refine ⟨22596857015651404254384877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120516570750140822690052677 22596857015651404254384877)
              ·
                refine ⟨8473821380869276595394329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22596857015651404254384877 8473821380869276595394329)
                ·
                  refine ⟨6355366035651957446545747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8473821380869276595394329 6355366035651957446545747)
                  ·
                    refine ⟨9533049053477936169818621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6355366035651957446545747 9533049053477936169818621)
                    ·
                      refine ⟨3574893395054226063681983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9533049053477936169818621 3574893395054226063681983)
                      ·
                        rfl

theorem cell23_6962080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_6962080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962080 prefixEnd_6962080 := by exact prefixLift 6962080
  have htrace : WordTrace (prefixWord ++ tailWord_6962080) baseStart_6962080 baseEnd_6962080 := by
    simpa [prefixWord, tailWord_6962080, baseEnd_6962080] using wordTrace_append hprefix tailTrace_6962080
  have hstable : (prefixWord ++ tailWord_6962080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962080).length < 2 ^ (prefixWord ++ tailWord_6962080).sum := by decide
  have hdescent : baseEnd_6962080 < baseStart_6962080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962106 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_6962106 : Nat := 118140960795 + 6962106 * 2 ^ 59
def prefixEnd_6962106 : Nat := 4983230072969 + 3 ^ 40 * 6962106 * 2
def baseEnd_6962106 : Nat := 3574906745551242961956863

theorem tailTrace_6962106 : CollatzResearch.WordTrace tailWord_6962106 prefixEnd_6962106 3574906745551242961956863 := by
  unfold tailWord_6962106
  simp only [CollatzResearch.WordTrace]
  refine ⟨63482216728871617471538543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169285911276990979924102781 63482216728871617471538543)
  ·
    refine ⟨95223325093307426207307815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63482216728871617471538543 95223325093307426207307815)
    ·
      refine ⟨142834987639961139310961723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95223325093307426207307815 142834987639961139310961723)
      ·
        refine ⟨214252481459941708966442585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142834987639961139310961723 214252481459941708966442585)
        ·
          refine ⟨160689361094956281724831939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214252481459941708966442585 160689361094956281724831939)
          ·
            refine ⟨241034041642434422587247909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160689361094956281724831939 241034041642434422587247909)
            ·
              refine ⟨45193882807956454235108983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241034041642434422587247909 45193882807956454235108983)
              ·
                refine ⟨67790824211934681352663475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45193882807956454235108983 67790824211934681352663475)
                ·
                  refine ⟨101686236317902022028995213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67790824211934681352663475 101686236317902022028995213)
                  ·
                    refine ⟨38132338619213258260873205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101686236317902022028995213 38132338619213258260873205)
                    ·
                      refine ⟨3574906745551242961956863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38132338619213258260873205 3574906745551242961956863)
                      ·
                        rfl

theorem cell23_6962106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_6962106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962106 prefixEnd_6962106 := by exact prefixLift 6962106
  have htrace : WordTrace (prefixWord ++ tailWord_6962106) baseStart_6962106 baseEnd_6962106 := by
    simpa [prefixWord, tailWord_6962106, baseEnd_6962106] using wordTrace_append hprefix tailTrace_6962106
  have hstable : (prefixWord ++ tailWord_6962106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962106).length < 2 ^ (prefixWord ++ tailWord_6962106).sum := by decide
  have hdescent : baseEnd_6962106 < baseStart_6962106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962137 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 1, 4, 2]
def baseStart_6962137 : Nat := 118140960795 + 6962137 * 2 ^ 59
def prefixEnd_6962137 : Nat := 4983230072969 + 3 ^ 40 * 6962137 * 2
def baseEnd_6962137 : Nat := 3574922663451532340669221

theorem tailTrace_6962137 : CollatzResearch.WordTrace tailWord_6962137 prefixEnd_6962137 3574922663451532340669221 := by
  unfold tailWord_6962137
  simp only [CollatzResearch.WordTrace]
  refine ⟨253929997578374162180532665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169286665052249441453688443 253929997578374162180532665)
  ·
    refine ⟨190447498183780621635399499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253929997578374162180532665 190447498183780621635399499)
    ·
      refine ⟨285671247275670932453099249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190447498183780621635399499 285671247275670932453099249)
      ·
        refine ⟨214253435456753199339824437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285671247275670932453099249 214253435456753199339824437)
        ·
          refine ⟨20086259574070612438108541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214253435456753199339824437 20086259574070612438108541)
          ·
            refine ⟨7532347340276479664290703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20086259574070612438108541 7532347340276479664290703)
            ·
              refine ⟨11298521010414719496436055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7532347340276479664290703 11298521010414719496436055)
              ·
                refine ⟨16947781515622079244654083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11298521010414719496436055 16947781515622079244654083)
                ·
                  refine ⟨25421672273433118866981125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16947781515622079244654083 25421672273433118866981125)
                  ·
                    refine ⟨4766563551268709787558961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25421672273433118866981125 4766563551268709787558961)
                    ·
                      refine ⟨3574922663451532340669221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766563551268709787558961 3574922663451532340669221)
                      ·
                        rfl

theorem cell23_6962137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_6962137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962137 prefixEnd_6962137 := by exact prefixLift 6962137
  have htrace : WordTrace (prefixWord ++ tailWord_6962137) baseStart_6962137 baseEnd_6962137 := by
    simpa [prefixWord, tailWord_6962137, baseEnd_6962137] using wordTrace_append hprefix tailTrace_6962137
  have hstable : (prefixWord ++ tailWord_6962137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962137).length < 2 ^ (prefixWord ++ tailWord_6962137).sum := by decide
  have hdescent : baseEnd_6962137 < baseStart_6962137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962163 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 7, 2]
def baseStart_6962163 : Nat := 118140960795 + 6962163 * 2 ^ 59
def prefixEnd_6962163 : Nat := 4983230072969 + 3 ^ 40 * 6962163 * 2
def baseEnd_6962163 : Nat := 3574936013948549238944101

theorem tailTrace_6962163 : CollatzResearch.WordTrace tailWord_6962163 prefixEnd_6962163 3574936013948549238944101 := by
  unfold tailWord_6962163
  simp only [CollatzResearch.WordTrace]
  refine ⟨253930945876279968620979143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169287297250853312413986095 253930945876279968620979143)
  ·
    refine ⟨380896418814419952931468715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253930945876279968620979143 380896418814419952931468715)
    ·
      refine ⟨571344628221629929397203073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380896418814419952931468715 571344628221629929397203073)
      ·
        refine ⟨428508471166222447047902305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571344628221629929397203073 428508471166222447047902305)
        ·
          refine ⟨321381353374666835285926729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428508471166222447047902305 321381353374666835285926729)
          ·
            refine ⟨241036015031000126464445047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321381353374666835285926729 241036015031000126464445047)
            ·
              refine ⟨361554022546500189696667571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241036015031000126464445047 361554022546500189696667571)
              ·
                refine ⟨542331033819750284545001357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361554022546500189696667571 542331033819750284545001357)
                ·
                  refine ⟨203374137682406356704375509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542331033819750284545001357 203374137682406356704375509)
                  ·
                    refine ⟨4766581351931398985258801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 203374137682406356704375509 4766581351931398985258801)
                    ·
                      refine ⟨3574936013948549238944101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766581351931398985258801 3574936013948549238944101)
                      ·
                        rfl

theorem cell23_6962163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7, 2].length) (baseStart_6962163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962163 prefixEnd_6962163 := by exact prefixLift 6962163
  have htrace : WordTrace (prefixWord ++ tailWord_6962163) baseStart_6962163 baseEnd_6962163 := by
    simpa [prefixWord, tailWord_6962163, baseEnd_6962163] using wordTrace_append hprefix tailTrace_6962163
  have hstable : (prefixWord ++ tailWord_6962163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962163).length < 2 ^ (prefixWord ++ tailWord_6962163).sum := by decide
  have hdescent : baseEnd_6962163 < baseStart_6962163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962177 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 5]
def baseStart_6962177 : Nat := 118140960795 + 6962177 * 2 ^ 59
def prefixEnd_6962177 : Nat := 4983230072969 + 3 ^ 40 * 6962177 * 2
def baseEnd_6962177 : Nat := 397215911408634687129893

theorem tailTrace_6962177 : CollatzResearch.WordTrace tailWord_6962177 prefixEnd_6962177 397215911408634687129893 := by
  unfold tailWord_6962177
  simp only [CollatzResearch.WordTrace]
  refine ⟨253931456498229249011988785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169287637665486166007992523 253931456498229249011988785)
  ·
    refine ⟨190448592373671936758991589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253931456498229249011988785 190448592373671936758991589)
    ·
      refine ⟨35709111070063488142310923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190448592373671936758991589 35709111070063488142310923)
      ·
        refine ⟨53563666605095232213466385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35709111070063488142310923 53563666605095232213466385)
        ·
          refine ⟨40172749953821424160099789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53563666605095232213466385 40172749953821424160099789)
          ·
            refine ⟨15064781232683034060037421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40172749953821424160099789 15064781232683034060037421)
            ·
              refine ⟨5649292962256137772514033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15064781232683034060037421 5649292962256137772514033)
              ·
                refine ⟨4236969721692103329385525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649292962256137772514033 4236969721692103329385525)
                ·
                  refine ⟨397215911408634687129893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4236969721692103329385525 397215911408634687129893)
                  ·
                    rfl

theorem cell23_6962177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 5].length) (baseStart_6962177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962177 prefixEnd_6962177 := by exact prefixLift 6962177
  have htrace : WordTrace (prefixWord ++ tailWord_6962177) baseStart_6962177 baseEnd_6962177 := by
    simpa [prefixWord, tailWord_6962177, baseEnd_6962177] using wordTrace_append hprefix tailTrace_6962177
  have hstable : (prefixWord ++ tailWord_6962177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962177).length < 2 ^ (prefixWord ++ tailWord_6962177).sum := by decide
  have hdescent : baseEnd_6962177 < baseStart_6962177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962183 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6962183 : Nat := 118140960795 + 6962183 * 2 ^ 59
def prefixEnd_6962183 : Nat := 4983230072969 + 3 ^ 40 * 6962183 * 2
def baseEnd_6962183 : Nat := 3574946283561639160694009

theorem tailTrace_6962183 : CollatzResearch.WordTrace tailWord_6962183 prefixEnd_6962183 3574946283561639160694009 := by
  unfold tailWord_6962183
  simp only [CollatzResearch.WordTrace]
  refine ⟨253931675336207512036707203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169287783557471674691138135 253931675336207512036707203)
  ·
    refine ⟨380897513004311268055060805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253931675336207512036707203 380897513004311268055060805)
    ·
      refine ⟨71418283688308362760323901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380897513004311268055060805 71418283688308362760323901)
      ·
        refine ⟨26781856383115636035121463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71418283688308362760323901 26781856383115636035121463)
        ·
          refine ⟨40172784574673454052682195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26781856383115636035121463 40172784574673454052682195)
          ·
            refine ⟨60259176862010181079023293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40172784574673454052682195 60259176862010181079023293)
            ·
              refine ⟨22597191323253817904633735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60259176862010181079023293 22597191323253817904633735)
              ·
                refine ⟨33895786984880726856950603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22597191323253817904633735 33895786984880726856950603)
                ·
                  refine ⟨50843680477321090285425905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33895786984880726856950603 50843680477321090285425905)
                  ·
                    refine ⟨38132760357990817714069429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50843680477321090285425905 38132760357990817714069429)
                    ·
                      refine ⟨3574946283561639160694009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38132760357990817714069429 3574946283561639160694009)
                      ·
                        rfl

theorem cell23_6962183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6962183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962183 prefixEnd_6962183 := by exact prefixLift 6962183
  have htrace : WordTrace (prefixWord ++ tailWord_6962183) baseStart_6962183 baseEnd_6962183 := by
    simpa [prefixWord, tailWord_6962183, baseEnd_6962183] using wordTrace_append hprefix tailTrace_6962183
  have hstable : (prefixWord ++ tailWord_6962183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962183).length < 2 ^ (prefixWord ++ tailWord_6962183).sum := by decide
  have hdescent : baseEnd_6962183 < baseStart_6962183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962210 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6962210 : Nat := 118140960795 + 6962210 * 2 ^ 59
def prefixEnd_6962210 : Nat := 4983230072969 + 3 ^ 40 * 6962210 * 2
def baseEnd_6962210 : Nat := 3574960147539310555056385

theorem tailTrace_6962210 : CollatzResearch.WordTrace tailWord_6962210 prefixEnd_6962210 3574960147539310555056385 := by
  unfold tailWord_6962210
  simp only [CollatzResearch.WordTrace]
  refine ⟨63483165026777423911985021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169288440071406463765293389 63483165026777423911985021)
  ·
    refine ⟨23806186885041533966994383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63483165026777423911985021 23806186885041533966994383)
    ·
      refine ⟨35709280327562300950491575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23806186885041533966994383 35709280327562300950491575)
      ·
        refine ⟨53563920491343451425737363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35709280327562300950491575 53563920491343451425737363)
        ·
          refine ⟨80345880737015177138606045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53563920491343451425737363 80345880737015177138606045)
          ·
            refine ⟨30129705276380691426977267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80345880737015177138606045 30129705276380691426977267)
            ·
              refine ⟨45194557914571037140465901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30129705276380691426977267 45194557914571037140465901)
              ·
                refine ⟨16947959217964138927674713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45194557914571037140465901 16947959217964138927674713)
                ·
                  refine ⟨12710969413473104195756035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16947959217964138927674713 12710969413473104195756035)
                  ·
                    refine ⟨19066454120209656293634053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12710969413473104195756035 19066454120209656293634053)
                    ·
                      refine ⟨3574960147539310555056385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19066454120209656293634053 3574960147539310555056385)
                      ·
                        rfl

theorem cell23_6962210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6962210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962210 prefixEnd_6962210 := by exact prefixLift 6962210
  have htrace : WordTrace (prefixWord ++ tailWord_6962210) baseStart_6962210 baseEnd_6962210 := by
    simpa [prefixWord, tailWord_6962210, baseEnd_6962210] using wordTrace_append hprefix tailTrace_6962210
  have hstable : (prefixWord ++ tailWord_6962210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962210).length < 2 ^ (prefixWord ++ tailWord_6962210).sum := by decide
  have hdescent : baseEnd_6962210 < baseStart_6962210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962294 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6962294 : Nat := 118140960795 + 6962294 * 2 ^ 59
def prefixEnd_6962294 : Nat := 4983230072969 + 3 ^ 40 * 6962294 * 2
def baseEnd_6962294 : Nat := 3575003279914288226405999

theorem tailTrace_6962294 : CollatzResearch.WordTrace tailWord_6962294 prefixEnd_6962294 3575003279914288226405999 := by
  unfold tailWord_6962294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15870982739925336124624871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169290482559203585329331957 15870982739925336124624871)
  ·
    refine ⟨23806474109888004186937307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15870982739925336124624871 23806474109888004186937307)
    ·
      refine ⟨35709711164832006280405961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23806474109888004186937307 35709711164832006280405961)
      ·
        refine ⟨26782283373624004710304471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35709711164832006280405961 26782283373624004710304471)
        ·
          refine ⟨40173425060436007065456707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26782283373624004710304471 40173425060436007065456707)
          ·
            refine ⟨60260137590654010598185061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40173425060436007065456707 60260137590654010598185061)
            ·
              refine ⟨11298775798247626987159699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60260137590654010598185061 11298775798247626987159699)
              ·
                refine ⟨16948163697371440480739549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11298775798247626987159699 16948163697371440480739549)
                ·
                  refine ⟨6355561386514290180277331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16948163697371440480739549 6355561386514290180277331)
                  ·
                    refine ⟨9533342079771435270415997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6355561386514290180277331 9533342079771435270415997)
                    ·
                      refine ⟨3575003279914288226405999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9533342079771435270415997 3575003279914288226405999)
                      ·
                        rfl

theorem cell23_6962294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6962294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962294 prefixEnd_6962294 := by exact prefixLift 6962294
  have htrace : WordTrace (prefixWord ++ tailWord_6962294) baseStart_6962294 baseEnd_6962294 := by
    simpa [prefixWord, tailWord_6962294, baseEnd_6962294] using wordTrace_append hprefix tailTrace_6962294
  have hstable : (prefixWord ++ tailWord_6962294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962294).length < 2 ^ (prefixWord ++ tailWord_6962294).sum := by decide
  have hdescent : baseEnd_6962294 < baseStart_6962294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962334 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_6962334 : Nat := 118140960795 + 6962334 * 2 ^ 59
def prefixEnd_6962334 : Nat := 4983230072969 + 3 ^ 40 * 6962334 * 2
def baseEnd_6962334 : Nat := 3575023819140468069905815

theorem tailTrace_6962334 : CollatzResearch.WordTrace tailWord_6962334 prefixEnd_6962334 3575023819140468069905815 := by
  unfold tailWord_6962334
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742147844832558103181757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169291455172440309883636037 31742147844832558103181757)
  ·
    refine ⟨11903305441812209288693159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31742147844832558103181757 11903305441812209288693159)
    ·
      refine ⟨17854958162718313933039739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11903305441812209288693159 17854958162718313933039739)
      ·
        refine ⟨26782437244077470899559609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17854958162718313933039739 26782437244077470899559609)
        ·
          refine ⟨20086827933058103174669707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26782437244077470899559609 20086827933058103174669707)
          ·
            refine ⟨30130241899587154762004561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20086827933058103174669707 30130241899587154762004561)
            ·
              refine ⟨22597681424690366071503421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30130241899587154762004561 22597681424690366071503421)
              ·
                refine ⟨8474130534258887276813783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22597681424690366071503421 8474130534258887276813783)
                ·
                  refine ⟨12711195801388330915220675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474130534258887276813783 12711195801388330915220675)
                  ·
                    refine ⟨19066793702082496372831013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12711195801388330915220675 19066793702082496372831013)
                    ·
                      refine ⟨3575023819140468069905815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19066793702082496372831013 3575023819140468069905815)
                      ·
                        rfl

theorem cell23_6962334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_6962334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962334 prefixEnd_6962334 := by exact prefixLift 6962334
  have htrace : WordTrace (prefixWord ++ tailWord_6962334) baseStart_6962334 baseEnd_6962334 := by
    simpa [prefixWord, tailWord_6962334, baseEnd_6962334] using wordTrace_append hprefix tailTrace_6962334
  have hstable : (prefixWord ++ tailWord_6962334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962334).length < 2 ^ (prefixWord ++ tailWord_6962334).sum := by decide
  have hdescent : baseEnd_6962334 < baseStart_6962334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962337 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6962337 : Nat := 118140960795 + 6962337 * 2 ^ 59
def prefixEnd_6962337 : Nat := 4983230072969 + 3 ^ 40 * 6962337 * 2
def baseEnd_6962337 : Nat := 3575025359582431558168301

theorem tailTrace_6962337 : CollatzResearch.WordTrace tailWord_6962337 prefixEnd_6962337 3575025359582431558168301 := by
  unfold tailWord_6962337
  simp only [CollatzResearch.WordTrace]
  refine ⟨253937292177649596337813265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169291528118433064225208843 253937292177649596337813265)
  ·
    refine ⟨190452969133237197253359949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253937292177649596337813265 190452969133237197253359949)
    ·
      refine ⟨71419863424963948970009981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190452969133237197253359949 71419863424963948970009981)
      ·
        refine ⟨26782448784361480863753743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71419863424963948970009981 26782448784361480863753743)
        ·
          refine ⟨40173673176542221295630615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26782448784361480863753743 40173673176542221295630615)
          ·
            refine ⟨60260509764813331943445923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40173673176542221295630615 60260509764813331943445923)
            ·
              refine ⟨90390764647219997915168885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60260509764813331943445923 90390764647219997915168885)
              ·
                refine ⟨8474134185676874804547083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90390764647219997915168885 8474134185676874804547083)
                ·
                  refine ⟨12711201278515312206820625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474134185676874804547083 12711201278515312206820625)
                  ·
                    refine ⟨9533400958886484155115469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12711201278515312206820625 9533400958886484155115469)
                    ·
                      refine ⟨3575025359582431558168301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9533400958886484155115469 3575025359582431558168301)
                      ·
                        rfl

theorem cell23_6962337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6962337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962337 prefixEnd_6962337 := by exact prefixLift 6962337
  have htrace : WordTrace (prefixWord ++ tailWord_6962337) baseStart_6962337 baseEnd_6962337 := by
    simpa [prefixWord, tailWord_6962337, baseEnd_6962337] using wordTrace_append hprefix tailTrace_6962337
  have hstable : (prefixWord ++ tailWord_6962337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962337).length < 2 ^ (prefixWord ++ tailWord_6962337).sum := by decide
  have hdescent : baseEnd_6962337 < baseStart_6962337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962340 : List Nat := [2, 3, 1, 2, 3, 3, 9]
def baseStart_6962340 : Nat := 118140960795 + 6962340 * 2 ^ 59
def prefixEnd_6962340 : Nat := 4983230072969 + 3 ^ 40 * 6962340 * 2
def baseEnd_6962340 : Nat := 44136134568202407980627

theorem tailTrace_6962340 : CollatzResearch.WordTrace tailWord_6962340 prefixEnd_6962340 44136134568202407980627 := by
  unfold tailWord_6962340
  simp only [CollatzResearch.WordTrace]
  refine ⟨126968700798319363925086237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169291601064425818566781649 126968700798319363925086237)
  ·
    refine ⟨47613262799369761471907339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126968700798319363925086237 47613262799369761471907339)
    ·
      refine ⟨71419894199054642207861009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47613262799369761471907339 71419894199054642207861009)
      ·
        refine ⟨53564920649290981655895757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71419894199054642207861009 53564920649290981655895757)
        ·
          refine ⟨20086845243484118120960909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53564920649290981655895757 20086845243484118120960909)
          ·
            refine ⟨7532566966306544295360341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20086845243484118120960909 7532566966306544295360341)
            ·
              refine ⟨44136134568202407980627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7532566966306544295360341 44136134568202407980627)
              ·
                rfl

theorem cell23_6962340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 9].length) (baseStart_6962340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962340 prefixEnd_6962340 := by exact prefixLift 6962340
  have htrace : WordTrace (prefixWord ++ tailWord_6962340) baseStart_6962340 baseEnd_6962340 := by
    simpa [prefixWord, tailWord_6962340, baseEnd_6962340] using wordTrace_append hprefix tailTrace_6962340
  have hstable : (prefixWord ++ tailWord_6962340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962340).length < 2 ^ (prefixWord ++ tailWord_6962340).sum := by decide
  have hdescent : baseEnd_6962340 < baseStart_6962340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962363 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_6962363 : Nat := 118140960795 + 6962363 * 2 ^ 59
def prefixEnd_6962363 : Nat := 4983230072969 + 3 ^ 40 * 6962363 * 2
def baseEnd_6962363 : Nat := 3575038710079448456443181

theorem tailTrace_6962363 : CollatzResearch.WordTrace tailWord_6962363 prefixEnd_6962363 3575038710079448456443181 := by
  unfold tailWord_6962363
  simp only [CollatzResearch.WordTrace]
  refine ⟨253938240475555402778259743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169292160317036935185506495 253938240475555402778259743)
  ·
    refine ⟨380907360713333104167389615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253938240475555402778259743 380907360713333104167389615)
    ·
      refine ⟨571361041069999656251084423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380907360713333104167389615 571361041069999656251084423)
      ·
        refine ⟨857041561604999484376626635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571361041069999656251084423 857041561604999484376626635)
        ·
          refine ⟨1285562342407499226564939953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857041561604999484376626635 1285562342407499226564939953)
          ·
            refine ⟨964171756805624419923704965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285562342407499226564939953 964171756805624419923704965)
            ·
              refine ⟨180782204401054578735694681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 964171756805624419923704965 180782204401054578735694681)
              ·
                refine ⟨135586653300790934051771011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180782204401054578735694681 135586653300790934051771011)
                ·
                  refine ⟨203379979951186401077656517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135586653300790934051771011 203379979951186401077656517)
                  ·
                    refine ⟨38133746240847450202060597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203379979951186401077656517 38133746240847450202060597)
                    ·
                      refine ⟨3575038710079448456443181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38133746240847450202060597 3575038710079448456443181)
                      ·
                        rfl

theorem cell23_6962363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_6962363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962363 prefixEnd_6962363 := by exact prefixLift 6962363
  have htrace : WordTrace (prefixWord ++ tailWord_6962363) baseStart_6962363 baseEnd_6962363 := by
    simpa [prefixWord, tailWord_6962363, baseEnd_6962363] using wordTrace_append hprefix tailTrace_6962363
  have hstable : (prefixWord ++ tailWord_6962363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962363).length < 2 ^ (prefixWord ++ tailWord_6962363).sum := by decide
  have hdescent : baseEnd_6962363 < baseStart_6962363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962373 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_6962373 : Nat := 118140960795 + 6962373 * 2 ^ 59
def prefixEnd_6962373 : Nat := 4983230072969 + 3 ^ 40 * 6962373 * 2
def baseEnd_6962373 : Nat := 3575043844885993417318135

theorem tailTrace_6962373 : CollatzResearch.WordTrace tailWord_6962373 prefixEnd_6962373 3575043844885993417318135 := by
  unfold tailWord_6962373
  simp only [CollatzResearch.WordTrace]
  refine ⟨253938605205519174486123773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169292403470346116324082515 253938605205519174486123773)
  ·
    refine ⟨95226976952069690432296415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253938605205519174486123773 95226976952069690432296415)
    ·
      refine ⟨142840465428104535648444623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95226976952069690432296415 142840465428104535648444623)
      ·
        refine ⟨214260698142156803472666935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142840465428104535648444623 214260698142156803472666935)
        ·
          refine ⟨321391047213235205209000403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214260698142156803472666935 321391047213235205209000403)
          ·
            refine ⟨482086570819852807813500605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321391047213235205209000403 482086570819852807813500605)
            ·
              refine ⟨180782464057444802930062727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482086570819852807813500605 180782464057444802930062727)
              ·
                refine ⟨271173696086167204395094091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180782464057444802930062727 271173696086167204395094091)
                ·
                  refine ⟨406760544129250806592641137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271173696086167204395094091 406760544129250806592641137)
                  ·
                    refine ⟨305070408096938104944480853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406760544129250806592641137 305070408096938104944480853)
                    ·
                      refine ⟨3575043844885993417318135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 305070408096938104944480853 3575043844885993417318135)
                      ·
                        rfl

theorem cell23_6962373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_6962373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962373 prefixEnd_6962373 := by exact prefixLift 6962373
  have htrace : WordTrace (prefixWord ++ tailWord_6962373) baseStart_6962373 baseEnd_6962373 := by
    simpa [prefixWord, tailWord_6962373, baseEnd_6962373] using wordTrace_append hprefix tailTrace_6962373
  have hstable : (prefixWord ++ tailWord_6962373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962373).length < 2 ^ (prefixWord ++ tailWord_6962373).sum := by decide
  have hdescent : baseEnd_6962373 < baseStart_6962373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962381 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6962381 : Nat := 118140960795 + 6962381 * 2 ^ 59
def prefixEnd_6962381 : Nat := 4983230072969 + 3 ^ 40 * 6962381 * 2
def baseEnd_6962381 : Nat := 3575047952731229386018099

theorem tailTrace_6962381 : CollatzResearch.WordTrace tailWord_6962381 prefixEnd_6962381 3575047952731229386018099 := by
  unfold tailWord_6962381
  simp only [CollatzResearch.WordTrace]
  refine ⟨253938896989490191852414997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169292597992993461234943331 253938896989490191852414997)
  ·
    refine ⟨11903385796382352743081953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253938896989490191852414997 11903385796382352743081953)
    ·
      refine ⟨8927539347286764557311465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11903385796382352743081953 8927539347286764557311465)
      ·
        refine ⟨6695654510465073417983599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8927539347286764557311465 6695654510465073417983599)
        ·
          refine ⟨10043481765697610126975399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695654510465073417983599 10043481765697610126975399)
          ·
            refine ⟨15065222648546415190463099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043481765697610126975399 15065222648546415190463099)
            ·
              refine ⟨22597833972819622785694649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15065222648546415190463099 22597833972819622785694649)
              ·
                refine ⟨16948375479614717089270987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22597833972819622785694649 16948375479614717089270987)
                ·
                  refine ⟨25422563219422075633906481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16948375479614717089270987 25422563219422075633906481)
                  ·
                    refine ⟨19066922414566556725429861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25422563219422075633906481 19066922414566556725429861)
                    ·
                      refine ⟨3575047952731229386018099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19066922414566556725429861 3575047952731229386018099)
                      ·
                        rfl

theorem cell23_6962381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6962381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962381 prefixEnd_6962381 := by exact prefixLift 6962381
  have htrace : WordTrace (prefixWord ++ tailWord_6962381) baseStart_6962381 baseEnd_6962381 := by
    simpa [prefixWord, tailWord_6962381, baseEnd_6962381] using wordTrace_append hprefix tailTrace_6962381
  have hstable : (prefixWord ++ tailWord_6962381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962381).length < 2 ^ (prefixWord ++ tailWord_6962381).sum := by decide
  have hdescent : baseEnd_6962381 < baseStart_6962381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962383 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 8]
def baseStart_6962383 : Nat := 118140960795 + 6962383 * 2 ^ 59
def prefixEnd_6962383 : Nat := 4983230072969 + 3 ^ 40 * 6962383 * 2
def baseEnd_6962383 : Nat := 1191682993230846126064363

theorem tailTrace_6962383 : CollatzResearch.WordTrace tailWord_6962383 prefixEnd_6962383 1191682993230846126064363 := by
  unfold tailWord_6962383
  simp only [CollatzResearch.WordTrace]
  refine ⟨253938969935482946193987803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169292646623655297462658535 253938969935482946193987803)
  ·
    refine ⟨380908454903224419290981705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253938969935482946193987803 380908454903224419290981705)
    ·
      refine ⟨285681341177418314468236279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380908454903224419290981705 285681341177418314468236279)
      ·
        refine ⟨428522011766127471702354419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285681341177418314468236279 428522011766127471702354419)
        ·
          refine ⟨642783017649191207553531629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428522011766127471702354419 642783017649191207553531629)
          ·
            refine ⟨241043631618446702832574361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642783017649191207553531629 241043631618446702832574361)
            ·
              refine ⟨180782723713835027124430771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241043631618446702832574361 180782723713835027124430771)
              ·
                refine ⟨271174085570752540686646157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180782723713835027124430771 271174085570752540686646157)
                ·
                  refine ⟨101690282089032202757492309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271174085570752540686646157 101690282089032202757492309)
                  ·
                    refine ⟨1191682993230846126064363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101690282089032202757492309 1191682993230846126064363)
                    ·
                      rfl

theorem cell23_6962383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_6962383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962383 prefixEnd_6962383 := by exact prefixLift 6962383
  have htrace : WordTrace (prefixWord ++ tailWord_6962383) baseStart_6962383 baseEnd_6962383 := by
    simpa [prefixWord, tailWord_6962383, baseEnd_6962383] using wordTrace_append hprefix tailTrace_6962383
  have hstable : (prefixWord ++ tailWord_6962383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962383).length < 2 ^ (prefixWord ++ tailWord_6962383).sum := by decide
  have hdescent : baseEnd_6962383 < baseStart_6962383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962388 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6962388 : Nat := 118140960795 + 6962388 * 2 ^ 59
def prefixEnd_6962388 : Nat := 4983230072969 + 3 ^ 40 * 6962388 * 2
def baseEnd_6962388 : Nat := 3575051547095810858630567

theorem tailTrace_6962388 : CollatzResearch.WordTrace tailWord_6962388 prefixEnd_6962388 3575051547095810858630567 := by
  unfold tailWord_6962388
  simp only [CollatzResearch.WordTrace]
  refine ⟨126969576150232416023959909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169292768200309888031946545 126969576150232416023959909)
  ·
    refine ⟨23806795528168578004492483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126969576150232416023959909 23806795528168578004492483)
    ·
      refine ⟨35710193292252867006738725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23806795528168578004492483 35710193292252867006738725)
      ·
        refine ⟨6695661242297412563763511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35710193292252867006738725 6695661242297412563763511)
        ·
          refine ⟨10043491863446118845645267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695661242297412563763511 10043491863446118845645267)
          ·
            refine ⟨15065237795169178268467901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043491863446118845645267 15065237795169178268467901)
            ·
              refine ⟨5649464173188441850675463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15065237795169178268467901 5649464173188441850675463)
              ·
                refine ⟨8474196259782662776013195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649464173188441850675463 8474196259782662776013195)
                ·
                  refine ⟨12711294389673994164019793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474196259782662776013195 12711294389673994164019793)
                  ·
                    refine ⟨9533470792255495623014845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12711294389673994164019793 9533470792255495623014845)
                    ·
                      refine ⟨3575051547095810858630567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9533470792255495623014845 3575051547095810858630567)
                      ·
                        rfl

theorem cell23_6962388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6962388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962388 prefixEnd_6962388 := by exact prefixLift 6962388
  have htrace : WordTrace (prefixWord ++ tailWord_6962388) baseStart_6962388 baseEnd_6962388 := by
    simpa [prefixWord, tailWord_6962388, baseEnd_6962388] using wordTrace_append hprefix tailTrace_6962388
  have hstable : (prefixWord ++ tailWord_6962388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962388).length < 2 ^ (prefixWord ++ tailWord_6962388).sum := by decide
  have hdescent : baseEnd_6962388 < baseStart_6962388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962458 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2]
def baseStart_6962458 : Nat := 118140960795 + 6962458 * 2 ^ 59
def prefixEnd_6962458 : Nat := 4983230072969 + 3 ^ 40 * 6962458 * 2
def baseEnd_6962458 : Nat := 3575087490741625584755245

theorem tailTrace_6962458 : CollatzResearch.WordTrace tailWord_6962458 prefixEnd_6962458 3575087490741625584755245 := by
  unfold tailWord_6962458
  simp only [CollatzResearch.WordTrace]
  refine ⟨63485426352552808500742007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169294470273474156001978685 63485426352552808500742007)
  ·
    refine ⟨95228139528829212751113011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63485426352552808500742007 95228139528829212751113011)
    ·
      refine ⟨142842209293243819126669517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95228139528829212751113011 142842209293243819126669517)
      ·
        refine ⟨53565828484966432172501069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142842209293243819126669517 53565828484966432172501069)
        ·
          refine ⟨20087185681862412064687901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53565828484966432172501069 20087185681862412064687901)
          ·
            refine ⟨7532694630698404524257963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20087185681862412064687901 7532694630698404524257963)
            ·
              refine ⟨11299041946047606786386945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7532694630698404524257963 11299041946047606786386945)
              ·
                refine ⟨8474281459535705089790209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11299041946047606786386945 8474281459535705089790209)
                ·
                  refine ⟨6355711094651778817342657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474281459535705089790209 6355711094651778817342657)
                  ·
                    refine ⟨4766783320988834113006993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6355711094651778817342657 4766783320988834113006993)
                    ·
                      refine ⟨3575087490741625584755245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766783320988834113006993 3575087490741625584755245)
                      ·
                        rfl

theorem cell23_6962458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_6962458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962458 prefixEnd_6962458 := by exact prefixLift 6962458
  have htrace : WordTrace (prefixWord ++ tailWord_6962458) baseStart_6962458 baseEnd_6962458 := by
    simpa [prefixWord, tailWord_6962458, baseEnd_6962458] using wordTrace_append hprefix tailTrace_6962458
  have hstable : (prefixWord ++ tailWord_6962458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962458).length < 2 ^ (prefixWord ++ tailWord_6962458).sum := by decide
  have hdescent : baseEnd_6962458 < baseStart_6962458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962474 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6962474 : Nat := 118140960795 + 6962474 * 2 ^ 59
def prefixEnd_6962474 : Nat := 4983230072969 + 3 ^ 40 * 6962474 * 2
def baseEnd_6962474 : Nat := 3575095706432097522155171

theorem tailTrace_6962474 : CollatzResearch.WordTrace tailWord_6962474 prefixEnd_6962474 3575095706432097522155171 := by
  unfold tailWord_6962474
  simp only [CollatzResearch.WordTrace]
  refine ⟨63485572244538317183887619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169294859318768845823700317 63485572244538317183887619)
  ·
    refine ⟨95228358366807475775831429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63485572244538317183887619 95228358366807475775831429)
    ·
      refine ⟨17855317193776401707968393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95228358366807475775831429 17855317193776401707968393)
      ·
        refine ⟨13391487895332301280976295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17855317193776401707968393 13391487895332301280976295)
        ·
          refine ⟨20087231842998451921464443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13391487895332301280976295 20087231842998451921464443)
          ·
            refine ⟨30130847764497677882196665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20087231842998451921464443 30130847764497677882196665)
            ·
              refine ⟨22598135823373258411647499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30130847764497677882196665 22598135823373258411647499)
              ·
                refine ⟨33897203735059887617471249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22598135823373258411647499 33897203735059887617471249)
                ·
                  refine ⟨25422902801294915713103437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33897203735059887617471249 25422902801294915713103437)
                  ·
                    refine ⟨9533588550485593392413789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25422902801294915713103437 9533588550485593392413789)
                    ·
                      refine ⟨3575095706432097522155171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9533588550485593392413789 3575095706432097522155171)
                      ·
                        rfl

theorem cell23_6962474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6962474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962474 prefixEnd_6962474 := by exact prefixLift 6962474
  have htrace : WordTrace (prefixWord ++ tailWord_6962474) baseStart_6962474 baseEnd_6962474 := by
    simpa [prefixWord, tailWord_6962474, baseEnd_6962474] using wordTrace_append hprefix tailTrace_6962474
  have hstable : (prefixWord ++ tailWord_6962474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962474).length < 2 ^ (prefixWord ++ tailWord_6962474).sum := by decide
  have hdescent : baseEnd_6962474 < baseStart_6962474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962480 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_6962480 : Nat := 118140960795 + 6962480 * 2 ^ 59
def prefixEnd_6962480 : Nat := 4983230072969 + 3 ^ 40 * 6962480 * 2
def baseEnd_6962480 : Nat := 3575098787316024498680143

theorem tailTrace_6962480 : CollatzResearch.WordTrace tailWord_6962480 prefixEnd_6962480 3575098787316024498680143 := by
  unfold tailWord_6962480
  simp only [CollatzResearch.WordTrace]
  refine ⟨126971253908065765880134447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169295005210754354506845929 126971253908065765880134447)
  ·
    refine ⟨190456880862098648820201671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126971253908065765880134447 190456880862098648820201671)
    ·
      refine ⟨285685321293147973230302507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190456880862098648820201671 285685321293147973230302507)
      ·
        refine ⟨428527981939721959845453761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285685321293147973230302507 428527981939721959845453761)
        ·
          refine ⟨321395986454791469884090321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428527981939721959845453761 321395986454791469884090321)
          ·
            refine ⟨241046989841093602413067741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321395986454791469884090321 241046989841093602413067741)
            ·
              refine ⟨90392621190410100904900403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241046989841093602413067741 90392621190410100904900403)
              ·
                refine ⟨135588931785615151357350605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90392621190410100904900403 135588931785615151357350605)
                ·
                  refine ⟨50845849419605681759006477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135588931785615151357350605 50845849419605681759006477)
                  ·
                    refine ⟨19067193532352130659627429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50845849419605681759006477 19067193532352130659627429)
                    ·
                      refine ⟨3575098787316024498680143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19067193532352130659627429 3575098787316024498680143)
                      ·
                        rfl

theorem cell23_6962480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_6962480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962480 prefixEnd_6962480 := by exact prefixLift 6962480
  have htrace : WordTrace (prefixWord ++ tailWord_6962480) baseStart_6962480 baseEnd_6962480 := by
    simpa [prefixWord, tailWord_6962480, baseEnd_6962480] using wordTrace_append hprefix tailTrace_6962480
  have hstable : (prefixWord ++ tailWord_6962480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962480).length < 2 ^ (prefixWord ++ tailWord_6962480).sum := by decide
  have hdescent : baseEnd_6962480 < baseStart_6962480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962490 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_6962490 : Nat := 118140960795 + 6962490 * 2 ^ 59
def prefixEnd_6962490 : Nat := 4983230072969 + 3 ^ 40 * 6962490 * 2
def baseEnd_6962490 : Nat := 1191701307374189819851699

theorem tailTrace_6962490 : CollatzResearch.WordTrace tailWord_6962490 prefixEnd_6962490 1191701307374189819851699 := by
  unfold tailWord_6962490
  simp only [CollatzResearch.WordTrace]
  refine ⟨63485718136523825867033231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169295248364063535645421949 63485718136523825867033231)
  ·
    refine ⟨95228577204785738800549847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63485718136523825867033231 95228577204785738800549847)
    ·
      refine ⟨142842865807178608200824771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95228577204785738800549847 142842865807178608200824771)
      ·
        refine ⟨214264298710767912301237157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142842865807178608200824771 214264298710767912301237157)
        ·
          refine ⟨40174556008268983556481967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214264298710767912301237157 40174556008268983556481967)
          ·
            refine ⟨60261834012403475334722951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40174556008268983556481967 60261834012403475334722951)
            ·
              refine ⟨90392751018605213002084427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60261834012403475334722951 90392751018605213002084427)
              ·
                refine ⟨135589126527907819503126641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90392751018605213002084427 135589126527907819503126641)
                ·
                  refine ⟨101691844895930864627344981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135589126527907819503126641 101691844895930864627344981)
                  ·
                    refine ⟨1191701307374189819851699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101691844895930864627344981 1191701307374189819851699)
                    ·
                      rfl

theorem cell23_6962490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_6962490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962490 prefixEnd_6962490 := by exact prefixLift 6962490
  have htrace : WordTrace (prefixWord ++ tailWord_6962490) baseStart_6962490 baseEnd_6962490 := by
    simpa [prefixWord, tailWord_6962490, baseEnd_6962490] using wordTrace_append hprefix tailTrace_6962490
  have hstable : (prefixWord ++ tailWord_6962490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962490).length < 2 ^ (prefixWord ++ tailWord_6962490).sum := by decide
  have hdescent : baseEnd_6962490 < baseStart_6962490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962520 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 8]
def baseStart_6962520 : Nat := 118140960795 + 6962520 * 2 ^ 59
def prefixEnd_6962520 : Nat := 4983230072969 + 3 ^ 40 * 6962520 * 2
def baseEnd_6962520 : Nat := 397235480726911593575551

theorem tailTrace_6962520 : CollatzResearch.WordTrace tailWord_6962520 prefixEnd_6962520 397235480726911593575551 := by
  unfold tailWord_6962520
  simp only [CollatzResearch.WordTrace]
  refine ⟨126971983367993309295862507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169295977823991079061150009 126971983367993309295862507)
  ·
    refine ⟨190457975051989963943793761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126971983367993309295862507 190457975051989963943793761)
    ·
      refine ⟨142843481288992472957845321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190457975051989963943793761 142843481288992472957845321)
      ·
        refine ⟨107132610966744354718383991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142843481288992472957845321 107132610966744354718383991)
        ·
          refine ⟨160698916450116532077575987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107132610966744354718383991 160698916450116532077575987)
          ·
            refine ⟨241048374675174798116363981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160698916450116532077575987 241048374675174798116363981)
            ·
              refine ⟨90393140503190549293636493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241048374675174798116363981 90393140503190549293636493)
              ·
                refine ⟨33897427688696455985113685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90393140503190549293636493 33897427688696455985113685)
                ·
                  refine ⟨397235480726911593575551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33897427688696455985113685 397235480726911593575551)
                  ·
                    rfl

theorem cell23_6962520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_6962520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962520 prefixEnd_6962520 := by exact prefixLift 6962520
  have htrace : WordTrace (prefixWord ++ tailWord_6962520) baseStart_6962520 baseEnd_6962520 := by
    simpa [prefixWord, tailWord_6962520, baseEnd_6962520] using wordTrace_append hprefix tailTrace_6962520
  have hstable : (prefixWord ++ tailWord_6962520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962520).length < 2 ^ (prefixWord ++ tailWord_6962520).sum := by decide
  have hdescent : baseEnd_6962520 < baseStart_6962520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962560 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_6962560 : Nat := 118140960795 + 6962560 * 2 ^ 59
def prefixEnd_6962560 : Nat := 4983230072969 + 3 ^ 40 * 6962560 * 2
def baseEnd_6962560 : Nat := 3575139865768384185679775

theorem tailTrace_6962560 : CollatzResearch.WordTrace tailWord_6962560 prefixEnd_6962560 3575139865768384185679775 := by
  unfold tailWord_6962560
  simp only [CollatzResearch.WordTrace]
  refine ⟨126972712827920852711590567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169296950437227803615454089 126972712827920852711590567)
  ·
    refine ⟨190459069241881279067385851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126972712827920852711590567 190459069241881279067385851)
    ·
      refine ⟨285688603862821918601078777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190459069241881279067385851 285688603862821918601078777)
      ·
        refine ⟨214266452897116438950809083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285688603862821918601078777 214266452897116438950809083)
        ·
          refine ⟨321399679345674658426213625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214266452897116438950809083 321399679345674658426213625)
          ·
            refine ⟨241049759509255993819660219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321399679345674658426213625 241049759509255993819660219)
            ·
              refine ⟨361574639263883990729490329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241049759509255993819660219 361574639263883990729490329)
              ·
                refine ⟨271180979447912993047117747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361574639263883990729490329 271180979447912993047117747)
                ·
                  refine ⟨406771469171869489570676621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271180979447912993047117747 406771469171869489570676621)
                  ·
                    refine ⟨152539300939451058589003733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406771469171869489570676621 152539300939451058589003733)
                    ·
                      refine ⟨3575139865768384185679775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152539300939451058589003733 3575139865768384185679775)
                      ·
                        rfl

theorem cell23_6962560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_6962560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962560 prefixEnd_6962560 := by exact prefixLift 6962560
  have htrace : WordTrace (prefixWord ++ tailWord_6962560) baseStart_6962560 baseEnd_6962560 := by
    simpa [prefixWord, tailWord_6962560, baseEnd_6962560] using wordTrace_append hprefix tailTrace_6962560
  have hstable : (prefixWord ++ tailWord_6962560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962560).length < 2 ^ (prefixWord ++ tailWord_6962560).sum := by decide
  have hdescent : baseEnd_6962560 < baseStart_6962560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962621 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_6962621 : Nat := 118140960795 + 6962621 * 2 ^ 59
def prefixEnd_6962621 : Nat := 4983230072969 + 3 ^ 40 * 6962621 * 2
def baseEnd_6962621 : Nat := 3575171188088308447016995

theorem tailTrace_6962621 : CollatzResearch.WordTrace tailWord_6962621 prefixEnd_6962621 3575171188088308447016995 := by
  unfold tailWord_6962621
  simp only [CollatzResearch.WordTrace]
  refine ⟨253947650508620712841151717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169298433672413808560767811 253947650508620712841151717)
  ·
    refine ⟨47615184470366383657715947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253947650508620712841151717 47615184470366383657715947)
    ·
      refine ⟨71422776705549575486573921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47615184470366383657715947 71422776705549575486573921)
      ·
        refine ⟨53567082529162181614930441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71422776705549575486573921 53567082529162181614930441)
        ·
          refine ⟨40175311896871636211197831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53567082529162181614930441 40175311896871636211197831)
          ·
            refine ⟨60262967845307454316796747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40175311896871636211197831 60262967845307454316796747)
            ·
              refine ⟨90394451767961181475195121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60262967845307454316796747 90394451767961181475195121)
              ·
                refine ⟨67795838825970886106396341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90394451767961181475195121 67795838825970886106396341)
                ·
                  refine ⟨6355859889934770572474657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67795838825970886106396341 6355859889934770572474657)
                  ·
                    refine ⟨4766894917451077929355993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6355859889934770572474657 4766894917451077929355993)
                    ·
                      refine ⟨3575171188088308447016995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766894917451077929355993 3575171188088308447016995)
                      ·
                        rfl

theorem cell23_6962621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_6962621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962621 prefixEnd_6962621 := by exact prefixLift 6962621
  have htrace : WordTrace (prefixWord ++ tailWord_6962621) baseStart_6962621 baseEnd_6962621 := by
    simpa [prefixWord, tailWord_6962621, baseEnd_6962621] using wordTrace_append hprefix tailTrace_6962621
  have hstable : (prefixWord ++ tailWord_6962621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962621).length < 2 ^ (prefixWord ++ tailWord_6962621).sum := by decide
  have hdescent : baseEnd_6962621 < baseStart_6962621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962661 : List Nat := [1, 3, 1, 5, 1, 3, 2, 7]
def baseStart_6962661 : Nat := 118140960795 + 6962661 * 2 ^ 59
def prefixEnd_6962661 : Nat := 4983230072969 + 3 ^ 40 * 6962661 * 2
def baseEnd_6962661 : Nat := 132414508419055121870993

theorem tailTrace_6962661 : CollatzResearch.WordTrace tailWord_6962661 prefixEnd_6962661 132414508419055121870993 := by
  unfold tailWord_6962661
  simp only [CollatzResearch.WordTrace]
  refine ⟨253949109428475799672607837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169299406285650533115071891 253949109428475799672607837)
  ·
    refine ⟨95230916035678424877227939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253949109428475799672607837 95230916035678424877227939)
    ·
      refine ⟨142846374053517637315841909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95230916035678424877227939 142846374053517637315841909)
      ·
        refine ⟨13391847567517278498360179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142846374053517637315841909 13391847567517278498360179)
        ·
          refine ⟨20087771351275917747540269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13391847567517278498360179 20087771351275917747540269)
          ·
            refine ⟨7532914256728469155327601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20087771351275917747540269 7532914256728469155327601)
            ·
              refine ⟨5649685692546351866495701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7532914256728469155327601 5649685692546351866495701)
              ·
                refine ⟨132414508419055121870993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5649685692546351866495701 132414508419055121870993)
                ·
                  rfl

theorem cell23_6962661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 7].length) (baseStart_6962661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962661 prefixEnd_6962661 := by exact prefixLift 6962661
  have htrace : WordTrace (prefixWord ++ tailWord_6962661) baseStart_6962661 baseEnd_6962661 := by
    simpa [prefixWord, tailWord_6962661, baseEnd_6962661] using wordTrace_append hprefix tailTrace_6962661
  have hstable : (prefixWord ++ tailWord_6962661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962661).length < 2 ^ (prefixWord ++ tailWord_6962661).sum := by decide
  have hdescent : baseEnd_6962661 < baseStart_6962661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962687 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 2, 6]
def baseStart_6962687 : Nat := 118140960795 + 6962687 * 2 ^ 59
def prefixEnd_6962687 : Nat := 4983230072969 + 3 ^ 40 * 6962687 * 2
def baseEnd_6962687 : Nat := 1191735025937168396263897

theorem tailTrace_6962687 : CollatzResearch.WordTrace tailWord_6962687 prefixEnd_6962687 1191735025937168396263897 := by
  unfold tailWord_6962687
  simp only [CollatzResearch.WordTrace]
  refine ⟨253950057726381606113054315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169300038484254404075369543 253950057726381606113054315)
  ·
    refine ⟨380925086589572409169581473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253950057726381606113054315 380925086589572409169581473)
    ·
      refine ⟨285693814942179306877186105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380925086589572409169581473 285693814942179306877186105)
      ·
        refine ⟨214270361206634480157889579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285693814942179306877186105 214270361206634480157889579)
        ·
          refine ⟨321405541809951720236834369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214270361206634480157889579 321405541809951720236834369)
          ·
            refine ⟨241054156357463790177625777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321405541809951720236834369 241054156357463790177625777)
            ·
              refine ⟨180790617268097842633219333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241054156357463790177625777 180790617268097842633219333)
              ·
                refine ⟨33898240737768345493728625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180790617268097842633219333 33898240737768345493728625)
                ·
                  refine ⟨25423680553326259120296469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33898240737768345493728625 25423680553326259120296469)
                  ·
                    refine ⟨1191735025937168396263897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25423680553326259120296469 1191735025937168396263897)
                    ·
                      rfl

theorem cell23_6962687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_6962687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962687 prefixEnd_6962687 := by exact prefixLift 6962687
  have htrace : WordTrace (prefixWord ++ tailWord_6962687) baseStart_6962687 baseEnd_6962687 := by
    simpa [prefixWord, tailWord_6962687, baseEnd_6962687] using wordTrace_append hprefix tailTrace_6962687
  have hstable : (prefixWord ++ tailWord_6962687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962687).length < 2 ^ (prefixWord ++ tailWord_6962687).sum := by decide
  have hdescent : baseEnd_6962687 < baseStart_6962687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962697 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_6962697 : Nat := 118140960795 + 6962697 * 2 ^ 59
def prefixEnd_6962697 : Nat := 4983230072969 + 3 ^ 40 * 6962697 * 2
def baseEnd_6962697 : Nat := 3575210212618050149666645

theorem tailTrace_6962697 : CollatzResearch.WordTrace tailWord_6962697 prefixEnd_6962697 3575210212618050149666645 := by
  unfold tailWord_6962697
  simp only [CollatzResearch.WordTrace]
  refine ⟨253950422456345377820918345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169300281637563585213945563 253950422456345377820918345)
  ·
    refine ⟨190462816842259033365688759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253950422456345377820918345 190462816842259033365688759)
    ·
      refine ⟨285694225263388550048533139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190462816842259033365688759 285694225263388550048533139)
      ·
        refine ⟨428541337895082825072799709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285694225263388550048533139 428541337895082825072799709)
        ·
          refine ⟨160703001710656059402299891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428541337895082825072799709 160703001710656059402299891)
          ·
            refine ⟨241054502565984089103449837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160703001710656059402299891 241054502565984089103449837)
            ·
              refine ⟨90395438462244033413793689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241054502565984089103449837 90395438462244033413793689)
              ·
                refine ⟨67796578846683025060345267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90395438462244033413793689 67796578846683025060345267)
                ·
                  refine ⟨101694868270024537590517901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67796578846683025060345267 101694868270024537590517901)
                  ·
                    refine ⟨38135575601259201596444213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101694868270024537590517901 38135575601259201596444213)
                    ·
                      refine ⟨3575210212618050149666645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38135575601259201596444213 3575210212618050149666645)
                      ·
                        rfl

theorem cell23_6962697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_6962697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962697 prefixEnd_6962697 := by exact prefixLift 6962697
  have htrace : WordTrace (prefixWord ++ tailWord_6962697) baseStart_6962697 baseEnd_6962697 := by
    simpa [prefixWord, tailWord_6962697, baseEnd_6962697] using wordTrace_append hprefix tailTrace_6962697
  have hstable : (prefixWord ++ tailWord_6962697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962697).length < 2 ^ (prefixWord ++ tailWord_6962697).sum := by decide
  have hdescent : baseEnd_6962697 < baseStart_6962697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962745 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6962745 : Nat := 118140960795 + 6962745 * 2 ^ 59
def prefixEnd_6962745 : Nat := 4983230072969 + 3 ^ 40 * 6962745 * 2
def baseEnd_6962745 : Nat := 3575234859689465961866425

theorem tailTrace_6962745 : CollatzResearch.WordTrace tailWord_6962745 prefixEnd_6962745 3575234859689465961866425 := by
  unfold tailWord_6962745
  simp only [CollatzResearch.WordTrace]
  refine ⟨253952173160171482018665689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169301448773447654679110459 253952173160171482018665689)
  ·
    refine ⟨190464129870128611513999267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253952173160171482018665689 190464129870128611513999267)
    ·
      refine ⟨285696194805192917270998901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190464129870128611513999267 285696194805192917270998901)
      ·
        refine ⟨26784018262986835994156147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285696194805192917270998901 26784018262986835994156147)
        ·
          refine ⟨40176027394480253991234221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26784018262986835994156147 40176027394480253991234221)
          ·
            refine ⟨15066010272930095246712833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40176027394480253991234221 15066010272930095246712833)
            ·
              refine ⟨11299507704697571435034625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15066010272930095246712833 11299507704697571435034625)
              ·
                refine ⟨8474630778523178576275969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11299507704697571435034625 8474630778523178576275969)
                ·
                  refine ⟨6355973083892383932206977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474630778523178576275969 6355973083892383932206977)
                  ·
                    refine ⟨4766979812919287949155233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6355973083892383932206977 4766979812919287949155233)
                    ·
                      refine ⟨3575234859689465961866425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766979812919287949155233 3575234859689465961866425)
                      ·
                        rfl

theorem cell23_6962745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6962745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962745 prefixEnd_6962745 := by exact prefixLift 6962745
  have htrace : WordTrace (prefixWord ++ tailWord_6962745) baseStart_6962745 baseEnd_6962745 := by
    simpa [prefixWord, tailWord_6962745, baseEnd_6962745] using wordTrace_append hprefix tailTrace_6962745
  have hstable : (prefixWord ++ tailWord_6962745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962745).length < 2 ^ (prefixWord ++ tailWord_6962745).sum := by decide
  have hdescent : baseEnd_6962745 < baseStart_6962745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962751 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 5]
def baseStart_6962751 : Nat := 118140960795 + 6962751 * 2 ^ 59
def prefixEnd_6962751 : Nat := 4983230072969 + 3 ^ 40 * 6962751 * 2
def baseEnd_6962751 : Nat := 397248660063710326487933

theorem tailTrace_6962751 : CollatzResearch.WordTrace tailWord_6962751 prefixEnd_6962751 397248660063710326487933 := by
  unfold tailWord_6962751
  simp only [CollatzResearch.WordTrace]
  refine ⟨253952391998149745043384107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169301594665433163362256071 253952391998149745043384107)
  ·
    refine ⟨380928587997224617565076161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253952391998149745043384107 380928587997224617565076161)
    ·
      refine ⟨285696440997918463173807121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380928587997224617565076161 285696440997918463173807121)
      ·
        refine ⟨214272330748438847380355341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285696440997918463173807121 214272330748438847380355341)
        ·
          refine ⟨80352124030664567767633253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214272330748438847380355341 80352124030664567767633253)
          ·
            refine ⟨15066023255749606456431235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80352124030664567767633253 15066023255749606456431235)
            ·
              refine ⟨22599034883624409684646853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15066023255749606456431235 22599034883624409684646853)
              ·
                refine ⟨4237319040679576815871285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22599034883624409684646853 4237319040679576815871285)
                ·
                  refine ⟨397248660063710326487933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4237319040679576815871285 397248660063710326487933)
                  ·
                    rfl

theorem cell23_6962751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 5].length) (baseStart_6962751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962751 prefixEnd_6962751 := by exact prefixLift 6962751
  have htrace : WordTrace (prefixWord ++ tailWord_6962751) baseStart_6962751 baseEnd_6962751 := by
    simpa [prefixWord, tailWord_6962751, baseEnd_6962751] using wordTrace_append hprefix tailTrace_6962751
  have hstable : (prefixWord ++ tailWord_6962751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962751).length < 2 ^ (prefixWord ++ tailWord_6962751).sum := by decide
  have hdescent : baseEnd_6962751 < baseStart_6962751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962811 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 3, 4]
def baseStart_6962811 : Nat := 118140960795 + 6962811 * 2 ^ 59
def prefixEnd_6962811 : Nat := 4983230072969 + 3 ^ 40 * 6962811 * 2
def baseEnd_6962811 : Nat := 1191756249804220901213707

theorem tailTrace_6962811 : CollatzResearch.WordTrace tailWord_6962811 prefixEnd_6962811 1191756249804220901213707 := by
  unfold tailWord_6962811
  simp only [CollatzResearch.WordTrace]
  refine ⟨253954580377932375290568287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169303053585288250193712191 253954580377932375290568287)
  ·
    refine ⟨380931870566898562935852431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253954580377932375290568287 380931870566898562935852431)
    ·
      refine ⟨571397805850347844403778647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380931870566898562935852431 571397805850347844403778647)
      ·
        refine ⟨857096708775521766605667971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571397805850347844403778647 857096708775521766605667971)
        ·
          refine ⟨1285645063163282649908501957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857096708775521766605667971 1285645063163282649908501957)
          ·
            refine ⟨241058449343115496857844117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1285645063163282649908501957 241058449343115496857844117)
            ·
              refine ⟨11299614812958538915211443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241058449343115496857844117 11299614812958538915211443)
              ·
                refine ⟨16949422219437808372817165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11299614812958538915211443 16949422219437808372817165)
                ·
                  refine ⟨6356033332289178139806437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16949422219437808372817165 6356033332289178139806437)
                  ·
                    refine ⟨1191756249804220901213707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356033332289178139806437 1191756249804220901213707)
                    ·
                      rfl

theorem cell23_6962811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 4].length) (baseStart_6962811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962811 prefixEnd_6962811 := by exact prefixLift 6962811
  have htrace : WordTrace (prefixWord ++ tailWord_6962811) baseStart_6962811 baseEnd_6962811 := by
    simpa [prefixWord, tailWord_6962811, baseEnd_6962811] using wordTrace_append hprefix tailTrace_6962811
  have hstable : (prefixWord ++ tailWord_6962811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962811).length < 2 ^ (prefixWord ++ tailWord_6962811).sum := by decide
  have hdescent : baseEnd_6962811 < baseStart_6962811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962862 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6962862 : Nat := 118140960795 + 6962862 * 2 ^ 59
def prefixEnd_6962862 : Nat := 4983230072969 + 3 ^ 40 * 6962862 * 2
def baseEnd_6962862 : Nat := 1191764978975347334701129

theorem tailTrace_6962862 : CollatzResearch.WordTrace tailWord_6962862 prefixEnd_6962862 1191764978975347334701129 := by
  unfold tailWord_6962862
  simp only [CollatzResearch.WordTrace]
  refine ⟨31744555062593451375084355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169304293667165074000449893 31744555062593451375084355)
  ·
    refine ⟨47616832593890177062626533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31744555062593451375084355 47616832593890177062626533)
    ·
      refine ⟨8928156111354408199242475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47616832593890177062626533 8928156111354408199242475)
      ·
        refine ⟨13392234167031612298863713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928156111354408199242475 13392234167031612298863713)
        ·
          refine ⟨10044175625273709224147785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13392234167031612298863713 10044175625273709224147785)
          ·
            refine ⟨7533131718955281918110839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10044175625273709224147785 7533131718955281918110839)
            ·
              refine ⟨11299697578432922877166259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533131718955281918110839 11299697578432922877166259)
              ·
                refine ⟨16949546367649384315749389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11299697578432922877166259 16949546367649384315749389)
                ·
                  refine ⟨6356079887868519118406021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16949546367649384315749389 6356079887868519118406021)
                  ·
                    refine ⟨1191764978975347334701129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356079887868519118406021 1191764978975347334701129)
                    ·
                      rfl

theorem cell23_6962862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6962862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962862 prefixEnd_6962862 := by exact prefixLift 6962862
  have htrace : WordTrace (prefixWord ++ tailWord_6962862) baseStart_6962862 baseEnd_6962862 := by
    simpa [prefixWord, tailWord_6962862, baseEnd_6962862] using wordTrace_append hprefix tailTrace_6962862
  have hstable : (prefixWord ++ tailWord_6962862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962862).length < 2 ^ (prefixWord ++ tailWord_6962862).sum := by decide
  have hdescent : baseEnd_6962862 < baseStart_6962862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962891 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 6, 2]
def baseStart_6962891 : Nat := 118140960795 + 6962891 * 2 ^ 59
def prefixEnd_6962891 : Nat := 4983230072969 + 3 ^ 40 * 6962891 * 2
def baseEnd_6962891 : Nat := 3575309827865022390640753

theorem tailTrace_6962891 : CollatzResearch.WordTrace tailWord_6962891 prefixEnd_6962891 3575309827865022390640753 := by
  unfold tailWord_6962891
  simp only [CollatzResearch.WordTrace]
  refine ⟨253957498217642548953480527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169304998811761699302320351 253957498217642548953480527)
  ·
    refine ⟨380936247326463823430220791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253957498217642548953480527 380936247326463823430220791)
    ·
      refine ⟨571404370989695735145331187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380936247326463823430220791 571404370989695735145331187)
      ·
        refine ⟨857106556484543602717996781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571404370989695735145331187 857106556484543602717996781)
        ·
          refine ⟨321414958681703851019248793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 857106556484543602717996781 321414958681703851019248793)
          ·
            refine ⟨241061219011277888264436595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321414958681703851019248793 241061219011277888264436595)
            ·
              refine ⟨361591828516916832396654893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241061219011277888264436595 361591828516916832396654893)
              ·
                refine ⟨135596935693843812148745585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361591828516916832396654893 135596935693843812148745585)
                ·
                  refine ⟨101697701770382859111559189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135596935693843812148745585 101697701770382859111559189)
                  ·
                    refine ⟨4767079770486696520854337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101697701770382859111559189 4767079770486696520854337)
                    ·
                      refine ⟨3575309827865022390640753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767079770486696520854337 3575309827865022390640753)
                      ·
                        rfl

theorem cell23_6962891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6, 2].length) (baseStart_6962891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962891 prefixEnd_6962891 := by exact prefixLift 6962891
  have htrace : WordTrace (prefixWord ++ tailWord_6962891) baseStart_6962891 baseEnd_6962891 := by
    simpa [prefixWord, tailWord_6962891, baseEnd_6962891] using wordTrace_append hprefix tailTrace_6962891
  have hstable : (prefixWord ++ tailWord_6962891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962891).length < 2 ^ (prefixWord ++ tailWord_6962891).sum := by decide
  have hdescent : baseEnd_6962891 < baseStart_6962891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962914 : List Nat := [3, 3, 17]
def baseStart_6962914 : Nat := 118140960795 + 6962914 * 2 ^ 59
def prefixEnd_6962914 : Nat := 4983230072969 + 3 ^ 40 * 6962914 * 2
def baseEnd_6962914 : Nat := 544935472934015516027

theorem tailTrace_6962914 : CollatzResearch.WordTrace tailWord_6962914 prefixEnd_6962914 544935472934015516027 := by
  unfold tailWord_6962914
  simp only [CollatzResearch.WordTrace]
  refine ⟨63489584274139805970391949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169305558064372815921045197 63489584274139805970391949)
  ·
    refine ⟨23808594102802427238896981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63489584274139805970391949 23808594102802427238896981)
    ·
      refine ⟨544935472934015516027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 23808594102802427238896981 544935472934015516027)
      ·
        rfl

theorem cell23_6962914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 17].length) (baseStart_6962914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962914 prefixEnd_6962914 := by exact prefixLift 6962914
  have htrace : WordTrace (prefixWord ++ tailWord_6962914) baseStart_6962914 baseEnd_6962914 := by
    simpa [prefixWord, tailWord_6962914, baseEnd_6962914] using wordTrace_append hprefix tailTrace_6962914
  have hstable : (prefixWord ++ tailWord_6962914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962914).length < 2 ^ (prefixWord ++ tailWord_6962914).sum := by decide
  have hdescent : baseEnd_6962914 < baseStart_6962914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962919 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6962919 : Nat := 118140960795 + 6962919 * 2 ^ 59
def prefixEnd_6962919 : Nat := 4983230072969 + 3 ^ 40 * 6962919 * 2
def baseEnd_6962919 : Nat := 3575324205323348281090625

theorem tailTrace_6962919 : CollatzResearch.WordTrace tailWord_6962919 prefixEnd_6962919 3575324205323348281090625 := by
  unfold tailWord_6962919
  simp only [CollatzResearch.WordTrace]
  refine ⟨253958519461541109735499811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169305679641027406490333207 253958519461541109735499811)
  ·
    refine ⟨380937779192311664603249717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253958519461541109735499811 380937779192311664603249717)
    ·
      refine ⟨35712916799279218556554661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 380937779192311664603249717 35712916799279218556554661)
      ·
        refine ⟨6696171899864853479353999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35712916799279218556554661 6696171899864853479353999)
        ·
          refine ⟨10044257849797280219030999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6696171899864853479353999 10044257849797280219030999)
          ·
            refine ⟨15066386774695920328546499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10044257849797280219030999 15066386774695920328546499)
            ·
              refine ⟨22599580162043880492819749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15066386774695920328546499 22599580162043880492819749)
              ·
                refine ⟨4237421280383227592403703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22599580162043880492819749 4237421280383227592403703)
                ·
                  refine ⟨6356131920574841388605555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237421280383227592403703 6356131920574841388605555)
                  ·
                    refine ⟨9534197880862262082908333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6356131920574841388605555 9534197880862262082908333)
                    ·
                      refine ⟨3575324205323348281090625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534197880862262082908333 3575324205323348281090625)
                      ·
                        rfl

theorem cell23_6962919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6962919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962919 prefixEnd_6962919 := by exact prefixLift 6962919
  have htrace : WordTrace (prefixWord ++ tailWord_6962919) baseStart_6962919 baseEnd_6962919 := by
    simpa [prefixWord, tailWord_6962919, baseEnd_6962919] using wordTrace_append hprefix tailTrace_6962919
  have hstable : (prefixWord ++ tailWord_6962919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962919).length < 2 ^ (prefixWord ++ tailWord_6962919).sum := by decide
  have hdescent : baseEnd_6962919 < baseStart_6962919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962948 : List Nat := [2, 3, 2, 2, 1, 3, 3, 7]
def baseStart_6962948 : Nat := 118140960795 + 6962948 * 2 ^ 59
def prefixEnd_6962948 : Nat := 4983230072969 + 3 ^ 40 * 6962948 * 2
def baseEnd_6962948 : Nat := 132419966528234395097333

theorem tailTrace_6962948 : CollatzResearch.WordTrace tailWord_6962948 prefixEnd_6962948 132419966528234395097333 := by
  unfold tailWord_6962948
  simp only [CollatzResearch.WordTrace]
  refine ⟨126979788589218023844152749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169306384785624031792203665 126979788589218023844152749)
  ·
    refine ⟨47617420720956758941557281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126979788589218023844152749 47617420720956758941557281)
    ·
      refine ⟨35713065540717569206167961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47617420720956758941557281 35713065540717569206167961)
      ·
        refine ⟨26784799155538176904625971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35713065540717569206167961 26784799155538176904625971)
        ·
          refine ⟨40177198733307265356938957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26784799155538176904625971 40177198733307265356938957)
          ·
            refine ⟨15066449524990224508852109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40177198733307265356938957 15066449524990224508852109)
            ·
              refine ⟨5649918571871334190819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15066449524990224508852109 5649918571871334190819541)
              ·
                refine ⟨132419966528234395097333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5649918571871334190819541 132419966528234395097333)
                ·
                  rfl

theorem cell23_6962948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 7].length) (baseStart_6962948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962948 prefixEnd_6962948 := by exact prefixLift 6962948
  have htrace : WordTrace (prefixWord ++ tailWord_6962948) baseStart_6962948 baseEnd_6962948 := by
    simpa [prefixWord, tailWord_6962948, baseEnd_6962948] using wordTrace_append hprefix tailTrace_6962948
  have hstable : (prefixWord ++ tailWord_6962948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962948).length < 2 ^ (prefixWord ++ tailWord_6962948).sum := by decide
  have hdescent : baseEnd_6962948 < baseStart_6962948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962958 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_6962958 : Nat := 118140960795 + 6962958 * 2 ^ 59
def prefixEnd_6962958 : Nat := 4983230072969 + 3 ^ 40 * 6962958 * 2
def baseEnd_6962958 : Nat := 3575344231068873628502945

theorem tailTrace_6962958 : CollatzResearch.WordTrace tailWord_6962958 prefixEnd_6962958 3575344231068873628502945 := by
  unfold tailWord_6962958
  simp only [CollatzResearch.WordTrace]
  refine ⟨31744992738549977424521191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169306627938933212930779685 31744992738549977424521191)
  ·
    refine ⟨47617489107824966136781787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31744992738549977424521191 47617489107824966136781787)
    ·
      refine ⟨71426233661737449205172681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47617489107824966136781787 71426233661737449205172681)
      ·
        refine ⟨53569675246303086903879511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71426233661737449205172681 53569675246303086903879511)
        ·
          refine ⟨80354512869454630355819267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53569675246303086903879511 80354512869454630355819267)
          ·
            refine ⟨120531769304181945533728901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80354512869454630355819267 120531769304181945533728901)
            ·
              refine ⟨22599706744534114787574169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120531769304181945533728901 22599706744534114787574169)
              ·
                refine ⟨16949780058400586090680627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22599706744534114787574169 16949780058400586090680627)
                ·
                  refine ⟨25424670087600879136020941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16949780058400586090680627 25424670087600879136020941)
                  ·
                    refine ⟨9534251282850329676007853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25424670087600879136020941 9534251282850329676007853)
                    ·
                      refine ⟨3575344231068873628502945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534251282850329676007853 3575344231068873628502945)
                      ·
                        rfl

theorem cell23_6962958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_6962958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962958 prefixEnd_6962958 := by exact prefixLift 6962958
  have htrace : WordTrace (prefixWord ++ tailWord_6962958) baseStart_6962958 baseEnd_6962958 := by
    simpa [prefixWord, tailWord_6962958, baseEnd_6962958] using wordTrace_append hprefix tailTrace_6962958
  have hstable : (prefixWord ++ tailWord_6962958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962958).length < 2 ^ (prefixWord ++ tailWord_6962958).sum := by decide
  have hdescent : baseEnd_6962958 < baseStart_6962958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6962962 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6962962 : Nat := 118140960795 + 6962962 * 2 ^ 59
def prefixEnd_6962962 : Nat := 4983230072969 + 3 ^ 40 * 6962962 * 2
def baseEnd_6962962 : Nat := 3575346284991491612852927

theorem tailTrace_6962962 : CollatzResearch.WordTrace tailWord_6962962 prefixEnd_6962962 3575346284991491612852927 := by
  unfold tailWord_6962962
  simp only [CollatzResearch.WordTrace]
  refine ⟨63490021950096332019828785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169306725200256885386210093 63490021950096332019828785)
  ·
    refine ⟨47617516462572249014871589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63490021950096332019828785 47617516462572249014871589)
    ·
      refine ⟨8928284336732296690288423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47617516462572249014871589 8928284336732296690288423)
      ·
        refine ⟨13392426505098445035432635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928284336732296690288423 13392426505098445035432635)
        ·
          refine ⟨20088639757647667553148953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13392426505098445035432635 20088639757647667553148953)
          ·
            refine ⟨15066479818235750664861715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20088639757647667553148953 15066479818235750664861715)
            ·
              refine ⟨22599719727353625997292573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15066479818235750664861715 22599719727353625997292573)
              ·
                refine ⟨8474894897757609748984715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22599719727353625997292573 8474894897757609748984715)
                ·
                  refine ⟨12712342346636414623477073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474894897757609748984715 12712342346636414623477073)
                  ·
                    refine ⟨9534256759977310967607805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12712342346636414623477073 9534256759977310967607805)
                    ·
                      refine ⟨3575346284991491612852927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534256759977310967607805 3575346284991491612852927)
                      ·
                        rfl

theorem cell23_6962962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6962962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6962962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6962962 prefixEnd_6962962 := by exact prefixLift 6962962
  have htrace : WordTrace (prefixWord ++ tailWord_6962962) baseStart_6962962 baseEnd_6962962 := by
    simpa [prefixWord, tailWord_6962962, baseEnd_6962962] using wordTrace_append hprefix tailTrace_6962962
  have hstable : (prefixWord ++ tailWord_6962962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6962962).length < 2 ^ (prefixWord ++ tailWord_6962962).sum := by decide
  have hdescent : baseEnd_6962962 < baseStart_6962962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6962962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963002 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2]
def baseStart_6963002 : Nat := 118140960795 + 6963002 * 2 ^ 59
def prefixEnd_6963002 : Nat := 4983230072969 + 3 ^ 40 * 6963002 * 2
def baseEnd_6963002 : Nat := 3575366824217671456352743

theorem tailTrace_6963002 : CollatzResearch.WordTrace tailWord_6963002 prefixEnd_6963002 3575366824217671456352743 := by
  unfold tailWord_6963002
  simp only [CollatzResearch.WordTrace]
  refine ⟨63490386680060103727692815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169307697813493609940514173 63490386680060103727692815)
  ·
    refine ⟨95235580020090155591539223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63490386680060103727692815 95235580020090155591539223)
    ·
      refine ⟨142853370030135233387308835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95235580020090155591539223 142853370030135233387308835)
      ·
        refine ⟨214280055045202850080963253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142853370030135233387308835 214280055045202850080963253)
        ·
          refine ⟨20088755160487767195090305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214280055045202850080963253 20088755160487767195090305)
          ·
            refine ⟨15066566370365825396317729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20088755160487767195090305 15066566370365825396317729)
            ·
              refine ⟨11299924777774369047238297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15066566370365825396317729 11299924777774369047238297)
              ·
                refine ⟨8474943583330776785428723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11299924777774369047238297 8474943583330776785428723)
                ·
                  refine ⟨12712415374996165178143085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474943583330776785428723 12712415374996165178143085)
                  ·
                    refine ⟨4767155765623561941803657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12712415374996165178143085 4767155765623561941803657)
                    ·
                      refine ⟨3575366824217671456352743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767155765623561941803657 3575366824217671456352743)
                      ·
                        rfl

theorem cell23_6963002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_6963002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963002 prefixEnd_6963002 := by exact prefixLift 6963002
  have htrace : WordTrace (prefixWord ++ tailWord_6963002) baseStart_6963002 baseEnd_6963002 := by
    simpa [prefixWord, tailWord_6963002, baseEnd_6963002] using wordTrace_append hprefix tailTrace_6963002
  have hstable : (prefixWord ++ tailWord_6963002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963002).length < 2 ^ (prefixWord ++ tailWord_6963002).sum := by decide
  have hdescent : baseEnd_6963002 < baseStart_6963002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963015 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_6963015 : Nat := 118140960795 + 6963015 * 2 ^ 59
def prefixEnd_6963015 : Nat := 4983230072969 + 3 ^ 40 * 6963015 * 2
def baseEnd_6963015 : Nat := 3575373499466179905490183

theorem tailTrace_6963015 : CollatzResearch.WordTrace tailWord_6963015 prefixEnd_6963015 3575373499466179905490183 := by
  unfold tailWord_6963015
  simp only [CollatzResearch.WordTrace]
  refine ⟨253962020869193318130994499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169308013912795545420662999 253962020869193318130994499)
  ·
    refine ⟨380943031303789977196491749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253962020869193318130994499 380943031303789977196491749)
    ·
      refine ⟨71426818369460620724342203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380943031303789977196491749 71426818369460620724342203)
      ·
        refine ⟨107140227554190931086513305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71426818369460620724342203 107140227554190931086513305)
        ·
          refine ⟨80355170665643198314884979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107140227554190931086513305 80355170665643198314884979)
          ·
            refine ⟨120532755998464797472327469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80355170665643198314884979 120532755998464797472327469)
            ·
              refine ⟨45199783499424299052122801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120532755998464797472327469 45199783499424299052122801)
              ·
                refine ⟨33899837624568224289092101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45199783499424299052122801 33899837624568224289092101)
                ·
                  refine ⟨6356219554606542054204769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33899837624568224289092101 6356219554606542054204769)
                  ·
                    refine ⟨4767164665954906540653577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6356219554606542054204769 4767164665954906540653577)
                    ·
                      refine ⟨3575373499466179905490183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767164665954906540653577 3575373499466179905490183)
                      ·
                        rfl

theorem cell23_6963015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_6963015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963015 prefixEnd_6963015 := by exact prefixLift 6963015
  have htrace : WordTrace (prefixWord ++ tailWord_6963015) baseStart_6963015 baseEnd_6963015 := by
    simpa [prefixWord, tailWord_6963015, baseEnd_6963015] using wordTrace_append hprefix tailTrace_6963015
  have hstable : (prefixWord ++ tailWord_6963015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963015).length < 2 ^ (prefixWord ++ tailWord_6963015).sum := by decide
  have hdescent : baseEnd_6963015 < baseStart_6963015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963048 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6963048 : Nat := 118140960795 + 6963048 * 2 ^ 59
def prefixEnd_6963048 : Nat := 4983230072969 + 3 ^ 40 * 6963048 * 2
def baseEnd_6963048 : Nat := 3575390444327778276377531

theorem tailTrace_6963048 : CollatzResearch.WordTrace tailWord_6963048 prefixEnd_6963048 3575390444327778276377531 := by
  unfold tailWord_6963048
  simp only [CollatzResearch.WordTrace]
  refine ⟨126981612239036882383472899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169308816318715843177963865 126981612239036882383472899)
  ·
    refine ⟨190472418358555323575209349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126981612239036882383472899 190472418358555323575209349)
    ·
      refine ⟨35713578442229123170351753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190472418358555323575209349 35713578442229123170351753)
      ·
        refine ⟨26785183831671842377763815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35713578442229123170351753 26785183831671842377763815)
        ·
          refine ⟨40177775747507763566645723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26785183831671842377763815 40177775747507763566645723)
          ·
            refine ⟨60266663621261645349968585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40177775747507763566645723 60266663621261645349968585)
            ·
              refine ⟨45199997715946234012476439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60266663621261645349968585 45199997715946234012476439)
              ·
                refine ⟨67799996573919351018714659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45199997715946234012476439 67799996573919351018714659)
                ·
                  refine ⟨101699994860879026528071989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67799996573919351018714659 101699994860879026528071989)
                  ·
                    refine ⟨9534374518207408737006749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101699994860879026528071989 9534374518207408737006749)
                    ·
                      refine ⟨3575390444327778276377531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534374518207408737006749 3575390444327778276377531)
                      ·
                        rfl

theorem cell23_6963048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6963048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963048 prefixEnd_6963048 := by exact prefixLift 6963048
  have htrace : WordTrace (prefixWord ++ tailWord_6963048) baseStart_6963048 baseEnd_6963048 := by
    simpa [prefixWord, tailWord_6963048, baseEnd_6963048] using wordTrace_append hprefix tailTrace_6963048
  have hstable : (prefixWord ++ tailWord_6963048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963048).length < 2 ^ (prefixWord ++ tailWord_6963048).sum := by decide
  have hdescent : baseEnd_6963048 < baseStart_6963048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963051 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 6, 5]
def baseStart_6963051 : Nat := 118140960795 + 6963051 * 2 ^ 59
def prefixEnd_6963051 : Nat := 4983230072969 + 3 ^ 40 * 6963051 * 2
def baseEnd_6963051 : Nat := 1191797328256580588213339

theorem tailTrace_6963051 : CollatzResearch.WordTrace tailWord_6963051 prefixEnd_6963051 1191797328256580588213339 := by
  unfold tailWord_6963051
  simp only [CollatzResearch.WordTrace]
  refine ⟨253963333897062896279305007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169308889264708597519536671 253963333897062896279305007)
  ·
    refine ⟨380945000845594344418957511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253963333897062896279305007 380945000845594344418957511)
    ·
      refine ⟨571417501268391516628436267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380945000845594344418957511 571417501268391516628436267)
      ·
        refine ⟨857126251902587274942654401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571417501268391516628436267 857126251902587274942654401)
        ·
          refine ⟨642844688926940456206990801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857126251902587274942654401 642844688926940456206990801)
          ·
            refine ⟨482133516695205342155243101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642844688926940456206990801 482133516695205342155243101)
            ·
              refine ⟨180800068760702003308216163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482133516695205342155243101 180800068760702003308216163)
              ·
                refine ⟨271200103141053004962324245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180800068760702003308216163 271200103141053004962324245)
                ·
                  refine ⟨12712504834736859607608949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 271200103141053004962324245 12712504834736859607608949)
                  ·
                    refine ⟨1191797328256580588213339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12712504834736859607608949 1191797328256580588213339)
                    ·
                      rfl

theorem cell23_6963051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 5].length) (baseStart_6963051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963051 prefixEnd_6963051 := by exact prefixLift 6963051
  have htrace : WordTrace (prefixWord ++ tailWord_6963051) baseStart_6963051 baseEnd_6963051 := by
    simpa [prefixWord, tailWord_6963051, baseEnd_6963051] using wordTrace_append hprefix tailTrace_6963051
  have hstable : (prefixWord ++ tailWord_6963051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963051).length < 2 ^ (prefixWord ++ tailWord_6963051).sum := by decide
  have hdescent : baseEnd_6963051 < baseStart_6963051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963125 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_6963125 : Nat := 118140960795 + 6963125 * 2 ^ 59
def prefixEnd_6963125 : Nat := 4983230072969 + 3 ^ 40 * 6963125 * 2
def baseEnd_6963125 : Nat := 3575429982338174475114677

theorem tailTrace_6963125 : CollatzResearch.WordTrace tailWord_6963125 prefixEnd_6963125 3575429982338174475114677 := by
  unfold tailWord_6963125
  simp only [CollatzResearch.WordTrace]
  refine ⟨253966032898794806917498829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169310688599196537944999219 253966032898794806917498829)
  ·
    refine ⟨95237262337048052594062061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253966032898794806917498829 95237262337048052594062061)
    ·
      refine ⟨35713973376393019722773273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95237262337048052594062061 35713973376393019722773273)
      ·
        refine ⟨26785480032294764792079955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35713973376393019722773273 26785480032294764792079955)
        ·
          refine ⟨40178220048442147188119933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26785480032294764792079955 40178220048442147188119933)
          ·
            refine ⟨15066832518165805195544975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40178220048442147188119933 15066832518165805195544975)
            ·
              refine ⟨22600248777248707793317463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15066832518165805195544975 22600248777248707793317463)
              ·
                refine ⟨33900373165873061689976195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22600248777248707793317463 33900373165873061689976195)
                ·
                  refine ⟨50850559748809592534964293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33900373165873061689976195 50850559748809592534964293)
                  ·
                    refine ⟨9534479952901798600305805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50850559748809592534964293 9534479952901798600305805)
                    ·
                      refine ⟨3575429982338174475114677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534479952901798600305805 3575429982338174475114677)
                      ·
                        rfl

theorem cell23_6963125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_6963125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963125 prefixEnd_6963125 := by exact prefixLift 6963125
  have htrace : WordTrace (prefixWord ++ tailWord_6963125) baseStart_6963125 baseEnd_6963125 := by
    simpa [prefixWord, tailWord_6963125, baseEnd_6963125] using wordTrace_append hprefix tailTrace_6963125
  have hstable : (prefixWord ++ tailWord_6963125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963125).length < 2 ^ (prefixWord ++ tailWord_6963125).sum := by decide
  have hdescent : baseEnd_6963125 < baseStart_6963125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963131 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_6963131 : Nat := 118140960795 + 6963131 * 2 ^ 59
def prefixEnd_6963131 : Nat := 4983230072969 + 3 ^ 40 * 6963131 * 2
def baseEnd_6963131 : Nat := 3575433063222101451639649

theorem tailTrace_6963131 : CollatzResearch.WordTrace tailWord_6963131 prefixEnd_6963131 3575433063222101451639649 := by
  unfold tailWord_6963131
  simp only [CollatzResearch.WordTrace]
  refine ⟨253966251736773069942217247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169310834491182046628144831 253966251736773069942217247)
  ·
    refine ⟨380949377605159604913325871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253966251736773069942217247 380949377605159604913325871)
    ·
      refine ⟨571424066407739407369988807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380949377605159604913325871 571424066407739407369988807)
      ·
        refine ⟨857136099611609111054983211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571424066407739407369988807 857136099611609111054983211)
        ·
          refine ⟨1285704149417413666582474817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857136099611609111054983211 1285704149417413666582474817)
          ·
            refine ⟨964278112063060249936856113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285704149417413666582474817 964278112063060249936856113)
            ·
              refine ⟨723208584047295187452642085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964278112063060249936856113 723208584047295187452642085)
              ·
                refine ⟨135601609508867847647370391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723208584047295187452642085 135601609508867847647370391)
                ·
                  refine ⟨203402414263301771471055587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135601609508867847647370391 203402414263301771471055587)
                  ·
                    refine ⟨305103621394952657206583381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203402414263301771471055587 305103621394952657206583381)
                    ·
                      refine ⟨3575433063222101451639649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 305103621394952657206583381 3575433063222101451639649)
                      ·
                        rfl

theorem cell23_6963131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_6963131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963131 prefixEnd_6963131 := by exact prefixLift 6963131
  have htrace : WordTrace (prefixWord ++ tailWord_6963131) baseStart_6963131 baseEnd_6963131 := by
    simpa [prefixWord, tailWord_6963131, baseEnd_6963131] using wordTrace_append hprefix tailTrace_6963131
  have hstable : (prefixWord ++ tailWord_6963131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963131).length < 2 ^ (prefixWord ++ tailWord_6963131).sum := by decide
  have hdescent : baseEnd_6963131 < baseStart_6963131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963148 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6963148 : Nat := 118140960795 + 6963148 * 2 ^ 59
def prefixEnd_6963148 : Nat := 4983230072969 + 3 ^ 40 * 6963148 * 2
def baseEnd_6963148 : Nat := 3575441792393227885127071

theorem tailTrace_6963148 : CollatzResearch.WordTrace tailWord_6963148 prefixEnd_6963148 3575441792393227885127071 := by
  unfold tailWord_6963148
  simp only [CollatzResearch.WordTrace]
  refine ⟨126983435888855740922793049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169311247851807654563724065 126983435888855740922793049)
  ·
    refine ⟨95237576916641805692094787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126983435888855740922793049 95237576916641805692094787)
    ·
      refine ⟨142856365374962708538142181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95237576916641805692094787 142856365374962708538142181)
      ·
        refine ⟨26785568507805507850901659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142856365374962708538142181 26785568507805507850901659)
        ·
          refine ⟨40178352761708261776352489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26785568507805507850901659 40178352761708261776352489)
          ·
            refine ⟨30133764571281196332264367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40178352761708261776352489 30133764571281196332264367)
            ·
              refine ⟨45200646856921794498396551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30133764571281196332264367 45200646856921794498396551)
              ·
                refine ⟨67800970285382691747594827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45200646856921794498396551 67800970285382691747594827)
                ·
                  refine ⟨101701455428074037621392241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67800970285382691747594827 101701455428074037621392241)
                  ·
                    refine ⟨76276091571055528216044181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101701455428074037621392241 76276091571055528216044181)
                    ·
                      refine ⟨3575441792393227885127071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76276091571055528216044181 3575441792393227885127071)
                      ·
                        rfl

theorem cell23_6963148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6963148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963148 prefixEnd_6963148 := by exact prefixLift 6963148
  have htrace : WordTrace (prefixWord ++ tailWord_6963148) baseStart_6963148 baseEnd_6963148 := by
    simpa [prefixWord, tailWord_6963148, baseEnd_6963148] using wordTrace_append hprefix tailTrace_6963148
  have hstable : (prefixWord ++ tailWord_6963148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963148).length < 2 ^ (prefixWord ++ tailWord_6963148).sum := by decide
  have hdescent : baseEnd_6963148 < baseStart_6963148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963162 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_6963162 : Nat := 118140960795 + 6963162 * 2 ^ 59
def prefixEnd_6963162 : Nat := 4983230072969 + 3 ^ 40 * 6963162 * 2
def baseEnd_6963162 : Nat := 397272109013598981150223

theorem tailTrace_6963162 : CollatzResearch.WordTrace tailWord_6963162 prefixEnd_6963162 397272109013598981150223 := by
  unfold tailWord_6963162
  simp only [CollatzResearch.WordTrace]
  refine ⟨63491845599915190559148935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169311588266440508157730493 63491845599915190559148935)
  ·
    refine ⟨95237768399872785838723403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63491845599915190559148935 95237768399872785838723403)
    ·
      refine ⟨142856652599809178758085105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95237768399872785838723403 142856652599809178758085105)
      ·
        refine ⟨107142489449856884068563829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142856652599809178758085105 107142489449856884068563829)
        ·
          refine ⟨10044608385924082881427859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107142489449856884068563829 10044608385924082881427859)
          ·
            refine ⟨15066912578886124322141789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10044608385924082881427859 15066912578886124322141789)
            ·
              refine ⟨5650092217082296620803171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15066912578886124322141789 5650092217082296620803171)
              ·
                refine ⟨8475138325623444931204757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650092217082296620803171 8475138325623444931204757)
                ·
                  refine ⟨397272109013598981150223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8475138325623444931204757 397272109013598981150223)
                  ·
                    rfl

theorem cell23_6963162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_6963162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963162 prefixEnd_6963162 := by exact prefixLift 6963162
  have htrace : WordTrace (prefixWord ++ tailWord_6963162) baseStart_6963162 baseEnd_6963162 := by
    simpa [prefixWord, tailWord_6963162, baseEnd_6963162] using wordTrace_append hprefix tailTrace_6963162
  have hstable : (prefixWord ++ tailWord_6963162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963162).length < 2 ^ (prefixWord ++ tailWord_6963162).sum := by decide
  have hdescent : baseEnd_6963162 < baseStart_6963162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963182 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_6963182 : Nat := 118140960795 + 6963182 * 2 ^ 59
def prefixEnd_6963182 : Nat := 4983230072969 + 3 ^ 40 * 6963182 * 2
def baseEnd_6963182 : Nat := 3575459250735480752101915

theorem tailTrace_6963182 : CollatzResearch.WordTrace tailWord_6963182 prefixEnd_6963182 3575459250735480752101915 := by
  unfold tailWord_6963182
  simp only [CollatzResearch.WordTrace]
  refine ⟨31746013982448538206540475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169312074573058870434882533 31746013982448538206540475)
  ·
    refine ⟨47619020973672807309810713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31746013982448538206540475 47619020973672807309810713)
    ·
      refine ⟨35714265730254605482358035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47619020973672807309810713 35714265730254605482358035)
      ·
        refine ⟨53571398595381908223537053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35714265730254605482358035 53571398595381908223537053)
        ·
          refine ⟨20089274473268215583826395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53571398595381908223537053 20089274473268215583826395)
          ·
            refine ⟨30133911709902323375739593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20089274473268215583826395 30133911709902323375739593)
            ·
              refine ⟨22600433782426742531804695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30133911709902323375739593 22600433782426742531804695)
              ·
                refine ⟨33900650673640113797707043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22600433782426742531804695 33900650673640113797707043)
                ·
                  refine ⟨50850976010460170696560565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33900650673640113797707043 50850976010460170696560565)
                  ·
                    refine ⟨4767279000980641002802553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50850976010460170696560565 4767279000980641002802553)
                    ·
                      refine ⟨3575459250735480752101915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767279000980641002802553 3575459250735480752101915)
                      ·
                        rfl

theorem cell23_6963182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_6963182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963182 prefixEnd_6963182 := by exact prefixLift 6963182
  have htrace : WordTrace (prefixWord ++ tailWord_6963182) baseStart_6963182 baseEnd_6963182 := by
    simpa [prefixWord, tailWord_6963182, baseEnd_6963182] using wordTrace_append hprefix tailTrace_6963182
  have hstable : (prefixWord ++ tailWord_6963182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963182).length < 2 ^ (prefixWord ++ tailWord_6963182).sum := by decide
  have hdescent : baseEnd_6963182 < baseStart_6963182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963195 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 4]
def baseStart_6963195 : Nat := 118140960795 + 6963195 * 2 ^ 59
def prefixEnd_6963195 : Nat := 4983230072969 + 3 ^ 40 * 6963195 * 2
def baseEnd_6963195 : Nat := 3575465925983989201239355

theorem tailTrace_6963195 : CollatzResearch.WordTrace tailWord_6963195 prefixEnd_6963195 3575465925983989201239355 := by
  unfold tailWord_6963195
  simp only [CollatzResearch.WordTrace]
  refine ⟨253968586008541208872547039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169312390672360805915031359 253968586008541208872547039)
  ·
    refine ⟨380952879012811813308820559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253968586008541208872547039 380952879012811813308820559)
    ·
      refine ⟨571429318519217719963230839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380952879012811813308820559 571429318519217719963230839)
      ·
        refine ⟨857143977778826579944846259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571429318519217719963230839 857143977778826579944846259)
        ·
          refine ⟨1285715966668239869917269389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857143977778826579944846259 1285715966668239869917269389)
          ·
            refine ⟨482143487500589951218976021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1285715966668239869917269389 482143487500589951218976021)
            ·
              refine ⟨22600475976590153963389501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 482143487500589951218976021 22600475976590153963389501)
              ·
                refine ⟨8475178491221307736271063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22600475976590153963389501 8475178491221307736271063)
                ·
                  refine ⟨12712767736831961604406595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475178491221307736271063 12712767736831961604406595)
                  ·
                    refine ⟨19069151605247942406609893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12712767736831961604406595 19069151605247942406609893)
                    ·
                      refine ⟨3575465925983989201239355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19069151605247942406609893 3575465925983989201239355)
                      ·
                        rfl

theorem cell23_6963195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 4].length) (baseStart_6963195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963195 prefixEnd_6963195 := by exact prefixLift 6963195
  have htrace : WordTrace (prefixWord ++ tailWord_6963195) baseStart_6963195 baseEnd_6963195 := by
    simpa [prefixWord, tailWord_6963195, baseEnd_6963195] using wordTrace_append hprefix tailTrace_6963195
  have hstable : (prefixWord ++ tailWord_6963195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963195).length < 2 ^ (prefixWord ++ tailWord_6963195).sum := by decide
  have hdescent : baseEnd_6963195 < baseStart_6963195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963205 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_6963205 : Nat := 118140960795 + 6963205 * 2 ^ 59
def prefixEnd_6963205 : Nat := 4983230072969 + 3 ^ 40 * 6963205 * 2
def baseEnd_6963205 : Nat := 1191823686930178054038103

theorem tailTrace_6963205 : CollatzResearch.WordTrace tailWord_6963205 prefixEnd_6963205 1191823686930178054038103 := by
  unfold tailWord_6963205
  simp only [CollatzResearch.WordTrace]
  refine ⟨253968950738504980580411069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169312633825669987053607379 253968950738504980580411069)
  ·
    refine ⟨95238356526939367717654151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253968950738504980580411069 95238356526939367717654151)
    ·
      refine ⟨142857534790409051576481227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95238356526939367717654151 142857534790409051576481227)
      ·
        refine ⟨214286302185613577364721841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142857534790409051576481227 214286302185613577364721841)
        ·
          refine ⟨160714726639210183023541381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214286302185613577364721841 160714726639210183023541381)
          ·
            refine ⟨30134011244851909316914009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160714726639210183023541381 30134011244851909316914009)
            ·
              refine ⟨22600508433638931987685507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30134011244851909316914009 22600508433638931987685507)
              ·
                refine ⟨33900762650458397981528261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22600508433638931987685507 33900762650458397981528261)
                ·
                  refine ⟨6356392996960949621536549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33900762650458397981528261 6356392996960949621536549)
                  ·
                    refine ⟨1191823686930178054038103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356392996960949621536549 1191823686930178054038103)
                    ·
                      rfl

theorem cell23_6963205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_6963205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963205 prefixEnd_6963205 := by exact prefixLift 6963205
  have htrace : WordTrace (prefixWord ++ tailWord_6963205) baseStart_6963205 baseEnd_6963205 := by
    simpa [prefixWord, tailWord_6963205, baseEnd_6963205] using wordTrace_append hprefix tailTrace_6963205
  have hstable : (prefixWord ++ tailWord_6963205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963205).length < 2 ^ (prefixWord ++ tailWord_6963205).sum := by decide
  have hdescent : baseEnd_6963205 < baseStart_6963205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963208 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6963208 : Nat := 118140960795 + 6963208 * 2 ^ 59
def prefixEnd_6963208 : Nat := 4983230072969 + 3 ^ 40 * 6963208 * 2
def baseEnd_6963208 : Nat := 3575472601232497650376795

theorem tailTrace_6963208 : CollatzResearch.WordTrace tailWord_6963208 prefixEnd_6963208 3575472601232497650376795 := by
  unfold tailWord_6963208
  simp only [CollatzResearch.WordTrace]
  refine ⟨126984530078747056046385139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169312706771662741395180185 126984530078747056046385139)
  ·
    refine ⟨190476795118120584069577709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126984530078747056046385139 190476795118120584069577709)
    ·
      refine ⟨71428798169295219026091641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190476795118120584069577709 71428798169295219026091641)
      ·
        refine ⟨53571598626971414269568731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71428798169295219026091641 53571598626971414269568731)
        ·
          refine ⟨80357397940457121404353097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53571598626971414269568731 80357397940457121404353097)
          ·
            refine ⟨60268048455342841053264823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80357397940457121404353097 60268048455342841053264823)
            ·
              refine ⟨90402072683014261579897235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60268048455342841053264823 90402072683014261579897235)
              ·
                refine ⟨135603109024521392369845853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90402072683014261579897235 135603109024521392369845853)
                ·
                  refine ⟨50851165884195522138692195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135603109024521392369845853 50851165884195522138692195)
                  ·
                    refine ⟨76276748826293283208038293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50851165884195522138692195 76276748826293283208038293)
                    ·
                      refine ⟨3575472601232497650376795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76276748826293283208038293 3575472601232497650376795)
                      ·
                        rfl

theorem cell23_6963208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6963208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963208 prefixEnd_6963208 := by exact prefixLift 6963208
  have htrace : WordTrace (prefixWord ++ tailWord_6963208) baseStart_6963208 baseEnd_6963208 := by
    simpa [prefixWord, tailWord_6963208, baseEnd_6963208] using wordTrace_append hprefix tailTrace_6963208
  have hstable : (prefixWord ++ tailWord_6963208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963208).length < 2 ^ (prefixWord ++ tailWord_6963208).sum := by decide
  have hdescent : baseEnd_6963208 < baseStart_6963208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963213 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6963213 : Nat := 118140960795 + 6963213 * 2 ^ 59
def prefixEnd_6963213 : Nat := 4983230072969 + 3 ^ 40 * 6963213 * 2
def baseEnd_6963213 : Nat := 397275018737307792312697

theorem tailTrace_6963213 : CollatzResearch.WordTrace tailWord_6963213 prefixEnd_6963213 397275018737307792312697 := by
  unfold tailWord_6963213
  simp only [CollatzResearch.WordTrace]
  refine ⟨253969242522475997946702293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169312828348317331964468195 253969242522475997946702293)
  ·
    refine ⟨5952404121620531201875835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 253969242522475997946702293 5952404121620531201875835)
    ·
      refine ⟨8928606182430796802813753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952404121620531201875835 8928606182430796802813753)
      ·
        refine ⟨6696454636823097602110315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8928606182430796802813753 6696454636823097602110315)
        ·
          refine ⟨10044681955234646403165473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6696454636823097602110315 10044681955234646403165473)
          ·
            refine ⟨7533511466425984802374105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10044681955234646403165473 7533511466425984802374105)
            ·
              refine ⟨5650133599819488601780579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7533511466425984802374105 5650133599819488601780579)
              ·
                refine ⟨8475200399729232902670869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650133599819488601780579 8475200399729232902670869)
                ·
                  refine ⟨397275018737307792312697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8475200399729232902670869 397275018737307792312697)
                  ·
                    rfl

theorem cell23_6963213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6963213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963213 prefixEnd_6963213 := by exact prefixLift 6963213
  have htrace : WordTrace (prefixWord ++ tailWord_6963213) baseStart_6963213 baseEnd_6963213 := by
    simpa [prefixWord, tailWord_6963213, baseEnd_6963213] using wordTrace_append hprefix tailTrace_6963213
  have hstable : (prefixWord ++ tailWord_6963213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963213).length < 2 ^ (prefixWord ++ tailWord_6963213).sum := by decide
  have hdescent : baseEnd_6963213 < baseStart_6963213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963229 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_6963229 : Nat := 118140960795 + 6963229 * 2 ^ 59
def prefixEnd_6963229 : Nat := 4983230072969 + 3 ^ 40 * 6963229 * 2
def baseEnd_6963229 : Nat := 3575483384326242068214199

theorem tailTrace_6963229 : CollatzResearch.WordTrace tailWord_6963229 prefixEnd_6963229 3575483384326242068214199 := by
  unfold tailWord_6963229
  simp only [CollatzResearch.WordTrace]
  refine ⟨253969826090418032679284741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169313217393612021786189827 253969826090418032679284741)
  ·
    refine ⟨47619342391953381127365889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253969826090418032679284741 47619342391953381127365889)
    ·
      refine ⟨35714506793965035845524417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47619342391953381127365889 35714506793965035845524417)
      ·
        refine ⟨26785880095473776884143313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35714506793965035845524417 26785880095473776884143313)
        ·
          refine ⟨20089410071605332663107485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26785880095473776884143313 20089410071605332663107485)
          ·
            refine ⟨7533528776851999748665307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20089410071605332663107485 7533528776851999748665307)
            ·
              refine ⟨11300293165277999622997961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533528776851999748665307 11300293165277999622997961)
              ·
                refine ⟨8475219873958499717248471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11300293165277999622997961 8475219873958499717248471)
                ·
                  refine ⟨12712829810937749575872707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475219873958499717248471 12712829810937749575872707)
                  ·
                    refine ⟨19069244716406624363809061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12712829810937749575872707 19069244716406624363809061)
                    ·
                      refine ⟨3575483384326242068214199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19069244716406624363809061 3575483384326242068214199)
                      ·
                        rfl

theorem cell23_6963229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_6963229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963229 prefixEnd_6963229 := by exact prefixLift 6963229
  have htrace : WordTrace (prefixWord ++ tailWord_6963229) baseStart_6963229 baseEnd_6963229 := by
    simpa [prefixWord, tailWord_6963229, baseEnd_6963229] using wordTrace_append hprefix tailTrace_6963229
  have hstable : (prefixWord ++ tailWord_6963229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963229).length < 2 ^ (prefixWord ++ tailWord_6963229).sum := by decide
  have hdescent : baseEnd_6963229 < baseStart_6963229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963242 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6963242 : Nat := 118140960795 + 6963242 * 2 ^ 59
def prefixEnd_6963242 : Nat := 4983230072969 + 3 ^ 40 * 6963242 * 2
def baseEnd_6963242 : Nat := 3575490059574750517351639

theorem tailTrace_6963242 : CollatzResearch.WordTrace tailWord_6963242 prefixEnd_6963242 3575490059574750517351639 := by
  unfold tailWord_6963242
  simp only [CollatzResearch.WordTrace]
  refine ⟨63492575059842733974876995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169313533492913957266338653 63492575059842733974876995)
  ·
    refine ⟨95238862589764100962315493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63492575059842733974876995 95238862589764100962315493)
    ·
      refine ⟨17857286735580768930434155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95238862589764100962315493 17857286735580768930434155)
      ·
        refine ⟨26785930103371153395651233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17857286735580768930434155 26785930103371153395651233)
        ·
          refine ⟨20089447577528365046738425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26785930103371153395651233 20089447577528365046738425)
          ·
            refine ⟨15067085683146273785053819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20089447577528365046738425 15067085683146273785053819)
            ·
              refine ⟨22600628524719410677580729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067085683146273785053819 22600628524719410677580729)
              ·
                refine ⟨16950471393539558008185547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22600628524719410677580729 16950471393539558008185547)
                ·
                  refine ⟨25425707090309337012278321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16950471393539558008185547 25425707090309337012278321)
                  ·
                    refine ⟨19069280317732002759208741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25425707090309337012278321 19069280317732002759208741)
                    ·
                      refine ⟨3575490059574750517351639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19069280317732002759208741 3575490059574750517351639)
                      ·
                        rfl

theorem cell23_6963242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6963242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963242 prefixEnd_6963242 := by exact prefixLift 6963242
  have htrace : WordTrace (prefixWord ++ tailWord_6963242) baseStart_6963242 baseEnd_6963242 := by
    simpa [prefixWord, tailWord_6963242, baseEnd_6963242] using wordTrace_append hprefix tailTrace_6963242
  have hstable : (prefixWord ++ tailWord_6963242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963242).length < 2 ^ (prefixWord ++ tailWord_6963242).sum := by decide
  have hdescent : baseEnd_6963242 < baseStart_6963242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963249 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 1, 2, 3]
def baseStart_6963249 : Nat := 118140960795 + 6963249 * 2 ^ 59
def prefixEnd_6963249 : Nat := 4983230072969 + 3 ^ 40 * 6963249 * 2
def baseEnd_6963249 : Nat := 3575493653939331989964107

theorem tailTrace_6963249 : CollatzResearch.WordTrace tailWord_6963249 prefixEnd_6963249 3575493653939331989964107 := by
  unfold tailWord_6963249
  simp only [CollatzResearch.WordTrace]
  refine ⟨253970555550345576095012801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169313703700230384063341867 253970555550345576095012801)
  ·
    refine ⟨190477916662759182071259601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253970555550345576095012801 190477916662759182071259601)
    ·
      refine ⟨142858437497069386553444701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190477916662759182071259601 142858437497069386553444701)
      ·
        refine ⟨53571914061401019957541763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142858437497069386553444701 53571914061401019957541763)
        ·
          refine ⟨80357871092101529936312645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53571914061401019957541763 80357871092101529936312645)
          ·
            refine ⟨15067100829769036863058621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80357871092101529936312645 15067100829769036863058621)
            ·
              refine ⟨5650162811163388823646983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15067100829769036863058621 5650162811163388823646983)
              ·
                refine ⟨8475244216745083235470475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650162811163388823646983 8475244216745083235470475)
                ·
                  refine ⟨12712866325117624853205713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475244216745083235470475 12712866325117624853205713)
                  ·
                    refine ⟨9534649743838218639904285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12712866325117624853205713 9534649743838218639904285)
                    ·
                      refine ⟨3575493653939331989964107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534649743838218639904285 3575493653939331989964107)
                      ·
                        rfl

theorem cell23_6963249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_6963249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963249 prefixEnd_6963249 := by exact prefixLift 6963249
  have htrace : WordTrace (prefixWord ++ tailWord_6963249) baseStart_6963249 baseEnd_6963249 := by
    simpa [prefixWord, tailWord_6963249, baseEnd_6963249] using wordTrace_append hprefix tailTrace_6963249
  have hstable : (prefixWord ++ tailWord_6963249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963249).length < 2 ^ (prefixWord ++ tailWord_6963249).sum := by decide
  have hdescent : baseEnd_6963249 < baseStart_6963249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963252 : List Nat := [2, 5, 1, 2, 3, 10]
def baseStart_6963252 : Nat := 118140960795 + 6963252 * 2 ^ 59
def prefixEnd_6963252 : Nat := 4983230072969 + 3 ^ 40 * 6963252 * 2
def baseEnd_6963252 : Nat := 14713971993338664519451

theorem tailTrace_6963252 : CollatzResearch.WordTrace tailWord_6963252 prefixEnd_6963252 14713971993338664519451 := by
  unfold tailWord_6963252
  simp only [CollatzResearch.WordTrace]
  refine ⟨126985332484667353803686005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169313776646223138404914673 126985332484667353803686005)
  ·
    refine ⟨11904874920437564419095563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126985332484667353803686005 11904874920437564419095563)
    ·
      refine ⟨17857312380656346628643345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11904874920437564419095563 17857312380656346628643345)
      ·
        refine ⟨13392984285492259971482509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17857312380656346628643345 13392984285492259971482509)
        ·
          refine ⟨5022369107059597489305941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13392984285492259971482509 5022369107059597489305941)
          ·
            refine ⟨14713971993338664519451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5022369107059597489305941 14713971993338664519451)
            ·
              rfl

theorem cell23_6963252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 10].length) (baseStart_6963252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963252 prefixEnd_6963252 := by exact prefixLift 6963252
  have htrace : WordTrace (prefixWord ++ tailWord_6963252) baseStart_6963252 baseEnd_6963252 := by
    simpa [prefixWord, tailWord_6963252, baseEnd_6963252] using wordTrace_append hprefix tailTrace_6963252
  have hstable : (prefixWord ++ tailWord_6963252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963252).length < 2 ^ (prefixWord ++ tailWord_6963252).sum := by decide
  have hdescent : baseEnd_6963252 < baseStart_6963252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963265 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6963265 : Nat := 118140960795 + 6963265 * 2 ^ 59
def prefixEnd_6963265 : Nat := 4983230072969 + 3 ^ 40 * 6963265 * 2
def baseEnd_6963265 : Nat := 1191833956543267975788011

theorem tailTrace_6963265 : CollatzResearch.WordTrace tailWord_6963265 prefixEnd_6963265 1191833956543267975788011 := by
  unfold tailWord_6963265
  simp only [CollatzResearch.WordTrace]
  refine ⟨253971139118287610827595249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169314092745525073885063499 253971139118287610827595249)
  ·
    refine ⟨190478354338715708120696437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253971139118287610827595249 190478354338715708120696437)
    ·
      refine ⟨17857345719254597636315291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190478354338715708120696437 17857345719254597636315291)
      ·
        refine ⟨26786018578881896454472937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17857345719254597636315291 26786018578881896454472937)
        ·
          refine ⟨20089513934161422340854703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26786018578881896454472937 20089513934161422340854703)
          ·
            refine ⟨30134270901242133511282055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20089513934161422340854703 30134270901242133511282055)
            ·
              refine ⟨45201406351863200266923083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30134270901242133511282055 45201406351863200266923083)
              ·
                refine ⟨67802109527794800400384625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45201406351863200266923083 67802109527794800400384625)
                ·
                  refine ⟨50851582145846100300288469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67802109527794800400384625 50851582145846100300288469)
                  ·
                    refine ⟨1191833956543267975788011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50851582145846100300288469 1191833956543267975788011)
                    ·
                      rfl

theorem cell23_6963265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6963265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963265 prefixEnd_6963265 := by exact prefixLift 6963265
  have htrace : WordTrace (prefixWord ++ tailWord_6963265) baseStart_6963265 baseEnd_6963265 := by
    simpa [prefixWord, tailWord_6963265, baseEnd_6963265] using wordTrace_append hprefix tailTrace_6963265
  have hstable : (prefixWord ++ tailWord_6963265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963265).length < 2 ^ (prefixWord ++ tailWord_6963265).sum := by decide
  have hdescent : baseEnd_6963265 < baseStart_6963265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963306 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_6963306 : Nat := 118140960795 + 6963306 * 2 ^ 59
def prefixEnd_6963306 : Nat := 4983230072969 + 3 ^ 40 * 6963306 * 2
def baseEnd_6963306 : Nat := 3575522922336638266951345

theorem tailTrace_6963306 : CollatzResearch.WordTrace tailWord_6963306 prefixEnd_6963306 3575522922336638266951345 := by
  unfold tailWord_6963306
  simp only [CollatzResearch.WordTrace]
  refine ⟨63493158627784768707459443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169315089674092716553225181 63493158627784768707459443)
  ·
    refine ⟨95239737941677153061189165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63493158627784768707459443 95239737941677153061189165)
    ·
      refine ⟨35714901728128932397945937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95239737941677153061189165 35714901728128932397945937)
      ·
        refine ⟨26786176296096699298459453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35714901728128932397945937 26786176296096699298459453)
        ·
          refine ⟨10044816111036262236922295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26786176296096699298459453 10044816111036262236922295)
          ·
            refine ⟨15067224166554393355383443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10044816111036262236922295 15067224166554393355383443)
            ·
              refine ⟨22600836249831590033075165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067224166554393355383443 22600836249831590033075165)
              ·
                refine ⟨8475313593686846262403187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22600836249831590033075165 8475313593686846262403187)
                ·
                  refine ⟨12712970390530269393604781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475313593686846262403187 12712970390530269393604781)
                  ·
                    refine ⟨4767363896448851022601793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12712970390530269393604781 4767363896448851022601793)
                    ·
                      refine ⟨3575522922336638266951345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767363896448851022601793 3575522922336638266951345)
                      ·
                        rfl

theorem cell23_6963306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_6963306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963306 prefixEnd_6963306 := by exact prefixLift 6963306
  have htrace : WordTrace (prefixWord ++ tailWord_6963306) baseStart_6963306 baseEnd_6963306 := by
    simpa [prefixWord, tailWord_6963306, baseEnd_6963306] using wordTrace_append hprefix tailTrace_6963306
  have hstable : (prefixWord ++ tailWord_6963306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963306).length < 2 ^ (prefixWord ++ tailWord_6963306).sum := by decide
  have hdescent : baseEnd_6963306 < baseStart_6963306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963319 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 4, 2, 2]
def baseStart_6963319 : Nat := 118140960795 + 6963319 * 2 ^ 59
def prefixEnd_6963319 : Nat := 4983230072969 + 3 ^ 40 * 6963319 * 2
def baseEnd_6963319 : Nat := 3575529597585146716088785

theorem tailTrace_6963319 : CollatzResearch.WordTrace tailWord_6963319 prefixEnd_6963319 3575529597585146716088785 := by
  unfold tailWord_6963319
  simp only [CollatzResearch.WordTrace]
  refine ⟨253973108660091978050061011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169315405773394652033374007 253973108660091978050061011)
  ·
    refine ⟨380959662990137967075091517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253973108660091978050061011 380959662990137967075091517)
    ·
      refine ⟨142859873621301737653159319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380959662990137967075091517 142859873621301737653159319)
      ·
        refine ⟨214289810431952606479738979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142859873621301737653159319 214289810431952606479738979)
        ·
          refine ⟨321434715647928909719608469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214289810431952606479738979 321434715647928909719608469)
          ·
            refine ⟨15067252295996667643106647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 321434715647928909719608469 15067252295996667643106647)
            ·
              refine ⟨22600878443995001464659971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067252295996667643106647 22600878443995001464659971)
              ·
                refine ⟨33901317665992502196989957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22600878443995001464659971 33901317665992502196989957)
                ·
                  refine ⟨6356497062373594161935617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33901317665992502196989957 6356497062373594161935617)
                  ·
                    refine ⟨4767372796780195621451713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6356497062373594161935617 4767372796780195621451713)
                    ·
                      refine ⟨3575529597585146716088785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767372796780195621451713 3575529597585146716088785)
                      ·
                        rfl

theorem cell23_6963319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_6963319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963319 prefixEnd_6963319 := by exact prefixLift 6963319
  have htrace : WordTrace (prefixWord ++ tailWord_6963319) baseStart_6963319 baseEnd_6963319 := by
    simpa [prefixWord, tailWord_6963319, baseEnd_6963319] using wordTrace_append hprefix tailTrace_6963319
  have hstable : (prefixWord ++ tailWord_6963319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963319).length < 2 ^ (prefixWord ++ tailWord_6963319).sum := by decide
  have hdescent : baseEnd_6963319 < baseStart_6963319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963325 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 7]
def baseStart_6963325 : Nat := 118140960795 + 6963325 * 2 ^ 59
def prefixEnd_6963325 : Nat := 4983230072969 + 3 ^ 40 * 6963325 * 2
def baseEnd_6963325 : Nat := 397281408718785965845973

theorem tailTrace_6963325 : CollatzResearch.WordTrace tailWord_6963325 prefixEnd_6963325 397281408718785965845973 := by
  unfold tailWord_6963325
  simp only [CollatzResearch.WordTrace]
  refine ⟨253973327498070241074779429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169315551665380160716519619 253973327498070241074779429)
  ·
    refine ⟨47619998905888170201521143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253973327498070241074779429 47619998905888170201521143)
    ·
      refine ⟨71429998358832255302281715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47619998905888170201521143 71429998358832255302281715)
      ·
        refine ⟨107144997538248382953422573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71429998358832255302281715 107144997538248382953422573)
        ·
          refine ⟨40179374076843143607533465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107144997538248382953422573 40179374076843143607533465)
          ·
            refine ⟨30134530557632357705650099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40179374076843143607533465 30134530557632357705650099)
            ·
              refine ⟨45201795836448536558475149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30134530557632357705650099 45201795836448536558475149)
              ·
                refine ⟨16950673438668201209428181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45201795836448536558475149 16950673438668201209428181)
                ·
                  refine ⟨397281408718785965845973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16950673438668201209428181 397281408718785965845973)
                  ·
                    rfl

theorem cell23_6963325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_6963325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963325 prefixEnd_6963325 := by exact prefixLift 6963325
  have htrace : WordTrace (prefixWord ++ tailWord_6963325) baseStart_6963325 baseEnd_6963325 := by
    simpa [prefixWord, tailWord_6963325, baseEnd_6963325] using wordTrace_append hprefix tailTrace_6963325
  have hstable : (prefixWord ++ tailWord_6963325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963325).length < 2 ^ (prefixWord ++ tailWord_6963325).sum := by decide
  have hdescent : baseEnd_6963325 < baseStart_6963325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963336 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6963336 : Nat := 118140960795 + 6963336 * 2 ^ 59
def prefixEnd_6963336 : Nat := 4983230072969 + 3 ^ 40 * 6963336 * 2
def baseEnd_6963336 : Nat := 3575538326756273149576207

theorem tailTrace_6963336 : CollatzResearch.WordTrace tailWord_6963336 prefixEnd_6963336 3575538326756273149576207 := by
  unfold tailWord_6963336
  simp only [CollatzResearch.WordTrace]
  refine ⟨126986864350515194976714931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169315819134020259968953241 126986864350515194976714931)
  ·
    refine ⟨190480296525772792465072397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126986864350515194976714931 190480296525772792465072397)
    ·
      refine ⟨71430111197164797174402149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190480296525772792465072397 71430111197164797174402149)
      ·
        refine ⟨13393145849468399470200403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71430111197164797174402149 13393145849468399470200403)
        ·
          refine ⟨20089718774202599205300605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13393145849468399470200403 20089718774202599205300605)
          ·
            refine ⟨7533644540325974701987727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20089718774202599205300605 7533644540325974701987727)
            ·
              refine ⟨11300466810488962052981591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533644540325974701987727 11300466810488962052981591)
              ·
                refine ⟨16950700215733443079472387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11300466810488962052981591 16950700215733443079472387)
                ·
                  refine ⟨25426050323600164619208581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16950700215733443079472387 25426050323600164619208581)
                  ·
                    refine ⟨4767384435675030866101609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25426050323600164619208581 4767384435675030866101609)
                    ·
                      refine ⟨3575538326756273149576207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767384435675030866101609 3575538326756273149576207)
                      ·
                        rfl

theorem cell23_6963336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6963336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963336 prefixEnd_6963336 := by exact prefixLift 6963336
  have htrace : WordTrace (prefixWord ++ tailWord_6963336) baseStart_6963336 baseEnd_6963336 := by
    simpa [prefixWord, tailWord_6963336, baseEnd_6963336] using wordTrace_append hprefix tailTrace_6963336
  have hstable : (prefixWord ++ tailWord_6963336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963336).length < 2 ^ (prefixWord ++ tailWord_6963336).sum := by decide
  have hdescent : baseEnd_6963336 < baseStart_6963336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963359 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 5]
def baseStart_6963359 : Nat := 118140960795 + 6963359 * 2 ^ 59
def prefixEnd_6963359 : Nat := 4983230072969 + 3 ^ 40 * 6963359 * 2
def baseEnd_6963359 : Nat := 397283348534591839954289

theorem tailTrace_6963359 : CollatzResearch.WordTrace tailWord_6963359 prefixEnd_6963359 397283348534591839954289 := by
  unfold tailWord_6963359
  simp only [CollatzResearch.WordTrace]
  refine ⟨253974567579947064881517131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169316378386631376587678087 253974567579947064881517131)
  ·
    refine ⟨380961851369920597322275697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253974567579947064881517131 380961851369920597322275697)
    ·
      refine ⟨285721388527440447991706773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380961851369920597322275697 285721388527440447991706773)
      ·
        refine ⟨13393190087223770999611255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 285721388527440447991706773 13393190087223770999611255)
        ·
          refine ⟨20089785130835656499416883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13393190087223770999611255 20089785130835656499416883)
          ·
            refine ⟨30134677696253484749125325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20089785130835656499416883 30134677696253484749125325)
            ·
              refine ⟨11300504136095056780921997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30134677696253484749125325 11300504136095056780921997)
              ·
                refine ⟨4237689051035646292845749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11300504136095056780921997 4237689051035646292845749)
                ·
                  refine ⟨397283348534591839954289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4237689051035646292845749 397283348534591839954289)
                  ·
                    rfl

theorem cell23_6963359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 5].length) (baseStart_6963359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963359 prefixEnd_6963359 := by exact prefixLift 6963359
  have htrace : WordTrace (prefixWord ++ tailWord_6963359) baseStart_6963359 baseEnd_6963359 := by
    simpa [prefixWord, tailWord_6963359, baseEnd_6963359] using wordTrace_append hprefix tailTrace_6963359
  have hstable : (prefixWord ++ tailWord_6963359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963359).length < 2 ^ (prefixWord ++ tailWord_6963359).sum := by decide
  have hdescent : baseEnd_6963359 < baseStart_6963359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963365 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_6963365 : Nat := 118140960795 + 6963365 * 2 ^ 59
def prefixEnd_6963365 : Nat := 4983230072969 + 3 ^ 40 * 6963365 * 2
def baseEnd_6963365 : Nat := 3575553217695253536113573

theorem tailTrace_6963365 : CollatzResearch.WordTrace tailWord_6963365 prefixEnd_6963365 3575553217695253536113573 := by
  unfold tailWord_6963365
  simp only [CollatzResearch.WordTrace]
  refine ⟨253974786417925327906235549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169316524278616885270823699 253974786417925327906235549)
  ·
    refine ⟨95240544906721997964838331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253974786417925327906235549 95240544906721997964838331)
    ·
      refine ⟨142860817360082996947257497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95240544906721997964838331 142860817360082996947257497)
      ·
        refine ⟨107145613020062247710443123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142860817360082996947257497 107145613020062247710443123)
        ·
          refine ⟨160718419530093371565664685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107145613020062247710443123 160718419530093371565664685)
          ·
            refine ⟨60269407323785014337124257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160718419530093371565664685 60269407323785014337124257)
            ·
              refine ⟨45202055492838760752843193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60269407323785014337124257 45202055492838760752843193)
              ·
                refine ⟨33901541619629070564632395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45202055492838760752843193 33901541619629070564632395)
                ·
                  refine ⟨50852312429443605846948593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33901541619629070564632395 50852312429443605846948593)
                  ·
                    refine ⟨38139234322082704385211445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50852312429443605846948593 38139234322082704385211445)
                    ·
                      refine ⟨3575553217695253536113573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38139234322082704385211445 3575553217695253536113573)
                      ·
                        rfl

theorem cell23_6963365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_6963365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963365 prefixEnd_6963365 := by exact prefixLift 6963365
  have htrace : WordTrace (prefixWord ++ tailWord_6963365) baseStart_6963365 baseEnd_6963365 := by
    simpa [prefixWord, tailWord_6963365, baseEnd_6963365] using wordTrace_append hprefix tailTrace_6963365
  have hstable : (prefixWord ++ tailWord_6963365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963365).length < 2 ^ (prefixWord ++ tailWord_6963365).sum := by decide
  have hdescent : baseEnd_6963365 < baseStart_6963365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963402 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_6963402 : Nat := 118140960795 + 6963402 * 2 ^ 59
def prefixEnd_6963402 : Nat := 4983230072969 + 3 ^ 40 * 6963402 * 2
def baseEnd_6963402 : Nat := 1191857405493156630450301

theorem tailTrace_6963402 : CollatzResearch.WordTrace tailWord_6963402 prefixEnd_6963402 1191857405493156630450301 := by
  unfold tailWord_6963402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63494033979697820806333115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169317423945860855483554973 63494033979697820806333115)
  ·
    refine ⟨95241050969546731209499673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63494033979697820806333115 95241050969546731209499673)
    ·
      refine ⟨71430788227160048407124755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95241050969546731209499673 71430788227160048407124755)
      ·
        refine ⟨107146182340740072610687133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71430788227160048407124755 107146182340740072610687133)
        ·
          refine ⟨40179818377777527229007675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107146182340740072610687133 40179818377777527229007675)
          ·
            refine ⟨60269727566666290843511513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40179818377777527229007675 60269727566666290843511513)
            ·
              refine ⟨45202295674999718132633635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60269727566666290843511513 45202295674999718132633635)
              ·
                refine ⟨67803443512499577198950453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45202295674999718132633635 67803443512499577198950453)
                ·
                  refine ⟨6356572829296835362401605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67803443512499577198950453 6356572829296835362401605)
                  ·
                    refine ⟨1191857405493156630450301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356572829296835362401605 1191857405493156630450301)
                    ·
                      rfl

theorem cell23_6963402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_6963402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963402 prefixEnd_6963402 := by exact prefixLift 6963402
  have htrace : WordTrace (prefixWord ++ tailWord_6963402) baseStart_6963402 baseEnd_6963402 := by
    simpa [prefixWord, tailWord_6963402, baseEnd_6963402] using wordTrace_append hprefix tailTrace_6963402
  have hstable : (prefixWord ++ tailWord_6963402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963402).length < 2 ^ (prefixWord ++ tailWord_6963402).sum := by decide
  have hdescent : baseEnd_6963402 < baseStart_6963402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963429 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6963429 : Nat := 118140960795 + 6963429 * 2 ^ 59
def prefixEnd_6963429 : Nat := 4983230072969 + 3 ^ 40 * 6963429 * 2
def baseEnd_6963429 : Nat := 3575586080457141285713279

theorem tailTrace_6963429 : CollatzResearch.WordTrace tailWord_6963429 prefixEnd_6963429 3575586080457141285713279 := by
  unfold tailWord_6963429
  simp only [CollatzResearch.WordTrace]
  refine ⟨253977120689693466836565341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169318080459795644557710227 253977120689693466836565341)
  ·
    refine ⟨95241420258635050063712003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253977120689693466836565341 95241420258635050063712003)
    ·
      refine ⟨142862130387952575095568005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95241420258635050063712003 142862130387952575095568005)
      ·
        refine ⟨26786649447741107830419001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142862130387952575095568005 26786649447741107830419001)
        ·
          refine ⟨20089987085805830872814251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26786649447741107830419001 20089987085805830872814251)
          ·
            refine ⟨30134980628708746309221377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20089987085805830872814251 30134980628708746309221377)
            ·
              refine ⟨22601235471531559731916033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30134980628708746309221377 22601235471531559731916033)
              ·
                refine ⟨16950926603648669798937025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22601235471531559731916033 16950926603648669798937025)
                ·
                  refine ⟨12713194952736502349202769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16950926603648669798937025 12713194952736502349202769)
                  ·
                    refine ⟨9534896214552376761902077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12713194952736502349202769 9534896214552376761902077)
                    ·
                      refine ⟨3575586080457141285713279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534896214552376761902077 3575586080457141285713279)
                      ·
                        rfl

theorem cell23_6963429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6963429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963429 prefixEnd_6963429 := by exact prefixLift 6963429
  have htrace : WordTrace (prefixWord ++ tailWord_6963429) baseStart_6963429 baseEnd_6963429 := by
    simpa [prefixWord, tailWord_6963429, baseEnd_6963429] using wordTrace_append hprefix tailTrace_6963429
  have hstable : (prefixWord ++ tailWord_6963429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963429).length < 2 ^ (prefixWord ++ tailWord_6963429).sum := by decide
  have hdescent : baseEnd_6963429 < baseStart_6963429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963432 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 6]
def baseStart_6963432 : Nat := 118140960795 + 6963432 * 2 ^ 59
def prefixEnd_6963432 : Nat := 4983230072969 + 3 ^ 40 * 6963432 * 2
def baseEnd_6963432 : Nat := 397287513433233863775085

theorem tailTrace_6963432 : CollatzResearch.WordTrace tailWord_6963432 prefixEnd_6963432 397287513433233863775085 := by
  unfold tailWord_6963432
  simp only [CollatzResearch.WordTrace]
  refine ⟨126988615054341299174462275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169318153405788398899283033 126988615054341299174462275)
  ·
    refine ⟨190482922581511948761693413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126988615054341299174462275 190482922581511948761693413)
    ·
      refine ⟨35715547984033490392817515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190482922581511948761693413 35715547984033490392817515)
      ·
        refine ⟨53573321976050235589226273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35715547984033490392817515 53573321976050235589226273)
        ·
          refine ⟨40179991482037676691919705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53573321976050235589226273 40179991482037676691919705)
          ·
            refine ⟨30134993611528257518939779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40179991482037676691919705 30134993611528257518939779)
            ·
              refine ⟨45202490417292386278409669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30134993611528257518939779 45202490417292386278409669)
              ·
                refine ⟨8475466953242322427201813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45202490417292386278409669 8475466953242322427201813)
                ·
                  refine ⟨397287513433233863775085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8475466953242322427201813 397287513433233863775085)
                  ·
                    rfl

theorem cell23_6963432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 6].length) (baseStart_6963432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963432 prefixEnd_6963432 := by exact prefixLift 6963432
  have htrace : WordTrace (prefixWord ++ tailWord_6963432) baseStart_6963432 baseEnd_6963432 := by
    simpa [prefixWord, tailWord_6963432, baseEnd_6963432] using wordTrace_append hprefix tailTrace_6963432
  have hstable : (prefixWord ++ tailWord_6963432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963432).length < 2 ^ (prefixWord ++ tailWord_6963432).sum := by decide
  have hdescent : baseEnd_6963432 < baseStart_6963432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963435 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_6963435 : Nat := 118140960795 + 6963435 * 2 ^ 59
def prefixEnd_6963435 : Nat := 4983230072969 + 3 ^ 40 * 6963435 * 2
def baseEnd_6963435 : Nat := 3575589161341068262238251

theorem tailTrace_6963435 : CollatzResearch.WordTrace tailWord_6963435 prefixEnd_6963435 3575589161341068262238251 := by
  unfold tailWord_6963435
  simp only [CollatzResearch.WordTrace]
  refine ⟨253977339527671729861283759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169318226351781153240855839 253977339527671729861283759)
  ·
    refine ⟨380966009291507594791925639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253977339527671729861283759 380966009291507594791925639)
    ·
      refine ⟨571449013937261392187888459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380966009291507594791925639 571449013937261392187888459)
      ·
        refine ⟨857173520905892088281832689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571449013937261392187888459 857173520905892088281832689)
        ·
          refine ⟨642880140679419066211374517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857173520905892088281832689 642880140679419066211374517)
          ·
            refine ⟨60270013188695537457316361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 642880140679419066211374517 60270013188695537457316361)
            ·
              refine ⟨45202509891521653092987271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60270013188695537457316361 45202509891521653092987271)
              ·
                refine ⟨67803764837282479639480907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45202509891521653092987271 67803764837282479639480907)
                ·
                  refine ⟨101705647255923719459221361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67803764837282479639480907 101705647255923719459221361)
                  ·
                    refine ⟨76279235441942789594416021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101705647255923719459221361 76279235441942789594416021)
                    ·
                      refine ⟨3575589161341068262238251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76279235441942789594416021 3575589161341068262238251)
                      ·
                        rfl

theorem cell23_6963435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_6963435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963435 prefixEnd_6963435 := by exact prefixLift 6963435
  have htrace : WordTrace (prefixWord ++ tailWord_6963435) baseStart_6963435 baseEnd_6963435 := by
    simpa [prefixWord, tailWord_6963435, baseEnd_6963435] using wordTrace_append hprefix tailTrace_6963435
  have hstable : (prefixWord ++ tailWord_6963435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963435).length < 2 ^ (prefixWord ++ tailWord_6963435).sum := by decide
  have hdescent : baseEnd_6963435 < baseStart_6963435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963455 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_6963455 : Nat := 118140960795 + 6963455 * 2 ^ 59
def prefixEnd_6963455 : Nat := 4983230072969 + 3 ^ 40 * 6963455 * 2
def baseEnd_6963455 : Nat := 3575599430954158183988159

theorem tailTrace_6963455 : CollatzResearch.WordTrace tailWord_6963455 prefixEnd_6963455 3575599430954158183988159 := by
  unfold tailWord_6963455
  simp only [CollatzResearch.WordTrace]
  refine ⟨253978068987599273277011819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169318712658399515518007879 253978068987599273277011819)
  ·
    refine ⟨380967103481398909915517729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253978068987599273277011819 380967103481398909915517729)
    ·
      refine ⟨285725327611049182436638297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380967103481398909915517729 285725327611049182436638297)
      ·
        refine ⟨214293995708286886827478723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285725327611049182436638297 214293995708286886827478723)
        ·
          refine ⟨321440993562430330241218085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214293995708286886827478723 321440993562430330241218085)
          ·
            refine ⟨60270186292955686920228391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321440993562430330241218085 60270186292955686920228391)
            ·
              refine ⟨90405279439433530380342587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60270186292955686920228391 90405279439433530380342587)
              ·
                refine ⟨135607919159150295570513881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90405279439433530380342587 135607919159150295570513881)
                ·
                  refine ⟨101705939369362721677885411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135607919159150295570513881 101705939369362721677885411)
                  ·
                    refine ⟨152558909054044082516828117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101705939369362721677885411 152558909054044082516828117)
                    ·
                      refine ⟨3575599430954158183988159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152558909054044082516828117 3575599430954158183988159)
                      ·
                        rfl

theorem cell23_6963455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_6963455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963455 prefixEnd_6963455 := by exact prefixLift 6963455
  have htrace : WordTrace (prefixWord ++ tailWord_6963455) baseStart_6963455 baseEnd_6963455 := by
    simpa [prefixWord, tailWord_6963455, baseEnd_6963455] using wordTrace_append hprefix tailTrace_6963455
  have hstable : (prefixWord ++ tailWord_6963455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963455).length < 2 ^ (prefixWord ++ tailWord_6963455).sum := by decide
  have hdescent : baseEnd_6963455 < baseStart_6963455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963459 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 3]
def baseStart_6963459 : Nat := 118140960795 + 6963459 * 2 ^ 59
def prefixEnd_6963459 : Nat := 4983230072969 + 3 ^ 40 * 6963459 * 2
def baseEnd_6963459 : Nat := 3575601484876776168338141

theorem tailTrace_6963459 : CollatzResearch.WordTrace tailWord_6963459 prefixEnd_6963459 3575601484876776168338141 := by
  unfold tailWord_6963459
  simp only [CollatzResearch.WordTrace]
  refine ⟨253978214879584781960157431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169318809919723187973438287 253978214879584781960157431)
  ·
    refine ⟨380967322319377172940236147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253978214879584781960157431 380967322319377172940236147)
    ·
      refine ⟨571450983479065759410354221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380967322319377172940236147 571450983479065759410354221)
      ·
        refine ⟨214294118804649659778882833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571450983479065759410354221 214294118804649659778882833)
        ·
          refine ⟨160720589103487244834162125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214294118804649659778882833 160720589103487244834162125)
          ·
            refine ⟨60270220913807716812810797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160720589103487244834162125 60270220913807716812810797)
            ·
              refine ⟨22601332842677893804804049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60270220913807716812810797 22601332842677893804804049)
              ·
                refine ⟨16950999632008420353603037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22601332842677893804804049 16950999632008420353603037)
                ·
                  refine ⟨6356624862003157632601139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16950999632008420353603037 6356624862003157632601139)
                  ·
                    refine ⟨9534937293004736448901709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6356624862003157632601139 9534937293004736448901709)
                    ·
                      refine ⟨3575601484876776168338141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534937293004736448901709 3575601484876776168338141)
                      ·
                        rfl

theorem cell23_6963459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_6963459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963459 prefixEnd_6963459 := by exact prefixLift 6963459
  have htrace : WordTrace (prefixWord ++ tailWord_6963459) baseStart_6963459 baseEnd_6963459 := by
    simpa [prefixWord, tailWord_6963459, baseEnd_6963459] using wordTrace_append hprefix tailTrace_6963459
  have hstable : (prefixWord ++ tailWord_6963459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963459).length < 2 ^ (prefixWord ++ tailWord_6963459).sum := by decide
  have hdescent : baseEnd_6963459 < baseStart_6963459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963463 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6963463 : Nat := 118140960795 + 6963463 * 2 ^ 59
def prefixEnd_6963463 : Nat := 4983230072969 + 3 ^ 40 * 6963463 * 2
def baseEnd_6963463 : Nat := 3575603538799394152688123

theorem tailTrace_6963463 : CollatzResearch.WordTrace tailWord_6963463 prefixEnd_6963463 3575603538799394152688123 := by
  unfold tailWord_6963463
  simp only [CollatzResearch.WordTrace]
  refine ⟨253978360771570290643303043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169318907181046860428868695 253978360771570290643303043)
  ·
    refine ⟨380967541157355435964954565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253978360771570290643303043 380967541157355435964954565)
    ·
      refine ⟨71431413967004144243428981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380967541157355435964954565 71431413967004144243428981)
      ·
        refine ⟨6696695059406638522821467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71431413967004144243428981 6696695059406638522821467)
        ·
          refine ⟨10045042589109957784232201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6696695059406638522821467 10045042589109957784232201)
          ·
            refine ⟨7533781941832468338174151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10045042589109957784232201 7533781941832468338174151)
            ·
              refine ⟨11300672912748702507261227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533781941832468338174151 11300672912748702507261227)
              ·
                refine ⟨16951009369123053760891841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11300672912748702507261227 16951009369123053760891841)
                ·
                  refine ⟨12713257026842290320668881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16951009369123053760891841 12713257026842290320668881)
                  ·
                    refine ⟨9534942770131717740501661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12713257026842290320668881 9534942770131717740501661)
                    ·
                      refine ⟨3575603538799394152688123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9534942770131717740501661 3575603538799394152688123)
                      ·
                        rfl

theorem cell23_6963463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6963463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963463 prefixEnd_6963463 := by exact prefixLift 6963463
  have htrace : WordTrace (prefixWord ++ tailWord_6963463) baseStart_6963463 baseEnd_6963463 := by
    simpa [prefixWord, tailWord_6963463, baseEnd_6963463] using wordTrace_append hprefix tailTrace_6963463
  have hstable : (prefixWord ++ tailWord_6963463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963463).length < 2 ^ (prefixWord ++ tailWord_6963463).sum := by decide
  have hdescent : baseEnd_6963463 < baseStart_6963463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963479 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 1, 5]
def baseStart_6963479 : Nat := 118140960795 + 6963479 * 2 ^ 59
def prefixEnd_6963479 : Nat := 4983230072969 + 3 ^ 40 * 6963479 * 2
def baseEnd_6963479 : Nat := 1191870584829955363362683

theorem tailTrace_6963479 : CollatzResearch.WordTrace tailWord_6963479 prefixEnd_6963479 1191870584829955363362683 := by
  unfold tailWord_6963479
  simp only [CollatzResearch.WordTrace]
  refine ⟨253978944339512325375885491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169319296226341550250590327 253978944339512325375885491)
  ·
    refine ⟨380968416509268488063828237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253978944339512325375885491 380968416509268488063828237)
    ·
      refine ⟨142863156190975683023935589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380968416509268488063828237 142863156190975683023935589)
      ·
        refine ⟨26786841785807940566987923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142863156190975683023935589 26786841785807940566987923)
        ·
          refine ⟨40180262678711910850481885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26786841785807940566987923 40180262678711910850481885)
          ·
            refine ⟨15067598504516966568930707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40180262678711910850481885 15067598504516966568930707)
            ·
              refine ⟨22601397756775449853396061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067598504516966568930707 22601397756775449853396061)
              ·
                refine ⟨8475524158790793695023523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22601397756775449853396061 8475524158790793695023523)
                ·
                  refine ⟨12713286238186190542535285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475524158790793695023523 12713286238186190542535285)
                  ·
                    refine ⟨1191870584829955363362683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12713286238186190542535285 1191870584829955363362683)
                    ·
                      rfl

theorem cell23_6963479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_6963479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963479 prefixEnd_6963479 := by exact prefixLift 6963479
  have htrace : WordTrace (prefixWord ++ tailWord_6963479) baseStart_6963479 baseEnd_6963479 := by
    simpa [prefixWord, tailWord_6963479, baseEnd_6963479] using wordTrace_append hprefix tailTrace_6963479
  have hstable : (prefixWord ++ tailWord_6963479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963479).length < 2 ^ (prefixWord ++ tailWord_6963479).sum := by decide
  have hdescent : baseEnd_6963479 < baseStart_6963479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963515 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_6963515 : Nat := 118140960795 + 6963515 * 2 ^ 59
def prefixEnd_6963515 : Nat := 4983230072969 + 3 ^ 40 * 6963515 * 2
def baseEnd_6963515 : Nat := 3575630239793427949237883

theorem tailTrace_6963515 : CollatzResearch.WordTrace tailWord_6963515 prefixEnd_6963515 3575630239793427949237883 := by
  unfold tailWord_6963515
  simp only [CollatzResearch.WordTrace]
  refine ⟨253980257367381903524195999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169320171578254602349463999 253980257367381903524195999)
  ·
    refine ⟨380970386051072855286293999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253980257367381903524195999 380970386051072855286293999)
    ·
      refine ⟨571455579076609282929440999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380970386051072855286293999 571455579076609282929440999)
      ·
        refine ⟨857183368614913924394161499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571455579076609282929440999 857183368614913924394161499)
        ·
          refine ⟨1285775052922370886591242249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857183368614913924394161499 1285775052922370886591242249)
          ·
            refine ⟨964331289691778164943431687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285775052922370886591242249 964331289691778164943431687)
            ·
              refine ⟨1446496934537667247415147531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964331289691778164943431687 1446496934537667247415147531)
              ·
                refine ⟨2169745401806500871122721297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446496934537667247415147531 2169745401806500871122721297)
                ·
                  refine ⟨1627309051354875653342040973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169745401806500871122721297 1627309051354875653342040973)
                  ·
                    refine ⟨610240894258078370003265365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1627309051354875653342040973 610240894258078370003265365)
                    ·
                      refine ⟨3575630239793427949237883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 610240894258078370003265365 3575630239793427949237883)
                      ·
                        rfl

theorem cell23_6963515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_6963515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963515 prefixEnd_6963515 := by exact prefixLift 6963515
  have htrace : WordTrace (prefixWord ++ tailWord_6963515) baseStart_6963515 baseEnd_6963515 := by
    simpa [prefixWord, tailWord_6963515, baseEnd_6963515] using wordTrace_append hprefix tailTrace_6963515
  have hstable : (prefixWord ++ tailWord_6963515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963515).length < 2 ^ (prefixWord ++ tailWord_6963515).sum := by decide
  have hdescent : baseEnd_6963515 < baseStart_6963515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963516 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_6963516 : Nat := 118140960795 + 6963516 * 2 ^ 59
def prefixEnd_6963516 : Nat := 4983230072969 + 3 ^ 40 * 6963516 * 2
def baseEnd_6963516 : Nat := 3575630753274082445325379

theorem tailTrace_6963516 : CollatzResearch.WordTrace tailWord_6963516 prefixEnd_6963516 3575630753274082445325379 := by
  unfold tailWord_6963516
  simp only [CollatzResearch.WordTrace]
  refine ⟨126990146920189140347491201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169320195893585520463321601 126990146920189140347491201)
  ·
    refine ⟨95242610190141855260618401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126990146920189140347491201 95242610190141855260618401)
    ·
      refine ⟨71431957642606391445463801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95242610190141855260618401 71431957642606391445463801)
      ·
        refine ⟨53573968231954793584097851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71431957642606391445463801 53573968231954793584097851)
        ·
          refine ⟨80360952347932190376146777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53573968231954793584097851 80360952347932190376146777)
          ·
            refine ⟨60270714260949142782110083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80360952347932190376146777 60270714260949142782110083)
            ·
              refine ⟨90406071391423714173165125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60270714260949142782110083 90406071391423714173165125)
              ·
                refine ⟨16951138385891946407468461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90406071391423714173165125 16951138385891946407468461)
                ·
                  refine ⟨6356676894709479902800673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16951138385891946407468461 6356676894709479902800673)
                  ·
                    refine ⟨4767507671032109927100505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6356676894709479902800673 4767507671032109927100505)
                    ·
                      refine ⟨3575630753274082445325379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767507671032109927100505 3575630753274082445325379)
                      ·
                        rfl

theorem cell23_6963516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_6963516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963516 prefixEnd_6963516 := by exact prefixLift 6963516
  have htrace : WordTrace (prefixWord ++ tailWord_6963516) baseStart_6963516 baseEnd_6963516 := by
    simpa [prefixWord, tailWord_6963516, baseEnd_6963516] using wordTrace_append hprefix tailTrace_6963516
  have hstable : (prefixWord ++ tailWord_6963516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963516).length < 2 ^ (prefixWord ++ tailWord_6963516).sum := by decide
  have hdescent : baseEnd_6963516 < baseStart_6963516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963619 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4]
def baseStart_6963619 : Nat := 118140960795 + 6963619 * 2 ^ 59
def prefixEnd_6963619 : Nat := 4983230072969 + 3 ^ 40 * 6963619 * 2
def baseEnd_6963619 : Nat := 3575683641781495542337405

theorem tailTrace_6963619 : CollatzResearch.WordTrace tailWord_6963619 prefixEnd_6963619 3575683641781495542337405 := by
  unfold tailWord_6963619
  simp only [CollatzResearch.WordTrace]
  refine ⟨253984050559005129285981911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169322700372670086190654607 253984050559005129285981911)
  ·
    refine ⟨380976075838507693928972867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253984050559005129285981911 380976075838507693928972867)
    ·
      refine ⟨571464113757761540893459301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380976075838507693928972867 571464113757761540893459301)
      ·
        refine ⟨107149521329580288917523619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 571464113757761540893459301 107149521329580288917523619)
        ·
          refine ⟨160724281994370433376285429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107149521329580288917523619 160724281994370433376285429)
          ·
            refine ⟨15067901436972228129026759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160724281994370433376285429 15067901436972228129026759)
            ·
              refine ⟨22601852155458342193540139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067901436972228129026759 22601852155458342193540139)
              ·
                refine ⟨33902778233187513290310209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22601852155458342193540139 33902778233187513290310209)
                ·
                  refine ⟨25427083674890634967732657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33902778233187513290310209 25427083674890634967732657)
                  ·
                    refine ⟨19070312756167976225799493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25427083674890634967732657 19070312756167976225799493)
                    ·
                      refine ⟨3575683641781495542337405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19070312756167976225799493 3575683641781495542337405)
                      ·
                        rfl

theorem cell23_6963619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_6963619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963619 prefixEnd_6963619 := by exact prefixLift 6963619
  have htrace : WordTrace (prefixWord ++ tailWord_6963619) baseStart_6963619 baseEnd_6963619 := by
    simpa [prefixWord, tailWord_6963619, baseEnd_6963619] using wordTrace_append hprefix tailTrace_6963619
  have hstable : (prefixWord ++ tailWord_6963619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963619).length < 2 ^ (prefixWord ++ tailWord_6963619).sum := by decide
  have hdescent : baseEnd_6963619 < baseStart_6963619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963623 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_6963623 : Nat := 118140960795 + 6963623 * 2 ^ 59
def prefixEnd_6963623 : Nat := 4983230072969 + 3 ^ 40 * 6963623 * 2
def baseEnd_6963623 : Nat := 3575685695704113526687387

theorem tailTrace_6963623 : CollatzResearch.WordTrace tailWord_6963623 prefixEnd_6963623 3575685695704113526687387 := by
  unfold tailWord_6963623
  simp only [CollatzResearch.WordTrace]
  refine ⟨253984196450990637969127523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169322797633993758646085015 253984196450990637969127523)
  ·
    refine ⟨380976294676485956953691285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253984196450990637969127523 380976294676485956953691285)
    ·
      refine ⟨17858263812960279232204279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 380976294676485956953691285 17858263812960279232204279)
      ·
        refine ⟨26787395719440418848306419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17858263812960279232204279 26787395719440418848306419)
        ·
          refine ⟨40181093579160628272459629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26787395719440418848306419 40181093579160628272459629)
          ·
            refine ⟨15067910092185235602172361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40181093579160628272459629 15067910092185235602172361)
            ·
              refine ⟨11300932569138926701629271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15067910092185235602172361 11300932569138926701629271)
              ·
                refine ⟨16951398853708390052443907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11300932569138926701629271 16951398853708390052443907)
                ·
                  refine ⟨25427098280562585078665861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16951398853708390052443907 25427098280562585078665861)
                  ·
                    refine ⟨4767580927605484702249849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25427098280562585078665861 4767580927605484702249849)
                    ·
                      refine ⟨3575685695704113526687387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767580927605484702249849 3575685695704113526687387)
                      ·
                        rfl

theorem cell23_6963623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_6963623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963623 prefixEnd_6963623 := by exact prefixLift 6963623
  have htrace : WordTrace (prefixWord ++ tailWord_6963623) baseStart_6963623 baseEnd_6963623 := by
    simpa [prefixWord, tailWord_6963623, baseEnd_6963623] using wordTrace_append hprefix tailTrace_6963623
  have hstable : (prefixWord ++ tailWord_6963623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963623).length < 2 ^ (prefixWord ++ tailWord_6963623).sum := by decide
  have hdescent : baseEnd_6963623 < baseStart_6963623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963646 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_6963646 : Nat := 118140960795 + 6963646 * 2 ^ 59
def prefixEnd_6963646 : Nat := 4983230072969 + 3 ^ 40 * 6963646 * 2
def baseEnd_6963646 : Nat := 397299722862129659633309

theorem tailTrace_6963646 : CollatzResearch.WordTrace tailWord_6963646 prefixEnd_6963646 397299722862129659633309 := by
  unfold tailWord_6963646
  simp only [CollatzResearch.WordTrace]
  refine ⟨31748129416238414112151849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169323356886604875264809861 31748129416238414112151849)
  ·
    refine ⟨23811097062178810584113887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31748129416238414112151849 23811097062178810584113887)
    ·
      refine ⟨35716645593268215876170831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23811097062178810584113887 35716645593268215876170831)
      ·
        refine ⟨53574968389902323814256247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35716645593268215876170831 53574968389902323814256247)
        ·
          refine ⟨80362452584853485721384371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53574968389902323814256247 80362452584853485721384371)
          ·
            refine ⟨120543678877280228582076557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80362452584853485721384371 120543678877280228582076557)
            ·
              refine ⟨45203879578980085718278709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120543678877280228582076557 45203879578980085718278709)
              ·
                refine ⟨4237863710529383036088629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45203879578980085718278709 4237863710529383036088629)
                ·
                  refine ⟨397299722862129659633309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4237863710529383036088629 397299722862129659633309)
                  ·
                    rfl

theorem cell23_6963646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_6963646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963646 prefixEnd_6963646 := by exact prefixLift 6963646
  have htrace : WordTrace (prefixWord ++ tailWord_6963646) baseStart_6963646 baseEnd_6963646 := by
    simpa [prefixWord, tailWord_6963646, baseEnd_6963646] using wordTrace_append hprefix tailTrace_6963646
  have hstable : (prefixWord ++ tailWord_6963646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963646).length < 2 ^ (prefixWord ++ tailWord_6963646).sum := by decide
  have hdescent : baseEnd_6963646 < baseStart_6963646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963679 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_6963679 : Nat := 118140960795 + 6963679 * 2 ^ 59
def prefixEnd_6963679 : Nat := 4983230072969 + 3 ^ 40 * 6963679 * 2
def baseEnd_6963679 : Nat := 3575714450620765307587129

theorem tailTrace_6963679 : CollatzResearch.WordTrace tailWord_6963679 prefixEnd_6963679 3575714450620765307587129 := by
  unfold tailWord_6963679
  simp only [CollatzResearch.WordTrace]
  refine ⟨253986238938787759533166091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169324159292525173022110727 253986238938787759533166091)
  ·
    refine ⟨380979358408181639299749137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253986238938787759533166091 380979358408181639299749137)
    ·
      refine ⟨285734518806136229474811853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380979358408181639299749137 285734518806136229474811853)
      ·
        refine ⟨107150444552301086053054445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285734518806136229474811853 107150444552301086053054445)
        ·
          refine ⟨40181416707112907269895417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107150444552301086053054445 40181416707112907269895417)
          ·
            refine ⟨30136062530334680452421563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40181416707112907269895417 30136062530334680452421563)
            ·
              refine ⟨45204093795502020678632345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30136062530334680452421563 45204093795502020678632345)
              ·
                refine ⟨33903070346626515508974259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45204093795502020678632345 33903070346626515508974259)
                ·
                  refine ⟨50854605519939773263461389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33903070346626515508974259 50854605519939773263461389)
                  ·
                    refine ⟨19070477069977414973798021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50854605519939773263461389 19070477069977414973798021)
                    ·
                      refine ⟨3575714450620765307587129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19070477069977414973798021 3575714450620765307587129)
                      ·
                        rfl

theorem cell23_6963679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_6963679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963679 prefixEnd_6963679 := by exact prefixLift 6963679
  have htrace : WordTrace (prefixWord ++ tailWord_6963679) baseStart_6963679 baseEnd_6963679 := by
    simpa [prefixWord, tailWord_6963679, baseEnd_6963679] using wordTrace_append hprefix tailTrace_6963679
  have hstable : (prefixWord ++ tailWord_6963679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963679).length < 2 ^ (prefixWord ++ tailWord_6963679).sum := by decide
  have hdescent : baseEnd_6963679 < baseStart_6963679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963689 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 5, 4]
def baseStart_6963689 : Nat := 118140960795 + 6963689 * 2 ^ 59
def prefixEnd_6963689 : Nat := 4983230072969 + 3 ^ 40 * 6963689 * 2
def baseEnd_6963689 : Nat := 1191906528475770089487361

theorem tailTrace_6963689 : CollatzResearch.WordTrace tailWord_6963689 prefixEnd_6963689 1191906528475770089487361 := by
  unfold tailWord_6963689
  simp only [CollatzResearch.WordTrace]
  refine ⟨253986603668751531241030121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169324402445834354160686747 253986603668751531241030121)
  ·
    refine ⟨190489952751563648430772591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253986603668751531241030121 190489952751563648430772591)
    ·
      refine ⟨285734929127345472646158887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190489952751563648430772591 285734929127345472646158887)
      ·
        refine ⟨428602393691018208969238331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285734929127345472646158887 428602393691018208969238331)
        ·
          refine ⟨642903590536527313453857497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428602393691018208969238331 642903590536527313453857497)
          ·
            refine ⟨482177692902395485090393123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642903590536527313453857497 482177692902395485090393123)
            ·
              refine ⟨723266539353593227635589685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482177692902395485090393123 723266539353593227635589685)
              ·
                refine ⟨67806238064399365090836533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 723266539353593227635589685 67806238064399365090836533)
                ·
                  refine ⟨6356834818537440477265925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67806238064399365090836533 6356834818537440477265925)
                  ·
                    refine ⟨1191906528475770089487361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356834818537440477265925 1191906528475770089487361)
                    ·
                      rfl

theorem cell23_6963689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_6963689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963689 prefixEnd_6963689 := by exact prefixLift 6963689
  have htrace : WordTrace (prefixWord ++ tailWord_6963689) baseStart_6963689 baseEnd_6963689 := by
    simpa [prefixWord, tailWord_6963689, baseEnd_6963689] using wordTrace_append hprefix tailTrace_6963689
  have hstable : (prefixWord ++ tailWord_6963689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963689).length < 2 ^ (prefixWord ++ tailWord_6963689).sum := by decide
  have hdescent : baseEnd_6963689 < baseStart_6963689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963699 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 3]
def baseStart_6963699 : Nat := 118140960795 + 6963699 * 2 ^ 59
def prefixEnd_6963699 : Nat := 4983230072969 + 3 ^ 40 * 6963699 * 2
def baseEnd_6963699 : Nat := 3575724720233855229337037

theorem tailTrace_6963699 : CollatzResearch.WordTrace tailWord_6963699 prefixEnd_6963699 3575724720233855229337037 := by
  unfold tailWord_6963699
  simp only [CollatzResearch.WordTrace]
  refine ⟨253986968398715302948894151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169324645599143535299262767 253986968398715302948894151)
  ·
    refine ⟨380980452598072954423341227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253986968398715302948894151 380980452598072954423341227)
    ·
      refine ⟨571470678897109431635011841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380980452598072954423341227 571470678897109431635011841)
      ·
        refine ⟨428603009172832073726258881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571470678897109431635011841 428603009172832073726258881)
        ·
          refine ⟨321452256879624055294694161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428603009172832073726258881 321452256879624055294694161)
          ·
            refine ⟨241089192659718041471020621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321452256879624055294694161 241089192659718041471020621)
            ·
              refine ⟨90408447247394265551632733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241089192659718041471020621 90408447247394265551632733)
              ·
                refine ⟨33903167717772849581862275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90408447247394265551632733 33903167717772849581862275)
                ·
                  refine ⟨50854751576659274372793413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33903167717772849581862275 50854751576659274372793413)
                  ·
                    refine ⟨9535265920623613944898765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50854751576659274372793413 9535265920623613944898765)
                    ·
                      refine ⟨3575724720233855229337037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535265920623613944898765 3575724720233855229337037)
                      ·
                        rfl

theorem cell23_6963699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_6963699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963699 prefixEnd_6963699 := by exact prefixLift 6963699
  have htrace : WordTrace (prefixWord ++ tailWord_6963699) baseStart_6963699 baseEnd_6963699 := by
    simpa [prefixWord, tailWord_6963699, baseEnd_6963699] using wordTrace_append hprefix tailTrace_6963699
  have hstable : (prefixWord ++ tailWord_6963699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963699).length < 2 ^ (prefixWord ++ tailWord_6963699).sum := by decide
  have hdescent : baseEnd_6963699 < baseStart_6963699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963723 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 3, 4]
def baseStart_6963723 : Nat := 118140960795 + 6963723 * 2 ^ 59
def prefixEnd_6963723 : Nat := 4983230072969 + 3 ^ 40 * 6963723 * 2
def baseEnd_6963723 : Nat := 1191912347923187711812309

theorem tailTrace_6963723 : CollatzResearch.WordTrace tailWord_6963723 prefixEnd_6963723 1191912347923187711812309 := by
  unfold tailWord_6963723
  simp only [CollatzResearch.WordTrace]
  refine ⟨253987843750628355047767823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169325229167085570031845215 253987843750628355047767823)
  ·
    refine ⟨380981765625942532571651735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253987843750628355047767823 380981765625942532571651735)
    ·
      refine ⟨571472648438913798857477603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380981765625942532571651735 571472648438913798857477603)
      ·
        refine ⟨857208972658370698286216405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571472648438913798857477603 857208972658370698286216405)
        ·
          refine ⟨20090835296680563241083197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 857208972658370698286216405 20090835296680563241083197)
          ·
            refine ⟨7534063236255211215406199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20090835296680563241083197 7534063236255211215406199)
            ·
              refine ⟨11301094854382816823109299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534063236255211215406199 11301094854382816823109299)
              ·
                refine ⟨16951642281574225234663949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11301094854382816823109299 16951642281574225234663949)
                ·
                  refine ⟨6356865855590334462998981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16951642281574225234663949 6356865855590334462998981)
                  ·
                    refine ⟨1191912347923187711812309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356865855590334462998981 1191912347923187711812309)
                    ·
                      rfl

theorem cell23_6963723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 4].length) (baseStart_6963723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963723 prefixEnd_6963723 := by exact prefixLift 6963723
  have htrace : WordTrace (prefixWord ++ tailWord_6963723) baseStart_6963723 baseEnd_6963723 := by
    simpa [prefixWord, tailWord_6963723, baseEnd_6963723] using wordTrace_append hprefix tailTrace_6963723
  have hstable : (prefixWord ++ tailWord_6963723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963723).length < 2 ^ (prefixWord ++ tailWord_6963723).sum := by decide
  have hdescent : baseEnd_6963723 < baseStart_6963723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963729 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_6963729 : Nat := 118140960795 + 6963729 * 2 ^ 59
def prefixEnd_6963729 : Nat := 4983230072969 + 3 ^ 40 * 6963729 * 2
def baseEnd_6963729 : Nat := 3575740124653490111961899

theorem tailTrace_6963729 : CollatzResearch.WordTrace tailWord_6963729 prefixEnd_6963729 3575740124653490111961899 := by
  unfold tailWord_6963729
  simp only [CollatzResearch.WordTrace]
  refine ⟨253988062588606618072486241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169325375059071078714990827 253988062588606618072486241)
  ·
    refine ⟨190491046941454963554364681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253988062588606618072486241 190491046941454963554364681)
    ·
      refine ⟨142868285206091222665773511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190491046941454963554364681 142868285206091222665773511)
      ·
        refine ⟨214302427809136833998660267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142868285206091222665773511 214302427809136833998660267)
        ·
          refine ⟨321453641713705250997990401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214302427809136833998660267 321453641713705250997990401)
          ·
            refine ⟨241090231285278938248492801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321453641713705250997990401 241090231285278938248492801)
            ·
              refine ⟨180817673463959203686369601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241090231285278938248492801 180817673463959203686369601)
              ·
                refine ⟨135613255097969402764777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180817673463959203686369601 135613255097969402764777201)
                ·
                  refine ⟨101709941323477052073582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135613255097969402764777201 101709941323477052073582901)
                  ·
                    refine ⟨9535306999075973631898397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101709941323477052073582901 9535306999075973631898397)
                    ·
                      refine ⟨3575740124653490111961899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535306999075973631898397 3575740124653490111961899)
                      ·
                        rfl

theorem cell23_6963729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_6963729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963729 prefixEnd_6963729 := by exact prefixLift 6963729
  have htrace : WordTrace (prefixWord ++ tailWord_6963729) baseStart_6963729 baseEnd_6963729 := by
    simpa [prefixWord, tailWord_6963729, baseEnd_6963729] using wordTrace_append hprefix tailTrace_6963729
  have hstable : (prefixWord ++ tailWord_6963729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963729).length < 2 ^ (prefixWord ++ tailWord_6963729).sum := by decide
  have hdescent : baseEnd_6963729 < baseStart_6963729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963736 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 6]
def baseStart_6963736 : Nat := 118140960795 + 6963736 * 2 ^ 59
def prefixEnd_6963736 : Nat := 4983230072969 + 3 ^ 40 * 6963736 * 2
def baseEnd_6963736 : Nat := 397304857668674620508263

theorem tailTrace_6963736 : CollatzResearch.WordTrace tailWord_6963736 prefixEnd_6963736 397304857668674620508263 := by
  unfold tailWord_6963736
  simp only [CollatzResearch.WordTrace]
  refine ⟨126994158949790629133995531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169325545266387505511994041 126994158949790629133995531)
  ·
    refine ⟨190491238424685943700993297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126994158949790629133995531 190491238424685943700993297)
    ·
      refine ⟨142868428818514457775744973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190491238424685943700993297 142868428818514457775744973)
      ·
        refine ⟨53575660806942921665904365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142868428818514457775744973 53575660806942921665904365)
        ·
          refine ⟨20090872802603595624714137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53575660806942921665904365 20090872802603595624714137)
          ·
            refine ⟨15068154601952696718535603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20090872802603595624714137 15068154601952696718535603)
            ·
              refine ⟨22602231902929045077803405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15068154601952696718535603 22602231902929045077803405)
              ·
                refine ⟨8475836963598391904176277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22602231902929045077803405 8475836963598391904176277)
                ·
                  refine ⟨397304857668674620508263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8475836963598391904176277 397304857668674620508263)
                  ·
                    rfl

theorem cell23_6963736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 6].length) (baseStart_6963736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963736 prefixEnd_6963736 := by exact prefixLift 6963736
  have htrace : WordTrace (prefixWord ++ tailWord_6963736) baseStart_6963736 baseEnd_6963736 := by
    simpa [prefixWord, tailWord_6963736, baseEnd_6963736] using wordTrace_append hprefix tailTrace_6963736
  have hstable : (prefixWord ++ tailWord_6963736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963736).length < 2 ^ (prefixWord ++ tailWord_6963736).sum := by decide
  have hdescent : baseEnd_6963736 < baseStart_6963736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963756 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 1, 5, 2]
def baseStart_6963756 : Nat := 118140960795 + 6963756 * 2 ^ 59
def prefixEnd_6963756 : Nat := 4983230072969 + 3 ^ 40 * 6963756 * 2
def baseEnd_6963756 : Nat := 3575753988631161506324275

theorem tailTrace_6963756 : CollatzResearch.WordTrace tailWord_6963756 prefixEnd_6963756 3575753988631161506324275 := by
  unfold tailWord_6963756
  simp only [CollatzResearch.WordTrace]
  refine ⟨126994523679754400841859561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169326031573005867789146081 126994523679754400841859561)
  ·
    refine ⟨95245892759815800631394671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126994523679754400841859561 95245892759815800631394671)
    ·
      refine ⟨142868839139723700947092007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95245892759815800631394671 142868839139723700947092007)
      ·
        refine ⟨214303258709585551420638011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142868839139723700947092007 214303258709585551420638011)
        ·
          refine ⟨321454888064378327130957017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214303258709585551420638011 321454888064378327130957017)
          ·
            refine ⟨241091166048283745348217763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321454888064378327130957017 241091166048283745348217763)
            ·
              refine ⟨361636749072425618022326645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241091166048283745348217763 361636749072425618022326645)
              ·
                refine ⟨33903445225539901689593123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361636749072425618022326645 33903445225539901689593123)
                ·
                  refine ⟨50855167838309852534389685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33903445225539901689593123 50855167838309852534389685)
                  ·
                    refine ⟨4767671984841548675099033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50855167838309852534389685 4767671984841548675099033)
                    ·
                      refine ⟨3575753988631161506324275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767671984841548675099033 3575753988631161506324275)
                      ·
                        rfl

theorem cell23_6963756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_6963756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963756 prefixEnd_6963756 := by exact prefixLift 6963756
  have htrace : WordTrace (prefixWord ++ tailWord_6963756) baseStart_6963756 baseEnd_6963756 := by
    simpa [prefixWord, tailWord_6963756, baseEnd_6963756] using wordTrace_append hprefix tailTrace_6963756
  have hstable : (prefixWord ++ tailWord_6963756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963756).length < 2 ^ (prefixWord ++ tailWord_6963756).sum := by decide
  have hdescent : baseEnd_6963756 < baseStart_6963756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963786 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_6963786 : Nat := 118140960795 + 6963786 * 2 ^ 59
def prefixEnd_6963786 : Nat := 4983230072969 + 3 ^ 40 * 6963786 * 2
def baseEnd_6963786 : Nat := 3575769393050796388949137

theorem tailTrace_6963786 : CollatzResearch.WordTrace tailWord_6963786 prefixEnd_6963786 3575769393050796388949137 := by
  unfold tailWord_6963786
  simp only [CollatzResearch.WordTrace]
  refine ⟨63497535387350029201827803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169326761032933411204874141 63497535387350029201827803)
  ·
    refine ⟨95246303081025043802741705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63497535387350029201827803 95246303081025043802741705)
    ·
      refine ⟨71434727310768782852056279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95246303081025043802741705 71434727310768782852056279)
      ·
        refine ⟨107152090966153174278084419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71434727310768782852056279 107152090966153174278084419)
        ·
          refine ⟨160728136449229761417126629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107152090966153174278084419 160728136449229761417126629)
          ·
            refine ⟨30136525584230580265711243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160728136449229761417126629 30136525584230580265711243)
            ·
              refine ⟨45204788376345870398566865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30136525584230580265711243 45204788376345870398566865)
              ·
                refine ⟨33903591282259402798925149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45204788376345870398566865 33903591282259402798925149)
                ·
                  refine ⟨12713846730847276049596931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33903591282259402798925149 12713846730847276049596931)
                  ·
                    refine ⟨19070770096270914074395397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12713846730847276049596931 19070770096270914074395397)
                    ·
                      refine ⟨3575769393050796388949137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19070770096270914074395397 3575769393050796388949137)
                      ·
                        rfl

theorem cell23_6963786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_6963786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963786 prefixEnd_6963786 := by exact prefixLift 6963786
  have htrace : WordTrace (prefixWord ++ tailWord_6963786) baseStart_6963786 baseEnd_6963786 := by
    simpa [prefixWord, tailWord_6963786, baseEnd_6963786] using wordTrace_append hprefix tailTrace_6963786
  have hstable : (prefixWord ++ tailWord_6963786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963786).length < 2 ^ (prefixWord ++ tailWord_6963786).sum := by decide
  have hdescent : baseEnd_6963786 < baseStart_6963786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963796 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_6963796 : Nat := 118140960795 + 6963796 * 2 ^ 59
def prefixEnd_6963796 : Nat := 4983230072969 + 3 ^ 40 * 6963796 * 2
def baseEnd_6963796 : Nat := 1191924842619113783274697

theorem tailTrace_6963796 : CollatzResearch.WordTrace tailWord_6963796 prefixEnd_6963796 1191924842619113783274697 := by
  unfold tailWord_6963796
  simp only [CollatzResearch.WordTrace]
  refine ⟨126995253139681944257587621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169327004186242592343450161 126995253139681944257587621)
  ·
    refine ⟨23811609963690364548297679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126995253139681944257587621 23811609963690364548297679)
    ·
      refine ⟨35717414945535546822446519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23811609963690364548297679 35717414945535546822446519)
      ·
        refine ⟨53576122418303320233669779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35717414945535546822446519 53576122418303320233669779)
        ·
          refine ⟨80364183627454980350504669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53576122418303320233669779 80364183627454980350504669)
          ·
            refine ⟨30136568860295617631439251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80364183627454980350504669 30136568860295617631439251)
            ·
              refine ⟨45204853290443426447158877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30136568860295617631439251 45204853290443426447158877)
              ·
                refine ⟨16951819983916284917684579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45204853290443426447158877 16951819983916284917684579)
                ·
                  refine ⟨25427729975874427376526869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16951819983916284917684579 25427729975874427376526869)
                  ·
                    refine ⟨1191924842619113783274697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25427729975874427376526869 1191924842619113783274697)
                    ·
                      rfl

theorem cell23_6963796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_6963796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963796 prefixEnd_6963796 := by exact prefixLift 6963796
  have htrace : WordTrace (prefixWord ++ tailWord_6963796) baseStart_6963796 baseEnd_6963796 := by
    simpa [prefixWord, tailWord_6963796, baseEnd_6963796] using wordTrace_append hprefix tailTrace_6963796
  have hstable : (prefixWord ++ tailWord_6963796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963796).length < 2 ^ (prefixWord ++ tailWord_6963796).sum := by decide
  have hdescent : baseEnd_6963796 < baseStart_6963796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963826 : List Nat := [3, 2, 1, 2, 4, 1, 10]
def baseStart_6963826 : Nat := 118140960795 + 6963826 * 2 ^ 59
def prefixEnd_6963826 : Nat := 4983230072969 + 3 ^ 40 * 6963826 * 2
def baseEnd_6963826 : Nat := 44145554719468842375913

theorem tailTrace_6963826 : CollatzResearch.WordTrace tailWord_6963826 prefixEnd_6963826 44145554719468842375913 := by
  unfold tailWord_6963826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63497900117313800909691833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169327733646170135759178221 63497900117313800909691833)
  ·
    refine ⟨47623425087985350682268875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63497900117313800909691833 47623425087985350682268875)
    ·
      refine ⟨71435137631978026023403313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47623425087985350682268875 71435137631978026023403313)
      ·
        refine ⟨53576353223983519517552485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71435137631978026023403313 53576353223983519517552485)
        ·
          refine ⟨10045566229496909909541091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53576353223983519517552485 10045566229496909909541091)
          ·
            refine ⟨15068349344245364864311637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045566229496909909541091 15068349344245364864311637)
            ·
              refine ⟨44145554719468842375913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15068349344245364864311637 44145554719468842375913)
              ·
                rfl

theorem cell23_6963826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 10].length) (baseStart_6963826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963826 prefixEnd_6963826 := by exact prefixLift 6963826
  have htrace : WordTrace (prefixWord ++ tailWord_6963826) baseStart_6963826 baseEnd_6963826 := by
    simpa [prefixWord, tailWord_6963826, baseEnd_6963826] using wordTrace_append hprefix tailTrace_6963826
  have hstable : (prefixWord ++ tailWord_6963826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963826).length < 2 ^ (prefixWord ++ tailWord_6963826).sum := by decide
  have hdescent : baseEnd_6963826 < baseStart_6963826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963830 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6963830 : Nat := 118140960795 + 6963830 * 2 ^ 59
def prefixEnd_6963830 : Nat := 4983230072969 + 3 ^ 40 * 6963830 * 2
def baseEnd_6963830 : Nat := 1191930662066531405599645

theorem tailTrace_6963830 : CollatzResearch.WordTrace tailWord_6963830 prefixEnd_6963830 1191930662066531405599645 := by
  unfold tailWord_6963830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874484147577544520119559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169327830907493808214608629 15874484147577544520119559)
  ·
    refine ⟨23811726221366316780179339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15874484147577544520119559 23811726221366316780179339)
    ·
      refine ⟨35717589332049475170269009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23811726221366316780179339 35717589332049475170269009)
      ·
        refine ⟨26788191999037106377701757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35717589332049475170269009 26788191999037106377701757)
        ·
          refine ⟨10045571999638914891638159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26788191999037106377701757 10045571999638914891638159)
          ·
            refine ⟨15068357999458372337457239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045571999638914891638159 15068357999458372337457239)
            ·
              refine ⟨22602536999187558506185859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15068357999458372337457239 22602536999187558506185859)
              ·
                refine ⟨33903805498781337759278789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22602536999187558506185859 33903805498781337759278789)
                ·
                  refine ⟨6356963531021500829864773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33903805498781337759278789 6356963531021500829864773)
                  ·
                    refine ⟨1191930662066531405599645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356963531021500829864773 1191930662066531405599645)
                    ·
                      rfl

theorem cell23_6963830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6963830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963830 prefixEnd_6963830 := by exact prefixLift 6963830
  have htrace : WordTrace (prefixWord ++ tailWord_6963830) baseStart_6963830 baseEnd_6963830 := by
    simpa [prefixWord, tailWord_6963830, baseEnd_6963830] using wordTrace_append hprefix tailTrace_6963830
  have hstable : (prefixWord ++ tailWord_6963830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963830).length < 2 ^ (prefixWord ++ tailWord_6963830).sum := by decide
  have hdescent : baseEnd_6963830 < baseStart_6963830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963836 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_6963836 : Nat := 118140960795 + 6963836 * 2 ^ 59
def prefixEnd_6963836 : Nat := 4983230072969 + 3 ^ 40 * 6963836 * 2
def baseEnd_6963836 : Nat := 3575795067083521193323907

theorem tailTrace_6963836 : CollatzResearch.WordTrace tailWord_6963836 prefixEnd_6963836 3575795067083521193323907 := by
  unfold tailWord_6963836
  simp only [CollatzResearch.WordTrace]
  refine ⟨126995982599609487673315681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169327976799479316897754241 126995982599609487673315681)
  ·
    refine ⟨95246986949707115754986761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126995982599609487673315681 95246986949707115754986761)
    ·
      refine ⟨71435240212280336816240071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95246986949707115754986761 71435240212280336816240071)
      ·
        refine ⟨107152860318420505224360107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71435240212280336816240071 107152860318420505224360107)
        ·
          refine ⟨160729290477630757836540161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107152860318420505224360107 160729290477630757836540161)
          ·
            refine ⟨120546967858223068377405121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160729290477630757836540161 120546967858223068377405121)
            ·
              refine ⟨90410225893667301283053841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120546967858223068377405121 90410225893667301283053841)
              ·
                refine ⟨67807669420250475962290381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90410225893667301283053841 67807669420250475962290381)
                ·
                  refine ⟨25427876032593928485858893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67807669420250475962290381 25427876032593928485858893)
                  ·
                    refine ⟨9535453512222723182197085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25427876032593928485858893 9535453512222723182197085)
                    ·
                      refine ⟨3575795067083521193323907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535453512222723182197085 3575795067083521193323907)
                      ·
                        rfl

theorem cell23_6963836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_6963836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963836 prefixEnd_6963836 := by exact prefixLift 6963836
  have htrace : WordTrace (prefixWord ++ tailWord_6963836) baseStart_6963836 baseEnd_6963836 := by
    simpa [prefixWord, tailWord_6963836, baseEnd_6963836] using wordTrace_append hprefix tailTrace_6963836
  have hstable : (prefixWord ++ tailWord_6963836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963836).length < 2 ^ (prefixWord ++ tailWord_6963836).sum := by decide
  have hdescent : baseEnd_6963836 < baseStart_6963836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963837 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_6963837 : Nat := 118140960795 + 6963837 * 2 ^ 59
def prefixEnd_6963837 : Nat := 4983230072969 + 3 ^ 40 * 6963837 * 2
def baseEnd_6963837 : Nat := 3575795580564175689411403

theorem tailTrace_6963837 : CollatzResearch.WordTrace tailWord_6963837 prefixEnd_6963837 3575795580564175689411403 := by
  unfold tailWord_6963837
  simp only [CollatzResearch.WordTrace]
  refine ⟨253992001672215352517417765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169328001114810235011611843 253992001672215352517417765)
  ·
    refine ⟨47623500313540378597015831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253992001672215352517417765 47623500313540378597015831)
    ·
      refine ⟨71435250470310567895523747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47623500313540378597015831 71435250470310567895523747)
      ·
        refine ⟨107152875705465851843285621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71435250470310567895523747 107152875705465851843285621)
        ·
          refine ⟨10045582097387423610308027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107152875705465851843285621 10045582097387423610308027)
          ·
            refine ⟨15068373146081135415462041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045582097387423610308027 15068373146081135415462041)
            ·
              refine ⟨11301279859560851561596531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15068373146081135415462041 11301279859560851561596531)
              ·
                refine ⟨16951919789341277342394797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11301279859560851561596531 16951919789341277342394797)
                ·
                  refine ⟨6356969921002979003398049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16951919789341277342394797 6356969921002979003398049)
                  ·
                    refine ⟨4767727440752234252548537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6356969921002979003398049 4767727440752234252548537)
                    ·
                      refine ⟨3575795580564175689411403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767727440752234252548537 3575795580564175689411403)
                      ·
                        rfl

theorem cell23_6963837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_6963837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963837 prefixEnd_6963837 := by exact prefixLift 6963837
  have htrace : WordTrace (prefixWord ++ tailWord_6963837) baseStart_6963837 baseEnd_6963837 := by
    simpa [prefixWord, tailWord_6963837, baseEnd_6963837] using wordTrace_append hprefix tailTrace_6963837
  have hstable : (prefixWord ++ tailWord_6963837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963837).length < 2 ^ (prefixWord ++ tailWord_6963837).sum := by decide
  have hdescent : baseEnd_6963837 < baseStart_6963837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963839 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 2, 7]
def baseStart_6963839 : Nat := 118140960795 + 6963839 * 2 ^ 59
def prefixEnd_6963839 : Nat := 4983230072969 + 3 ^ 40 * 6963839 * 2
def baseEnd_6963839 : Nat := 1191932202508494893862131

theorem tailTrace_6963839 : CollatzResearch.WordTrace tailWord_6963839 prefixEnd_6963839 1191932202508494893862131 := by
  unfold tailWord_6963839
  simp only [CollatzResearch.WordTrace]
  refine ⟨253992074618208106858990571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169328049745472071239327047 253992074618208106858990571)
  ·
    refine ⟨380988111927312160288485857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253992074618208106858990571 380988111927312160288485857)
    ·
      refine ⟨285741083945484120216364393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380988111927312160288485857 285741083945484120216364393)
      ·
        refine ⟨214305812959113090162273295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285741083945484120216364393 214305812959113090162273295)
        ·
          refine ⟨321458719438669635243409943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214305812959113090162273295 321458719438669635243409943)
          ·
            refine ⟨482188079158004452865114915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321458719438669635243409943 482188079158004452865114915)
            ·
              refine ⟨723282118737006679297672373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482188079158004452865114915 723282118737006679297672373)
              ·
                refine ⟨67807698631594376184156785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 723282118737006679297672373 67807698631594376184156785)
                ·
                  refine ⟨50855773973695782138117589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67807698631594376184156785 50855773973695782138117589)
                  ·
                    refine ⟨1191932202508494893862131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50855773973695782138117589 1191932202508494893862131)
                    ·
                      rfl

theorem cell23_6963839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_6963839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963839 prefixEnd_6963839 := by exact prefixLift 6963839
  have htrace : WordTrace (prefixWord ++ tailWord_6963839) baseStart_6963839 baseEnd_6963839 := by
    simpa [prefixWord, tailWord_6963839, baseEnd_6963839] using wordTrace_append hprefix tailTrace_6963839
  have hstable : (prefixWord ++ tailWord_6963839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963839).length < 2 ^ (prefixWord ++ tailWord_6963839).sum := by decide
  have hdescent : baseEnd_6963839 < baseStart_6963839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963850 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_6963850 : Nat := 118140960795 + 6963850 * 2 ^ 59
def prefixEnd_6963850 : Nat := 4983230072969 + 3 ^ 40 * 6963850 * 2
def baseEnd_6963850 : Nat := 3575802255812684138548843

theorem tailTrace_6963850 : CollatzResearch.WordTrace tailWord_6963850 prefixEnd_6963850 3575802255812684138548843 := by
  unfold tailWord_6963850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63498118955292063934410251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169328317214112170491760669 63498118955292063934410251)
  ·
    refine ⟨95247178432938095901615377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63498118955292063934410251 95247178432938095901615377)
    ·
      refine ⟨71435383824703571926211533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95247178432938095901615377 71435383824703571926211533)
      ·
        refine ⟨26788268934263839472329325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71435383824703571926211533 26788268934263839472329325)
        ·
          refine ⟨10045600850348939802123497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26788268934263839472329325 10045600850348939802123497)
          ·
            refine ⟨7534200637761704851592623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10045600850348939802123497 7534200637761704851592623)
            ·
              refine ⟨11301300956642557277388935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534200637761704851592623 11301300956642557277388935)
              ·
                refine ⟨16951951434963835916083403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11301300956642557277388935 16951951434963835916083403)
                ·
                  refine ⟨25427927152445753874125105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16951951434963835916083403 25427927152445753874125105)
                  ·
                    refine ⟨19070945364334315405593829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25427927152445753874125105 19070945364334315405593829)
                    ·
                      refine ⟨3575802255812684138548843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19070945364334315405593829 3575802255812684138548843)
                      ·
                        rfl

theorem cell23_6963850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_6963850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963850 prefixEnd_6963850 := by exact prefixLift 6963850
  have htrace : WordTrace (prefixWord ++ tailWord_6963850) baseStart_6963850 baseEnd_6963850 := by
    simpa [prefixWord, tailWord_6963850, baseEnd_6963850] using wordTrace_append hprefix tailTrace_6963850
  have hstable : (prefixWord ++ tailWord_6963850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963850).length < 2 ^ (prefixWord ++ tailWord_6963850).sum := by decide
  have hdescent : baseEnd_6963850 < baseStart_6963850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963860 : List Nat := [2, 4, 2, 2, 1, 3, 2, 7]
def baseStart_6963860 : Nat := 118140960795 + 6963860 * 2 ^ 59
def prefixEnd_6963860 : Nat := 4983230072969 + 3 ^ 40 * 6963860 * 2
def baseEnd_6963860 : Nat := 132437310763675151830511

theorem tailTrace_6963860 : CollatzResearch.WordTrace tailWord_6963860 prefixEnd_6963860 132437310763675151830511 := by
  unfold tailWord_6963860
  simp only [CollatzResearch.WordTrace]
  refine ⟨126996420275566013722752517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169328560367421351630336689 126996420275566013722752517)
  ·
    refine ⟨23811828801668627573016097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126996420275566013722752517 23811828801668627573016097)
    ·
      refine ⟨17858871601251470679762073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23811828801668627573016097 17858871601251470679762073)
      ·
        refine ⟨13394153700938603009821555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17858871601251470679762073 13394153700938603009821555)
        ·
          refine ⟨20091230551407904514732333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394153700938603009821555 20091230551407904514732333)
          ·
            refine ⟨7534211456777964193024625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20091230551407904514732333 7534211456777964193024625)
            ·
              refine ⟨5650658592583473144768469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7534211456777964193024625 5650658592583473144768469)
              ·
                refine ⟨132437310763675151830511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5650658592583473144768469 132437310763675151830511)
                ·
                  rfl

theorem cell23_6963860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 7].length) (baseStart_6963860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963860 prefixEnd_6963860 := by exact prefixLift 6963860
  have htrace : WordTrace (prefixWord ++ tailWord_6963860) baseStart_6963860 baseEnd_6963860 := by
    simpa [prefixWord, tailWord_6963860, baseEnd_6963860] using wordTrace_append hprefix tailTrace_6963860
  have hstable : (prefixWord ++ tailWord_6963860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963860).length < 2 ^ (prefixWord ++ tailWord_6963860).sum := by decide
  have hdescent : baseEnd_6963860 < baseStart_6963860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963870 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_6963870 : Nat := 118140960795 + 6963870 * 2 ^ 59
def prefixEnd_6963870 : Nat := 4983230072969 + 3 ^ 40 * 6963870 * 2
def baseEnd_6963870 : Nat := 3575812525425774060298751

theorem tailTrace_6963870 : CollatzResearch.WordTrace tailWord_6963870 prefixEnd_6963870 3575812525425774060298751 := by
  unfold tailWord_6963870
  simp only [CollatzResearch.WordTrace]
  refine ⟨31749150660136974894171133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169328803520730532768912709 31749150660136974894171133)
  ·
    refine ⟨11905931497551365585314175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31749150660136974894171133 11905931497551365585314175)
    ·
      refine ⟨17858897246327048377971263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11905931497551365585314175 17858897246327048377971263)
      ·
        refine ⟨26788345869490572566956895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17858897246327048377971263 26788345869490572566956895)
        ·
          refine ⟨40182518804235858850435343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26788345869490572566956895 40182518804235858850435343)
          ·
            refine ⟨60273778206353788275653015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40182518804235858850435343 60273778206353788275653015)
            ·
              refine ⟨90410667309530682413479523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60273778206353788275653015 90410667309530682413479523)
              ·
                refine ⟨135616000964296023620219285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90410667309530682413479523 135616000964296023620219285)
                ·
                  refine ⟨6357000045201376107197779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135616000964296023620219285 6357000045201376107197779)
                  ·
                    refine ⟨9535500067802064160796669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357000045201376107197779 9535500067802064160796669)
                    ·
                      refine ⟨3575812525425774060298751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535500067802064160796669 3575812525425774060298751)
                      ·
                        rfl

theorem cell23_6963870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_6963870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963870 prefixEnd_6963870 := by exact prefixLift 6963870
  have htrace : WordTrace (prefixWord ++ tailWord_6963870) baseStart_6963870 baseEnd_6963870 := by
    simpa [prefixWord, tailWord_6963870, baseEnd_6963870] using wordTrace_append hprefix tailTrace_6963870
  have hstable : (prefixWord ++ tailWord_6963870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963870).length < 2 ^ (prefixWord ++ tailWord_6963870).sum := by decide
  have hdescent : baseEnd_6963870 < baseStart_6963870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963944 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6963944 : Nat := 118140960795 + 6963944 * 2 ^ 59
def prefixEnd_6963944 : Nat := 4983230072969 + 3 ^ 40 * 6963944 * 2
def baseEnd_6963944 : Nat := 3575850522994206770773411

theorem tailTrace_6963944 : CollatzResearch.WordTrace tailWord_6963944 prefixEnd_6963944 3575850522994206770773411 := by
  unfold tailWord_6963944
  simp only [CollatzResearch.WordTrace]
  refine ⟨126997952141413854895781443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169330602855218473194375257 126997952141413854895781443)
  ·
    refine ⟨190496928212120782343672165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126997952141413854895781443 190496928212120782343672165)
    ·
      refine ⟨35718174039772646689438531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190496928212120782343672165 35718174039772646689438531)
      ·
        refine ⟨53577261059658970034157797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35718174039772646689438531 53577261059658970034157797)
        ·
          refine ⟨10045736448686056881404587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53577261059658970034157797 10045736448686056881404587)
          ·
            refine ⟨15068604673029085322106881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045736448686056881404587 15068604673029085322106881)
            ·
              refine ⟨11301453504771813991580161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15068604673029085322106881 11301453504771813991580161)
              ·
                refine ⟨8476090128578860493685121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11301453504771813991580161 8476090128578860493685121)
                ·
                  refine ⟨6357067596434145370263841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476090128578860493685121 6357067596434145370263841)
                  ·
                    refine ⟨4767800697325609027697881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357067596434145370263841 4767800697325609027697881)
                    ·
                      refine ⟨3575850522994206770773411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767800697325609027697881 3575850522994206770773411)
                      ·
                        rfl

theorem cell23_6963944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6963944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963944 prefixEnd_6963944 := by exact prefixLift 6963944
  have htrace : WordTrace (prefixWord ++ tailWord_6963944) baseStart_6963944 baseEnd_6963944 := by
    simpa [prefixWord, tailWord_6963944, baseEnd_6963944] using wordTrace_append hprefix tailTrace_6963944
  have hstable : (prefixWord ++ tailWord_6963944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963944).length < 2 ^ (prefixWord ++ tailWord_6963944).sum := by decide
  have hdescent : baseEnd_6963944 < baseStart_6963944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963946 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_6963946 : Nat := 118140960795 + 6963946 * 2 ^ 59
def prefixEnd_6963946 : Nat := 4983230072969 + 3 ^ 40 * 6963946 * 2
def baseEnd_6963946 : Nat := 1191950516651838587649467

theorem tailTrace_6963946 : CollatzResearch.WordTrace tailWord_6963946 prefixEnd_6963946 1191950516651838587649467 := by
  unfold tailWord_6963946
  simp only [CollatzResearch.WordTrace]
  refine ⟨63498994307205116033283923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169330651485880309422090461 63498994307205116033283923)
  ·
    refine ⟨95248491460807674049925885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63498994307205116033283923 95248491460807674049925885)
    ·
      refine ⟨35718184297802877768722207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95248491460807674049925885 35718184297802877768722207)
      ·
        refine ⟨53577276446704316653083311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35718184297802877768722207 53577276446704316653083311)
        ·
          refine ⟨80365914670056474979624967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53577276446704316653083311 80365914670056474979624967)
          ·
            refine ⟨120548872005084712469437451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80365914670056474979624967 120548872005084712469437451)
            ·
              refine ⟨180823308007627068704156177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120548872005084712469437451 180823308007627068704156177)
              ·
                refine ⟨135617481005720301528117133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180823308007627068704156177 135617481005720301528117133)
                ·
                  refine ⟨50856555377145113073043925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135617481005720301528117133 50856555377145113073043925)
                  ·
                    refine ⟨1191950516651838587649467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50856555377145113073043925 1191950516651838587649467)
                    ·
                      rfl

theorem cell23_6963946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_6963946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963946 prefixEnd_6963946 := by exact prefixLift 6963946
  have htrace : WordTrace (prefixWord ++ tailWord_6963946) baseStart_6963946 baseEnd_6963946 := by
    simpa [prefixWord, tailWord_6963946, baseEnd_6963946] using wordTrace_append hprefix tailTrace_6963946
  have hstable : (prefixWord ++ tailWord_6963946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963946).length < 2 ^ (prefixWord ++ tailWord_6963946).sum := by decide
  have hdescent : baseEnd_6963946 < baseStart_6963946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963950 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_6963950 : Nat := 118140960795 + 6963950 * 2 ^ 59
def prefixEnd_6963950 : Nat := 4983230072969 + 3 ^ 40 * 6963950 * 2
def baseEnd_6963950 : Nat := 397317067097570416366487

theorem tailTrace_6963950 : CollatzResearch.WordTrace tailWord_6963950 prefixEnd_6963950 397317067097570416366487 := by
  unfold tailWord_6963950
  simp only [CollatzResearch.WordTrace]
  refine ⟨31749515390100746602035163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169330748747203981877520869 31749515390100746602035163)
  ·
    refine ⟨47624273085151119903052745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31749515390100746602035163 47624273085151119903052745)
    ·
      refine ⟨35718204813863339927289559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47624273085151119903052745 35718204813863339927289559)
      ·
        refine ⟨53577307220795009890934339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35718204813863339927289559 53577307220795009890934339)
        ·
          refine ⟨80365960831192514836401509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53577307220795009890934339 80365960831192514836401509)
          ·
            refine ⟨15068617655848596531825283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80365960831192514836401509 15068617655848596531825283)
            ·
              refine ⟨22602926483772894797737925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15068617655848596531825283 22602926483772894797737925)
              ·
                refine ⟨4238048715707417774575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22602926483772894797737925 4238048715707417774575861)
                ·
                  refine ⟨397317067097570416366487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4238048715707417774575861 397317067097570416366487)
                  ·
                    rfl

theorem cell23_6963950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_6963950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963950 prefixEnd_6963950 := by exact prefixLift 6963950
  have htrace : WordTrace (prefixWord ++ tailWord_6963950) baseStart_6963950 baseEnd_6963950 := by
    simpa [prefixWord, tailWord_6963950, baseEnd_6963950] using wordTrace_append hprefix tailTrace_6963950
  have hstable : (prefixWord ++ tailWord_6963950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963950).length < 2 ^ (prefixWord ++ tailWord_6963950).sum := by decide
  have hdescent : baseEnd_6963950 < baseStart_6963950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963953 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 7, 2]
def baseStart_6963953 : Nat := 118140960795 + 6963953 * 2 ^ 59
def prefixEnd_6963953 : Nat := 4983230072969 + 3 ^ 40 * 6963953 * 2
def baseEnd_6963953 : Nat := 3575855144320097235560869

theorem tailTrace_6963953 : CollatzResearch.WordTrace tailWord_6963953 prefixEnd_6963953 3575855144320097235560869 := by
  unfold tailWord_6963953
  simp only [CollatzResearch.WordTrace]
  refine ⟨253996232539795104328640513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169330821693196736219093675 253996232539795104328640513)
  ·
    refine ⟨190497174404846328246480385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253996232539795104328640513 190497174404846328246480385)
    ·
      refine ⟨142872880803634746184860289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190497174404846328246480385 142872880803634746184860289)
      ·
        refine ⟨107154660602726059638645217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142872880803634746184860289 107154660602726059638645217)
        ·
          refine ⟨80365995452044544728983913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107154660602726059638645217 80365995452044544728983913)
          ·
            refine ⟨60274496589033408546737935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80365995452044544728983913 60274496589033408546737935)
            ·
              refine ⟨90411744883550112820106903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60274496589033408546737935 90411744883550112820106903)
              ·
                refine ⟨135617617325325169230160355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90411744883550112820106903 135617617325325169230160355)
                ·
                  refine ⟨203426425987987753845240533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135617617325325169230160355 203426425987987753845240533)
                  ·
                    refine ⟨4767806859093462980747825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 203426425987987753845240533 4767806859093462980747825)
                    ·
                      refine ⟨3575855144320097235560869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767806859093462980747825 3575855144320097235560869)
                      ·
                        rfl

theorem cell23_6963953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_6963953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963953 prefixEnd_6963953 := by exact prefixLift 6963953
  have htrace : WordTrace (prefixWord ++ tailWord_6963953) baseStart_6963953 baseEnd_6963953 := by
    simpa [prefixWord, tailWord_6963953, baseEnd_6963953] using wordTrace_append hprefix tailTrace_6963953
  have hstable : (prefixWord ++ tailWord_6963953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963953).length < 2 ^ (prefixWord ++ tailWord_6963953).sum := by decide
  have hdescent : baseEnd_6963953 < baseStart_6963953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6963983 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 6, 2]
def baseStart_6963983 : Nat := 118140960795 + 6963983 * 2 ^ 59
def prefixEnd_6963983 : Nat := 4983230072969 + 3 ^ 40 * 6963983 * 2
def baseEnd_6963983 : Nat := 3575870548739732118185731

theorem tailTrace_6963983 : CollatzResearch.WordTrace tailWord_6963983 prefixEnd_6963983 3575870548739732118185731 := by
  unfold tailWord_6963983
  simp only [CollatzResearch.WordTrace]
  refine ⟨253997326729686419452232603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169331551153124279634821735 253997326729686419452232603)
  ·
    refine ⟨380995990094529629178348905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253997326729686419452232603 380995990094529629178348905)
    ·
      refine ⟨285746992570897221883761679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380995990094529629178348905 285746992570897221883761679)
      ·
        refine ⟨428620488856345832825642519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285746992570897221883761679 428620488856345832825642519)
        ·
          refine ⟨642930733284518749238463779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428620488856345832825642519 642930733284518749238463779)
          ·
            refine ⟨964396099926778123857695669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642930733284518749238463779 964396099926778123857695669)
            ·
              refine ⟨90412134368135449111658969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 964396099926778123857695669 90412134368135449111658969)
              ·
                refine ⟨67809100776101586833744227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90412134368135449111658969 67809100776101586833744227)
                ·
                  refine ⟨101713651164152380250616341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67809100776101586833744227 101713651164152380250616341)
                  ·
                    refine ⟨4767827398319642824247641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101713651164152380250616341 4767827398319642824247641)
                    ·
                      refine ⟨3575870548739732118185731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767827398319642824247641 3575870548739732118185731)
                      ·
                        rfl

theorem cell23_6963983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6, 2].length) (baseStart_6963983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6963983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6963983 prefixEnd_6963983 := by exact prefixLift 6963983
  have htrace : WordTrace (prefixWord ++ tailWord_6963983) baseStart_6963983 baseEnd_6963983 := by
    simpa [prefixWord, tailWord_6963983, baseEnd_6963983] using wordTrace_append hprefix tailTrace_6963983
  have hstable : (prefixWord ++ tailWord_6963983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6963983).length < 2 ^ (prefixWord ++ tailWord_6963983).sum := by decide
  have hdescent : baseEnd_6963983 < baseStart_6963983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6963983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964000 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 2, 4, 2]
def baseStart_6964000 : Nat := 118140960795 + 6964000 * 2 ^ 59
def prefixEnd_6964000 : Nat := 4983230072969 + 3 ^ 40 * 6964000 * 2
def baseEnd_6964000 : Nat := 3575879277910858551673153

theorem tailTrace_6964000 : CollatzResearch.WordTrace tailWord_6964000 prefixEnd_6964000 3575879277910858551673153 := by
  unfold tailWord_6964000
  simp only [CollatzResearch.WordTrace]
  refine ⟨126998973385312415677800727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169331964513749887570400969 126998973385312415677800727)
  ·
    refine ⟨190498460077968623516701091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126998973385312415677800727 190498460077968623516701091)
    ·
      refine ⟨285747690116952935275051637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190498460077968623516701091 285747690116952935275051637)
      ·
        refine ⟨26788845948464337682036091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285747690116952935275051637 26788845948464337682036091)
        ·
          refine ⟨40183268922696506523054137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26788845948464337682036091 40183268922696506523054137)
          ·
            refine ⟨30137451692022379892290603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40183268922696506523054137 30137451692022379892290603)
            ·
              refine ⟨45206177538033569838435905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30137451692022379892290603 45206177538033569838435905)
              ·
                refine ⟨33904633153525177378826929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45206177538033569838435905 33904633153525177378826929)
                ·
                  refine ⟨25428474865143883034120197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33904633153525177378826929 25428474865143883034120197)
                  ·
                    refine ⟨4767839037214478068897537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25428474865143883034120197 4767839037214478068897537)
                    ·
                      refine ⟨3575879277910858551673153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4767839037214478068897537 3575879277910858551673153)
                      ·
                        rfl

theorem cell23_6964000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_6964000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964000 prefixEnd_6964000 := by exact prefixLift 6964000
  have htrace : WordTrace (prefixWord ++ tailWord_6964000) baseStart_6964000 baseEnd_6964000 := by
    simpa [prefixWord, tailWord_6964000, baseEnd_6964000] using wordTrace_append hprefix tailTrace_6964000
  have hstable : (prefixWord ++ tailWord_6964000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964000).length < 2 ^ (prefixWord ++ tailWord_6964000).sum := by decide
  have hdescent : baseEnd_6964000 < baseStart_6964000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964003 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 3]
def baseStart_6964003 : Nat := 118140960795 + 6964003 * 2 ^ 59
def prefixEnd_6964003 : Nat := 4983230072969 + 3 ^ 40 * 6964003 * 2
def baseEnd_6964003 : Nat := 3575880818352822039935639

theorem tailTrace_6964003 : CollatzResearch.WordTrace tailWord_6964003 prefixEnd_6964003 3575880818352822039935639 := by
  unfold tailWord_6964003
  simp only [CollatzResearch.WordTrace]
  refine ⟨253998056189613962867960663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169332037459742641911973775 253998056189613962867960663)
  ·
    refine ⟨380997084284420944301940995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253998056189613962867960663 380997084284420944301940995)
    ·
      refine ⟨571495626426631416452911493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380997084284420944301940995 571495626426631416452911493)
      ·
        refine ⟨107155429954993390584920905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 571495626426631416452911493 107155429954993390584920905)
        ·
          refine ⟨80366572466245042938690679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107155429954993390584920905 80366572466245042938690679)
          ·
            refine ⟨120549858699367564408036019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80366572466245042938690679 120549858699367564408036019)
            ·
              refine ⟨180824788049051346612054029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120549858699367564408036019 180824788049051346612054029)
              ·
                refine ⟨67809295518394254979520261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180824788049051346612054029 67809295518394254979520261)
                ·
                  refine ⟨12714242909698922808660049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67809295518394254979520261 12714242909698922808660049)
                  ·
                    refine ⟨9535682182274192106495037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12714242909698922808660049 9535682182274192106495037)
                    ·
                      refine ⟨3575880818352822039935639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535682182274192106495037 3575880818352822039935639)
                      ·
                        rfl

theorem cell23_6964003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_6964003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964003 prefixEnd_6964003 := by exact prefixLift 6964003
  have htrace : WordTrace (prefixWord ++ tailWord_6964003) baseStart_6964003 baseEnd_6964003 := by
    simpa [prefixWord, tailWord_6964003, baseEnd_6964003] using wordTrace_append hprefix tailTrace_6964003
  have hstable : (prefixWord ++ tailWord_6964003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964003).length < 2 ^ (prefixWord ++ tailWord_6964003).sum := by decide
  have hdescent : baseEnd_6964003 < baseStart_6964003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964044 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_6964044 : Nat := 118140960795 + 6964044 * 2 ^ 59
def prefixEnd_6964044 : Nat := 4983230072969 + 3 ^ 40 * 6964044 * 2
def baseEnd_6964044 : Nat := 1191967290353218793174317

theorem tailTrace_6964044 : CollatzResearch.WordTrace tailWord_6964044 prefixEnd_6964044 1191967290353218793174317 := by
  unfold tailWord_6964044
  simp only [CollatzResearch.WordTrace]
  refine ⟨126999775791232713435101593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169333034388310284580135457 126999775791232713435101593)
  ·
    refine ⟨95249831843424535076326195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126999775791232713435101593 95249831843424535076326195)
    ·
      refine ⟨142874747765136802614489293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95249831843424535076326195 142874747765136802614489293)
      ·
        refine ⟨53578030411926300980433485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142874747765136802614489293 53578030411926300980433485)
        ·
          refine ⟨20091761404472362867662557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53578030411926300980433485 20091761404472362867662557)
          ·
            refine ⟨7534410526677136075373459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20091761404472362867662557 7534410526677136075373459)
            ·
              refine ⟨11301615790015704113060189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534410526677136075373459 11301615790015704113060189)
              ·
                refine ⟨4238105921255889042397571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11301615790015704113060189 4238105921255889042397571)
                ·
                  refine ⟨6357158881883833563596357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238105921255889042397571 6357158881883833563596357)
                  ·
                    refine ⟨1191967290353218793174317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6357158881883833563596357 1191967290353218793174317)
                    ·
                      rfl

theorem cell23_6964044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_6964044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964044 prefixEnd_6964044 := by exact prefixLift 6964044
  have htrace : WordTrace (prefixWord ++ tailWord_6964044) baseStart_6964044 baseEnd_6964044 := by
    simpa [prefixWord, tailWord_6964044, baseEnd_6964044] using wordTrace_append hprefix tailTrace_6964044
  have hstable : (prefixWord ++ tailWord_6964044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964044).length < 2 ^ (prefixWord ++ tailWord_6964044).sum := by decide
  have hdescent : baseEnd_6964044 < baseStart_6964044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964067 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 3]
def baseStart_6964067 : Nat := 118140960795 + 6964067 * 2 ^ 59
def prefixEnd_6964067 : Nat := 4983230072969 + 3 ^ 40 * 6964067 * 2
def baseEnd_6964067 : Nat := 3575913681114709789535345

theorem tailTrace_6964067 : CollatzResearch.WordTrace tailWord_6964067 prefixEnd_6964067 3575913681114709789535345 := by
  unfold tailWord_6964067
  simp only [CollatzResearch.WordTrace]
  refine ⟨254000390461382101798290455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169333593640921401198860303 254000390461382101798290455)
  ·
    refine ⟨381000585692073152697435683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254000390461382101798290455 381000585692073152697435683)
    ·
      refine ⟨571500878538109729046153525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381000585692073152697435683 571500878538109729046153525)
      ·
        refine ⟨53578207362947787098076893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 571500878538109729046153525 53578207362947787098076893)
        ·
          refine ⟨20091827761105420161778835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53578207362947787098076893 20091827761105420161778835)
          ·
            refine ⟨30137741641658130242668253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20091827761105420161778835 30137741641658130242668253)
            ·
              refine ⟨11301653115621798841000595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30137741641658130242668253 11301653115621798841000595)
              ·
                refine ⟨16952479673432698261500893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11301653115621798841000595 16952479673432698261500893)
                ·
                  refine ⟨6357179877537261848062835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16952479673432698261500893 6357179877537261848062835)
                  ·
                    refine ⟨9535769816305892772094253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357179877537261848062835 9535769816305892772094253)
                    ·
                      refine ⟨3575913681114709789535345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535769816305892772094253 3575913681114709789535345)
                      ·
                        rfl

theorem cell23_6964067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_6964067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964067 prefixEnd_6964067 := by exact prefixLift 6964067
  have htrace : WordTrace (prefixWord ++ tailWord_6964067) baseStart_6964067 baseEnd_6964067 := by
    simpa [prefixWord, tailWord_6964067, baseEnd_6964067] using wordTrace_append hprefix tailTrace_6964067
  have hstable : (prefixWord ++ tailWord_6964067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964067).length < 2 ^ (prefixWord ++ tailWord_6964067).sum := by decide
  have hdescent : baseEnd_6964067 < baseStart_6964067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964093 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_6964093 : Nat := 118140960795 + 6964093 * 2 ^ 59
def prefixEnd_6964093 : Nat := 4983230072969 + 3 ^ 40 * 6964093 * 2
def baseEnd_6964093 : Nat := 3575927031611726687810225

theorem tailTrace_6964093 : CollatzResearch.WordTrace tailWord_6964093 prefixEnd_6964093 3575927031611726687810225 := by
  unfold tailWord_6964093
  simp only [CollatzResearch.WordTrace]
  refine ⟨254001338759287908238736933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169334225839525272159157955 254001338759287908238736933)
  ·
    refine ⟨47625251017366482794763175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254001338759287908238736933 47625251017366482794763175)
    ·
      refine ⟨71437876526049724192144763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47625251017366482794763175 71437876526049724192144763)
      ·
        refine ⟨107156814789074586288217145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71437876526049724192144763 107156814789074586288217145)
        ·
          refine ⟨80367611091805939716162859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107156814789074586288217145 80367611091805939716162859)
          ·
            refine ⟨120551416637708909574244289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80367611091805939716162859 120551416637708909574244289)
            ·
              refine ⟨90413562478281682180683217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120551416637708909574244289 90413562478281682180683217)
              ·
                refine ⟨67810171858711261635512413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90413562478281682180683217 67810171858711261635512413)
                ·
                  refine ⟨25428814447016723113317155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67810171858711261635512413 25428814447016723113317155)
                  ·
                    refine ⟨38143221670525084669975733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25428814447016723113317155 38143221670525084669975733)
                    ·
                      refine ⟨3575927031611726687810225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38143221670525084669975733 3575927031611726687810225)
                      ·
                        rfl

theorem cell23_6964093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_6964093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964093 prefixEnd_6964093 := by exact prefixLift 6964093
  have htrace : WordTrace (prefixWord ++ tailWord_6964093) baseStart_6964093 baseEnd_6964093 := by
    simpa [prefixWord, tailWord_6964093, baseEnd_6964093] using wordTrace_append hprefix tailTrace_6964093
  have hstable : (prefixWord ++ tailWord_6964093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964093).length < 2 ^ (prefixWord ++ tailWord_6964093).sum := by decide
  have hdescent : baseEnd_6964093 < baseStart_6964093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964117 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_6964117 : Nat := 118140960795 + 6964117 * 2 ^ 59
def prefixEnd_6964117 : Nat := 4983230072969 + 3 ^ 40 * 6964117 * 2
def baseEnd_6964117 : Nat := 1191979785049144864636705

theorem tailTrace_6964117 : CollatzResearch.WordTrace tailWord_6964117 prefixEnd_6964117 1191979785049144864636705 := by
  unfold tailWord_6964117
  simp only [CollatzResearch.WordTrace]
  refine ⟨254002214111200960337610605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169334809407467306891740403 254002214111200960337610605)
  ·
    refine ⟨95250830291700360126603977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254002214111200960337610605 95250830291700360126603977)
    ·
      refine ⟨71438122718775270094952983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95250830291700360126603977 71438122718775270094952983)
      ·
        refine ⟨107157184078162905142429475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71438122718775270094952983 107157184078162905142429475)
        ·
          refine ⟨160735776117244357713644213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107157184078162905142429475 160735776117244357713644213)
          ·
            refine ⟨15068979010991658535654145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160735776117244357713644213 15068979010991658535654145)
            ·
              refine ⟨11301734258243743901740609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15068979010991658535654145 11301734258243743901740609)
              ·
                refine ⟨8476300693682807926305457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11301734258243743901740609 8476300693682807926305457)
                ·
                  refine ⟨6357225520262105944729093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476300693682807926305457 6357225520262105944729093)
                  ·
                    refine ⟨1191979785049144864636705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6357225520262105944729093 1191979785049144864636705)
                    ·
                      rfl

theorem cell23_6964117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_6964117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964117 prefixEnd_6964117 := by exact prefixLift 6964117
  have htrace : WordTrace (prefixWord ++ tailWord_6964117) baseStart_6964117 baseEnd_6964117 := by
    simpa [prefixWord, tailWord_6964117, baseEnd_6964117] using wordTrace_append hprefix tailTrace_6964117
  have hstable : (prefixWord ++ tailWord_6964117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964117).length < 2 ^ (prefixWord ++ tailWord_6964117).sum := by decide
  have hdescent : baseEnd_6964117 < baseStart_6964117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964130 : List Nat := [3, 3, 1, 2, 2, 1, 3, 8]
def baseStart_6964130 : Nat := 118140960795 + 6964130 * 2 ^ 59
def prefixEnd_6964130 : Nat := 4983230072969 + 3 ^ 40 * 6964130 * 2
def baseEnd_6964130 : Nat := 132442445570220112705465

theorem tailTrace_6964130 : CollatzResearch.WordTrace tailWord_6964130 prefixEnd_6964130 132442445570220112705465 := by
  unfold tailWord_6964130
  simp only [CollatzResearch.WordTrace]
  refine ⟨63500672065038465889458461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169335125506769242371889229 63500672065038465889458461)
  ·
    refine ⟨23812752024389424708546923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63500672065038465889458461 23812752024389424708546923)
    ·
      refine ⟨35719128036584137062820385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23812752024389424708546923 35719128036584137062820385)
      ·
        refine ⟨26789346027438102797115289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35719128036584137062820385 26789346027438102797115289)
        ·
          refine ⟨20092009520578577097836467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26789346027438102797115289 20092009520578577097836467)
          ·
            refine ⟨30138014280867865646754701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20092009520578577097836467 30138014280867865646754701)
            ·
              refine ⟨11301755355325449617533013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30138014280867865646754701 11301755355325449617533013)
              ·
                refine ⟨132442445570220112705465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11301755355325449617533013 132442445570220112705465)
                ·
                  rfl

theorem cell23_6964130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_6964130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964130 prefixEnd_6964130 := by exact prefixLift 6964130
  have htrace : WordTrace (prefixWord ++ tailWord_6964130) baseStart_6964130 baseEnd_6964130 := by
    simpa [prefixWord, tailWord_6964130, baseEnd_6964130] using wordTrace_append hprefix tailTrace_6964130
  have hstable : (prefixWord ++ tailWord_6964130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964130).length < 2 ^ (prefixWord ++ tailWord_6964130).sum := by decide
  have hdescent : baseEnd_6964130 < baseStart_6964130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964163 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4]
def baseStart_6964163 : Nat := 118140960795 + 6964163 * 2 ^ 59
def prefixEnd_6964163 : Nat := 4983230072969 + 3 ^ 40 * 6964163 * 2
def baseEnd_6964163 : Nat := 3575962975257541413934903

theorem tailTrace_6964163 : CollatzResearch.WordTrace tailWord_6964163 prefixEnd_6964163 3575962975257541413934903 := by
  unfold tailWord_6964163
  simp only [CollatzResearch.WordTrace]
  refine ⟨254003891869034310193785143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169335927912689540129190095 254003891869034310193785143)
  ·
    refine ⟨381005837803551465290677715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254003891869034310193785143 381005837803551465290677715)
    ·
      refine ⟨571508756705327197936016573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381005837803551465290677715 571508756705327197936016573)
      ·
        refine ⟨214315783764497699226006215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571508756705327197936016573 214315783764497699226006215)
        ·
          refine ⟨321473675646746548839009323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214315783764497699226006215 321473675646746548839009323)
          ·
            refine ⟨482210513470119823258513985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321473675646746548839009323 482210513470119823258513985)
            ·
              refine ⟨361657885102589867443885489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482210513470119823258513985 361657885102589867443885489)
              ·
                refine ⟨271243413826942400582914117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361657885102589867443885489 271243413826942400582914117)
                ·
                  refine ⟨50858140092551700109296397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271243413826942400582914117 50858140092551700109296397)
                  ·
                    refine ⟨19071802534706887540986149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50858140092551700109296397 19071802534706887540986149)
                    ·
                      refine ⟨3575962975257541413934903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19071802534706887540986149 3575962975257541413934903)
                      ·
                        rfl

theorem cell23_6964163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_6964163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964163 prefixEnd_6964163 := by exact prefixLift 6964163
  have htrace : WordTrace (prefixWord ++ tailWord_6964163) baseStart_6964163 baseEnd_6964163 := by
    simpa [prefixWord, tailWord_6964163, baseEnd_6964163] using wordTrace_append hprefix tailTrace_6964163
  have hstable : (prefixWord ++ tailWord_6964163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964163).length < 2 ^ (prefixWord ++ tailWord_6964163).sum := by decide
  have hdescent : baseEnd_6964163 < baseStart_6964163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964174 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_6964174 : Nat := 118140960795 + 6964174 * 2 ^ 59
def prefixEnd_6964174 : Nat := 4983230072969 + 3 ^ 40 * 6964174 * 2
def baseEnd_6964174 : Nat := 3575968623544740870897353

theorem tailTrace_6964174 : CollatzResearch.WordTrace tailWord_6964174 prefixEnd_6964174 3575968623544740870897353 := by
  unfold tailWord_6964174
  simp only [CollatzResearch.WordTrace]
  refine ⟨31750536633999307384054447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169336195381329639381623717 31750536633999307384054447)
  ·
    refine ⟨47625804950998961076081671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31750536633999307384054447 47625804950998961076081671)
    ·
      refine ⟨71438707426498441614122507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47625804950998961076081671 71438707426498441614122507)
      ·
        refine ⟨107158061139747662421183761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71438707426498441614122507 107158061139747662421183761)
        ·
          refine ⟨80368545854810746815887821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107158061139747662421183761 80368545854810746815887821)
          ·
            refine ⟨30138204695554030055957933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80368545854810746815887821 30138204695554030055957933)
            ·
              refine ⟨11301826760832761270984225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30138204695554030055957933 11301826760832761270984225)
              ·
                refine ⟨8476370070624570953238169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11301826760832761270984225 8476370070624570953238169)
                ·
                  refine ⟨6357277552968428214928627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476370070624570953238169 6357277552968428214928627)
                  ·
                    refine ⟨9535916329452642322392941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357277552968428214928627 9535916329452642322392941)
                    ·
                      refine ⟨3575968623544740870897353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535916329452642322392941 3575968623544740870897353)
                      ·
                        rfl

theorem cell23_6964174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_6964174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964174 prefixEnd_6964174 := by exact prefixLift 6964174
  have htrace : WordTrace (prefixWord ++ tailWord_6964174) baseStart_6964174 baseEnd_6964174 := by
    simpa [prefixWord, tailWord_6964174, baseEnd_6964174] using wordTrace_append hprefix tailTrace_6964174
  have hstable : (prefixWord ++ tailWord_6964174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964174).length < 2 ^ (prefixWord ++ tailWord_6964174).sum := by decide
  have hdescent : baseEnd_6964174 < baseStart_6964174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964183 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_6964183 : Nat := 118140960795 + 6964183 * 2 ^ 59
def prefixEnd_6964183 : Nat := 4983230072969 + 3 ^ 40 * 6964183 * 2
def baseEnd_6964183 : Nat := 3575973244870631335684811

theorem tailTrace_6964183 : CollatzResearch.WordTrace tailWord_6964183 prefixEnd_6964183 3575973244870631335684811 := by
  unfold tailWord_6964183
  simp only [CollatzResearch.WordTrace]
  refine ⟨254004621328961853609513203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169336414219307902406342135 254004621328961853609513203)
  ·
    refine ⟨381006931993442780414269805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254004621328961853609513203 381006931993442780414269805)
    ·
      refine ⟨142877599497541042655351177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381006931993442780414269805 142877599497541042655351177)
      ·
        refine ⟨107158199623155781991513383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142877599497541042655351177 107158199623155781991513383)
        ·
          refine ⟨160737299434733672987270075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107158199623155781991513383 160737299434733672987270075)
          ·
            refine ⟨241105949152100509480905113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160737299434733672987270075 241105949152100509480905113)
            ·
              refine ⟨180829461864075382110678835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241105949152100509480905113 180829461864075382110678835)
              ·
                refine ⟨271244192796113073166018253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180829461864075382110678835 271244192796113073166018253)
                ·
                  refine ⟨101716572298542402437256845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271244192796113073166018253 101716572298542402437256845)
                  ·
                    refine ⟨38143714611953400913971317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101716572298542402437256845 38143714611953400913971317)
                    ·
                      refine ⟨3575973244870631335684811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38143714611953400913971317 3575973244870631335684811)
                      ·
                        rfl

theorem cell23_6964183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_6964183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964183 prefixEnd_6964183 := by exact prefixLift 6964183
  have htrace : WordTrace (prefixWord ++ tailWord_6964183) baseStart_6964183 baseEnd_6964183 := by
    simpa [prefixWord, tailWord_6964183, baseEnd_6964183] using wordTrace_append hprefix tailTrace_6964183
  have hstable : (prefixWord ++ tailWord_6964183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964183).length < 2 ^ (prefixWord ++ tailWord_6964183).sum := by decide
  have hdescent : baseEnd_6964183 < baseStart_6964183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964191 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 2, 1, 3]
def baseStart_6964191 : Nat := 118140960795 + 6964191 * 2 ^ 59
def prefixEnd_6964191 : Nat := 4983230072969 + 3 ^ 40 * 6964191 * 2
def baseEnd_6964191 : Nat := 3575977352715867304384775

theorem tailTrace_6964191 : CollatzResearch.WordTrace tailWord_6964191 prefixEnd_6964191 3575977352715867304384775 := by
  unfold tailWord_6964191
  simp only [CollatzResearch.WordTrace]
  refine ⟨254004913112932870975804427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169336608741955247317202951 254004913112932870975804427)
  ·
    refine ⟨381007369669399306463706641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254004913112932870975804427 381007369669399306463706641)
    ·
      refine ⟨285755527252049479847779981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381007369669399306463706641 285755527252049479847779981)
      ·
        refine ⟨107158322719518554942917493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285755527252049479847779981 107158322719518554942917493)
        ·
          refine ⟨10046092754954864525898515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107158322719518554942917493 10046092754954864525898515)
          ·
            refine ⟨15069139132432296788847773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10046092754954864525898515 15069139132432296788847773)
            ·
              refine ⟨5650927174662111295817915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15069139132432296788847773 5650927174662111295817915)
              ·
                refine ⟨8476390761993166943726873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650927174662111295817915 8476390761993166943726873)
                ·
                  refine ⟨6357293071494875207795155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476390761993166943726873 6357293071494875207795155)
                  ·
                    refine ⟨9535939607242312811692733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357293071494875207795155 9535939607242312811692733)
                    ·
                      refine ⟨3575977352715867304384775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535939607242312811692733 3575977352715867304384775)
                      ·
                        rfl

theorem cell23_6964191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_6964191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964191 prefixEnd_6964191 := by exact prefixLift 6964191
  have htrace : WordTrace (prefixWord ++ tailWord_6964191) baseStart_6964191 baseEnd_6964191 := by
    simpa [prefixWord, tailWord_6964191, baseEnd_6964191] using wordTrace_append hprefix tailTrace_6964191
  have hstable : (prefixWord ++ tailWord_6964191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964191).length < 2 ^ (prefixWord ++ tailWord_6964191).sum := by decide
  have hdescent : baseEnd_6964191 < baseStart_6964191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964200 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6964200 : Nat := 118140960795 + 6964200 * 2 ^ 59
def prefixEnd_6964200 : Nat := 4983230072969 + 3 ^ 40 * 6964200 * 2
def baseEnd_6964200 : Nat := 3575981974041757769172233

theorem tailTrace_6964200 : CollatzResearch.WordTrace tailWord_6964200 prefixEnd_6964200 3575981974041757769172233 := by
  unfold tailWord_6964200
  simp only [CollatzResearch.WordTrace]
  refine ⟨127002620684950132756441027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169336827579933510341921369 127002620684950132756441027)
  ·
    refine ⟨190503931027425199134661541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127002620684950132756441027 190503931027425199134661541)
    ·
      refine ⟨35719487067642224837749039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190503931027425199134661541 35719487067642224837749039)
      ·
        refine ⟨53579230601463337256623559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35719487067642224837749039 53579230601463337256623559)
        ·
          refine ⟨80368845902195005884935339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53579230601463337256623559 80368845902195005884935339)
          ·
            refine ⟨120553268853292508827403009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80368845902195005884935339 120553268853292508827403009)
            ·
              refine ⟨90414951639969381620552257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120553268853292508827403009 90414951639969381620552257)
              ·
                refine ⟨67811213729977036215414193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90414951639969381620552257 67811213729977036215414193)
                ·
                  refine ⟨50858410297482777161560645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67811213729977036215414193 50858410297482777161560645)
                  ·
                    refine ⟨9535951930778020717792621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50858410297482777161560645 9535951930778020717792621)
                    ·
                      refine ⟨3575981974041757769172233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9535951930778020717792621 3575981974041757769172233)
                      ·
                        rfl

theorem cell23_6964200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6964200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964200 prefixEnd_6964200 := by exact prefixLift 6964200
  have htrace : WordTrace (prefixWord ++ tailWord_6964200) baseStart_6964200 baseEnd_6964200 := by
    simpa [prefixWord, tailWord_6964200, baseEnd_6964200] using wordTrace_append hprefix tailTrace_6964200
  have hstable : (prefixWord ++ tailWord_6964200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964200).length < 2 ^ (prefixWord ++ tailWord_6964200).sum := by decide
  have hdescent : baseEnd_6964200 < baseStart_6964200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964223 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_6964223 : Nat := 118140960795 + 6964223 * 2 ^ 59
def prefixEnd_6964223 : Nat := 4983230072969 + 3 ^ 40 * 6964223 * 2
def baseEnd_6964223 : Nat := 3575993784096811179184627

theorem tailTrace_6964223 : CollatzResearch.WordTrace tailWord_6964223 prefixEnd_6964223 3575993784096811179184627 := by
  unfold tailWord_6964223
  simp only [CollatzResearch.WordTrace]
  refine ⟨254006080248816940440969323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169337386832544626960646215 254006080248816940440969323)
  ·
    refine ⟨381009120373225410661453985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254006080248816940440969323 381009120373225410661453985)
    ·
      refine ⟨285756840279919057996090489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381009120373225410661453985 285756840279919057996090489)
      ·
        refine ⟨214317630209939293497067867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285756840279919057996090489 214317630209939293497067867)
        ·
          refine ⟨321476445314908940245601801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214317630209939293497067867 321476445314908940245601801)
          ·
            refine ⟨241107333986181705184201351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321476445314908940245601801 241107333986181705184201351)
            ·
              refine ⟨361661000979272557776302027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241107333986181705184201351 361661000979272557776302027)
              ·
                refine ⟨542491501468908836664453041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361661000979272557776302027 542491501468908836664453041)
                ·
                  refine ⟨406868626101681627498339781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542491501468908836664453041 406868626101681627498339781)
                  ·
                    refine ⟨76287867394065305155938709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406868626101681627498339781 76287867394065305155938709)
                    ·
                      refine ⟨3575993784096811179184627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76287867394065305155938709 3575993784096811179184627)
                      ·
                        rfl

theorem cell23_6964223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_6964223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964223 prefixEnd_6964223 := by exact prefixLift 6964223
  have htrace : WordTrace (prefixWord ++ tailWord_6964223) baseStart_6964223 baseEnd_6964223 := by
    simpa [prefixWord, tailWord_6964223, baseEnd_6964223] using wordTrace_append hprefix tailTrace_6964223
  have hstable : (prefixWord ++ tailWord_6964223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964223).length < 2 ^ (prefixWord ++ tailWord_6964223).sum := by decide
  have hdescent : baseEnd_6964223 < baseStart_6964223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964242 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6964242 : Nat := 118140960795 + 6964242 * 2 ^ 59
def prefixEnd_6964242 : Nat := 4983230072969 + 3 ^ 40 * 6964242 * 2
def baseEnd_6964242 : Nat := 3576003540229246604847041

theorem tailTrace_6964242 : CollatzResearch.WordTrace tailWord_6964242 prefixEnd_6964242 3576003540229246604847041 := by
  unfold tailWord_6964242
  simp only [CollatzResearch.WordTrace]
  refine ⟨63501693308937026671477745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169337848823832071123940653 63501693308937026671477745)
  ·
    refine ⟨47626269981702770003608309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63501693308937026671477745 47626269981702770003608309)
    ·
      refine ⟨4464962810784634687838279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47626269981702770003608309 4464962810784634687838279)
      ·
        refine ⟨6697444216176952031757419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4464962810784634687838279 6697444216176952031757419)
        ·
          refine ⟨10046166324265428047636129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697444216176952031757419 10046166324265428047636129)
          ·
            refine ⟨7534624743199071035727097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046166324265428047636129 7534624743199071035727097)
            ·
              refine ⟨5650968557399303276795323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7534624743199071035727097 5650968557399303276795323)
              ·
                refine ⟨8476452836098954915192985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650968557399303276795323 8476452836098954915192985)
                ·
                  refine ⟨6357339627074216186394739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476452836098954915192985 6357339627074216186394739)
                  ·
                    refine ⟨9536009440611324279592109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357339627074216186394739 9536009440611324279592109)
                    ·
                      refine ⟨3576003540229246604847041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9536009440611324279592109 3576003540229246604847041)
                      ·
                        rfl

theorem cell23_6964242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6964242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964242 prefixEnd_6964242 := by exact prefixLift 6964242
  have htrace : WordTrace (prefixWord ++ tailWord_6964242) baseStart_6964242 baseEnd_6964242 := by
    simpa [prefixWord, tailWord_6964242, baseEnd_6964242] using wordTrace_append hprefix tailTrace_6964242
  have hstable : (prefixWord ++ tailWord_6964242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964242).length < 2 ^ (prefixWord ++ tailWord_6964242).sum := by decide
  have hdescent : baseEnd_6964242 < baseStart_6964242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964248 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 2, 2, 2]
def baseStart_6964248 : Nat := 118140960795 + 6964248 * 2 ^ 59
def prefixEnd_6964248 : Nat := 4983230072969 + 3 ^ 40 * 6964248 * 2
def baseEnd_6964248 : Nat := 3576006621113173581372013

theorem tailTrace_6964248 : CollatzResearch.WordTrace tailWord_6964248 prefixEnd_6964248 3576006621113173581372013 := by
  unfold tailWord_6964248
  simp only [CollatzResearch.WordTrace]
  refine ⟨127003496036863184855314699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169337994715817579807086265 127003496036863184855314699)
  ·
    refine ⟨190505244055294777282972049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127003496036863184855314699 190505244055294777282972049)
    ·
      refine ⟨142878933041471082962229037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190505244055294777282972049 142878933041471082962229037)
      ·
        refine ⟨53579599890551656110835889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142878933041471082962229037 53579599890551656110835889)
        ·
          refine ⟨40184699917913742083126917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53579599890551656110835889 40184699917913742083126917)
          ·
            refine ⟨7534631234608826640586297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40184699917913742083126917 7534631234608826640586297)
            ·
              refine ⟨5650973425956619980439723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7534631234608826640586297 5650973425956619980439723)
              ·
                refine ⟨8476460138934929970659585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650973425956619980439723 8476460138934929970659585)
                ·
                  refine ⟨6357345104201197477994689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476460138934929970659585 6357345104201197477994689)
                  ·
                    refine ⟨4768008828150898108496017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357345104201197477994689 4768008828150898108496017)
                    ·
                      refine ⟨3576006621113173581372013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768008828150898108496017 3576006621113173581372013)
                      ·
                        rfl

theorem cell23_6964248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_6964248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964248 prefixEnd_6964248 := by exact prefixLift 6964248
  have htrace : WordTrace (prefixWord ++ tailWord_6964248) baseStart_6964248 baseEnd_6964248 := by
    simpa [prefixWord, tailWord_6964248, baseEnd_6964248] using wordTrace_append hprefix tailTrace_6964248
  have hstable : (prefixWord ++ tailWord_6964248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964248).length < 2 ^ (prefixWord ++ tailWord_6964248).sum := by decide
  have hdescent : baseEnd_6964248 < baseStart_6964248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964250 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_6964250 : Nat := 118140960795 + 6964250 * 2 ^ 59
def prefixEnd_6964250 : Nat := 4983230072969 + 3 ^ 40 * 6964250 * 2
def baseEnd_6964250 : Nat := 1192002549358160857849001

theorem tailTrace_6964250 : CollatzResearch.WordTrace tailWord_6964250 prefixEnd_6964250 1192002549358160857849001 := by
  unfold tailWord_6964250
  simp only [CollatzResearch.WordTrace]
  refine ⟨63501766254929781013050551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169338043346479416034801469 63501766254929781013050551)
  ·
    refine ⟨95252649382394671519575827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63501766254929781013050551 95252649382394671519575827)
    ·
      refine ⟨142878974073592007279363741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95252649382394671519575827 142878974073592007279363741)
      ·
        refine ⟨53579615277597002729761403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142878974073592007279363741 53579615277597002729761403)
        ·
          refine ⟨80369422916395504094642105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53579615277597002729761403 80369422916395504094642105)
          ·
            refine ⟨60277067187296628070981579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80369422916395504094642105 60277067187296628070981579)
            ·
              refine ⟨90415600780944942106472369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60277067187296628070981579 90415600780944942106472369)
              ·
                refine ⟨67811700585708706579854277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90415600780944942106472369 67811700585708706579854277)
                ·
                  refine ⟨12714693859820382483722677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67811700585708706579854277 12714693859820382483722677)
                  ·
                    refine ⟨1192002549358160857849001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12714693859820382483722677 1192002549358160857849001)
                    ·
                      rfl

theorem cell23_6964250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_6964250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964250 prefixEnd_6964250 := by exact prefixLift 6964250
  have htrace : WordTrace (prefixWord ++ tailWord_6964250) baseStart_6964250 baseEnd_6964250 := by
    simpa [prefixWord, tailWord_6964250, baseEnd_6964250] using wordTrace_append hprefix tailTrace_6964250
  have hstable : (prefixWord ++ tailWord_6964250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964250).length < 2 ^ (prefixWord ++ tailWord_6964250).sum := by decide
  have hdescent : baseEnd_6964250 < baseStart_6964250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964287 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 2, 4, 2]
def baseStart_6964287 : Nat := 118140960795 + 6964287 * 2 ^ 59
def prefixEnd_6964287 : Nat := 4983230072969 + 3 ^ 40 * 6964287 * 2
def baseEnd_6964287 : Nat := 3576026646858698928784333

theorem tailTrace_6964287 : CollatzResearch.WordTrace tailWord_6964287 prefixEnd_6964287 3576026646858698928784333 := by
  unfold tailWord_6964287
  simp only [CollatzResearch.WordTrace]
  refine ⟨254008414520585079371299115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169338943013723386247532743 254008414520585079371299115)
  ·
    refine ⟨381012621780877619056948673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254008414520585079371299115 381012621780877619056948673)
    ·
      refine ⟨285759466335658214292711505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381012621780877619056948673 285759466335658214292711505)
      ·
        refine ⟨214319599751743660719533629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285759466335658214292711505 214319599751743660719533629)
        ·
          refine ⟨80369849906903872769825111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214319599751743660719533629 80369849906903872769825111)
          ·
            refine ⟨120554774860355809154737667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80369849906903872769825111 120554774860355809154737667)
            ·
              refine ⟨180832162290533713732106501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120554774860355809154737667 180832162290533713732106501)
              ·
                refine ⟨33906030429475071324769969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180832162290533713732106501 33906030429475071324769969)
                ·
                  refine ⟨25429522822106303493577477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33906030429475071324769969 25429522822106303493577477)
                  ·
                    refine ⟨4768035529144931905045777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25429522822106303493577477 4768035529144931905045777)
                    ·
                      refine ⟨3576026646858698928784333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768035529144931905045777 3576026646858698928784333)
                      ·
                        rfl

theorem cell23_6964287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_6964287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964287 prefixEnd_6964287 := by exact prefixLift 6964287
  have htrace : WordTrace (prefixWord ++ tailWord_6964287) baseStart_6964287 baseEnd_6964287 := by
    simpa [prefixWord, tailWord_6964287, baseEnd_6964287] using wordTrace_append hprefix tailTrace_6964287
  have hstable : (prefixWord ++ tailWord_6964287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964287).length < 2 ^ (prefixWord ++ tailWord_6964287).sum := by decide
  have hdescent : baseEnd_6964287 < baseStart_6964287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964294 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6964294 : Nat := 118140960795 + 6964294 * 2 ^ 59
def prefixEnd_6964294 : Nat := 4983230072969 + 3 ^ 40 * 6964294 * 2
def baseEnd_6964294 : Nat := 3576030241223280401396801

theorem tailTrace_6964294 : CollatzResearch.WordTrace tailWord_6964294 prefixEnd_6964294 3576030241223280401396801 := by
  unfold tailWord_6964294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937770932236241236462623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169339113221039813044535957 7937770932236241236462623)
  ·
    refine ⟨11906656398354361854693935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7937770932236241236462623 11906656398354361854693935)
    ·
      refine ⟨17859984597531542782040903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11906656398354361854693935 17859984597531542782040903)
      ·
        refine ⟨26789976896297314173061355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17859984597531542782040903 26789976896297314173061355)
        ·
          refine ⟨40184965344445971259592033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26789976896297314173061355 40184965344445971259592033)
          ·
            refine ⟨30138724008334478444694025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40184965344445971259592033 30138724008334478444694025)
            ·
              refine ⟨22604043006250858833520519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30138724008334478444694025 22604043006250858833520519)
              ·
                refine ⟨33906064509376288250280779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22604043006250858833520519 33906064509376288250280779)
                ·
                  refine ⟨50859096764064432375421169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33906064509376288250280779 50859096764064432375421169)
                  ·
                    refine ⟨38144322573048324281565877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50859096764064432375421169 38144322573048324281565877)
                    ·
                      refine ⟨3576030241223280401396801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38144322573048324281565877 3576030241223280401396801)
                      ·
                        rfl

theorem cell23_6964294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6964294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964294 prefixEnd_6964294 := by exact prefixLift 6964294
  have htrace : WordTrace (prefixWord ++ tailWord_6964294) baseStart_6964294 baseEnd_6964294 := by
    simpa [prefixWord, tailWord_6964294, baseEnd_6964294] using wordTrace_append hprefix tailTrace_6964294
  have hstable : (prefixWord ++ tailWord_6964294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964294).length < 2 ^ (prefixWord ++ tailWord_6964294).sum := by decide
  have hdescent : baseEnd_6964294 < baseStart_6964294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964300 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6964300 : Nat := 118140960795 + 6964300 * 2 ^ 59
def prefixEnd_6964300 : Nat := 4983230072969 + 3 ^ 40 * 6964300 * 2
def baseEnd_6964300 : Nat := 3576033322107207377921773

theorem tailTrace_6964300 : CollatzResearch.WordTrace tailWord_6964300 prefixEnd_6964300 3576033322107207377921773 := by
  unfold tailWord_6964300
  simp only [CollatzResearch.WordTrace]
  refine ⟨127004444334768991295761177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169339259113025321727681569 127004444334768991295761177)
  ·
    refine ⟨95253333251076743471820883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127004444334768991295761177 95253333251076743471820883)
    ·
      refine ⟨142879999876615115207731325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95253333251076743471820883 142879999876615115207731325)
      ·
        refine ⟨53579999953730668202899247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142879999876615115207731325 53579999953730668202899247)
        ·
          refine ⟨80369999930596002304348871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53579999953730668202899247 80369999930596002304348871)
          ·
            refine ⟨120554999895894003456523307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80369999930596002304348871 120554999895894003456523307)
            ·
              refine ⟨180832499843841005184784961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120554999895894003456523307 180832499843841005184784961)
              ·
                refine ⟨135624374882880753888588721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180832499843841005184784961 135624374882880753888588721)
                ·
                  refine ⟨101718281162160565416441541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135624374882880753888588721 101718281162160565416441541)
                  ·
                    refine ⟨19072177717905106015582789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101718281162160565416441541 19072177717905106015582789)
                    ·
                      refine ⟨3576033322107207377921773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19072177717905106015582789 3576033322107207377921773)
                      ·
                        rfl

theorem cell23_6964300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6964300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964300 prefixEnd_6964300 := by exact prefixLift 6964300
  have htrace : WordTrace (prefixWord ++ tailWord_6964300) baseStart_6964300 baseEnd_6964300 := by
    simpa [prefixWord, tailWord_6964300, baseEnd_6964300] using wordTrace_append hprefix tailTrace_6964300
  have hstable : (prefixWord ++ tailWord_6964300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964300).length < 2 ^ (prefixWord ++ tailWord_6964300).sum := by decide
  have hdescent : baseEnd_6964300 < baseStart_6964300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964318 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6964318 : Nat := 118140960795 + 6964318 * 2 ^ 59
def prefixEnd_6964318 : Nat := 4983230072969 + 3 ^ 40 * 6964318 * 2
def baseEnd_6964318 : Nat := 1192014188252996102498897

theorem tailTrace_6964318 : CollatzResearch.WordTrace tailWord_6964318 prefixEnd_6964318 1192014188252996102498897 := by
  unfold tailWord_6964318
  simp only [CollatzResearch.WordTrace]
  refine ⟨31751193147934096458209701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169339696788981847777118405 31751193147934096458209701)
  ·
    refine ⟨5953348715237643085914319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31751193147934096458209701 5953348715237643085914319)
    ·
      refine ⟨8930023072856464628871479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953348715237643085914319 8930023072856464628871479)
      ·
        refine ⟨13395034609284696943307219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8930023072856464628871479 13395034609284696943307219)
        ·
          refine ⟨20092551913927045414960829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13395034609284696943307219 20092551913927045414960829)
          ·
            refine ⟨7534706967722642030610311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20092551913927045414960829 7534706967722642030610311)
            ·
              refine ⟨11302060451583963045915467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534706967722642030610311 11302060451583963045915467)
              ·
                refine ⟨16953090677375944568873201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11302060451583963045915467 16953090677375944568873201)
                ·
                  refine ⟨12714818008031958426654901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16953090677375944568873201 12714818008031958426654901)
                  ·
                    refine ⟨1192014188252996102498897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12714818008031958426654901 1192014188252996102498897)
                    ·
                      rfl

theorem cell23_6964318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6964318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964318 prefixEnd_6964318 := by exact prefixLift 6964318
  have htrace : WordTrace (prefixWord ++ tailWord_6964318) baseStart_6964318 baseEnd_6964318 := by
    simpa [prefixWord, tailWord_6964318, baseEnd_6964318] using wordTrace_append hprefix tailTrace_6964318
  have hstable : (prefixWord ++ tailWord_6964318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964318).length < 2 ^ (prefixWord ++ tailWord_6964318).sum := by decide
  have hdescent : baseEnd_6964318 < baseStart_6964318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964388 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_6964388 : Nat := 118140960795 + 6964388 * 2 ^ 59
def prefixEnd_6964388 : Nat := 4983230072969 + 3 ^ 40 * 6964388 * 2
def baseEnd_6964388 : Nat := 3576078508404803033621369

theorem tailTrace_6964388 : CollatzResearch.WordTrace tailWord_6964388 prefixEnd_6964388 3576078508404803033621369 := by
  unfold tailWord_6964388
  simp only [CollatzResearch.WordTrace]
  refine ⟨127006049146609586810362909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169341398862146115747150545 127006049146609586810362909)
  ·
    refine ⟨47627268429978595053886091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127006049146609586810362909 47627268429978595053886091)
    ·
      refine ⟨71440902644967892580829137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47627268429978595053886091 71440902644967892580829137)
      ·
        refine ⟨53580676983725919435621853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71440902644967892580829137 53580676983725919435621853)
        ·
          refine ⟨20092753868897219788358195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53580676983725919435621853 20092753868897219788358195)
          ·
            refine ⟨30139130803345829682537293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20092753868897219788358195 30139130803345829682537293)
            ·
              refine ⟨11302174051254686130951485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30139130803345829682537293 11302174051254686130951485)
              ·
                refine ⟨4238315269220507299106807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11302174051254686130951485 4238315269220507299106807)
                ·
                  refine ⟨6357472903830760948660211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238315269220507299106807 6357472903830760948660211)
                  ·
                    refine ⟨9536209355746141422990317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357472903830760948660211 9536209355746141422990317)
                    ·
                      refine ⟨3576078508404803033621369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9536209355746141422990317 3576078508404803033621369)
                      ·
                        rfl

theorem cell23_6964388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_6964388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964388 prefixEnd_6964388 := by exact prefixLift 6964388
  have htrace : WordTrace (prefixWord ++ tailWord_6964388) baseStart_6964388 baseEnd_6964388 := by
    simpa [prefixWord, tailWord_6964388, baseEnd_6964388] using wordTrace_append hprefix tailTrace_6964388
  have hstable : (prefixWord ++ tailWord_6964388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964388).length < 2 ^ (prefixWord ++ tailWord_6964388).sum := by decide
  have hdescent : baseEnd_6964388 < baseStart_6964388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964414 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_6964414 : Nat := 118140960795 + 6964414 * 2 ^ 59
def prefixEnd_6964414 : Nat := 4983230072969 + 3 ^ 40 * 6964414 * 2
def baseEnd_6964414 : Nat := 3576091858901819931896249

theorem tailTrace_6964414 : CollatzResearch.WordTrace tailWord_6964414 prefixEnd_6964414 3576091858901819931896249 := by
  unfold tailWord_6964414
  simp only [CollatzResearch.WordTrace]
  refine ⟨31751630823890622507646537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169342031060749986707448197 31751630823890622507646537)
  ·
    refine ⟨23813723117917966880734903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31751630823890622507646537 23813723117917966880734903)
    ·
      refine ⟨35720584676876950321102355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23813723117917966880734903 35720584676876950321102355)
      ·
        refine ⟨53580877015315425481653533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35720584676876950321102355 53580877015315425481653533)
        ·
          refine ⟨20092828880743284555620075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53580877015315425481653533 20092828880743284555620075)
          ·
            refine ⟨30139243321114926833430113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20092828880743284555620075 30139243321114926833430113)
            ·
              refine ⟨22604432490836195125072585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30139243321114926833430113 22604432490836195125072585)
              ·
                refine ⟨16953324368127146343804439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22604432490836195125072585 16953324368127146343804439)
                ·
                  refine ⟨25429986552190719515706659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16953324368127146343804439 25429986552190719515706659)
                  ·
                    refine ⟨38144979828286079273559989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25429986552190719515706659 38144979828286079273559989)
                    ·
                      refine ⟨3576091858901819931896249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38144979828286079273559989 3576091858901819931896249)
                      ·
                        rfl

theorem cell23_6964414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_6964414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964414 prefixEnd_6964414 := by exact prefixLift 6964414
  have htrace : WordTrace (prefixWord ++ tailWord_6964414) baseStart_6964414 baseEnd_6964414 := by
    simpa [prefixWord, tailWord_6964414, baseEnd_6964414] using wordTrace_append hprefix tailTrace_6964414
  have hstable : (prefixWord ++ tailWord_6964414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964414).length < 2 ^ (prefixWord ++ tailWord_6964414).sum := by decide
  have hdescent : baseEnd_6964414 < baseStart_6964414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964467 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4]
def baseStart_6964467 : Nat := 118140960795 + 6964467 * 2 ^ 59
def prefixEnd_6964467 : Nat := 4983230072969 + 3 ^ 40 * 6964467 * 2
def baseEnd_6964467 : Nat := 3576119073376508224533505

theorem tailTrace_6964467 : CollatzResearch.WordTrace tailWord_6964467 prefixEnd_6964467 3576119073376508224533505 := by
  unfold tailWord_6964467
  simp only [CollatzResearch.WordTrace]
  refine ⟨254014979659932970112851655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169343319773288646741901103 254014979659932970112851655)
  ·
    refine ⟨381022469489899455169277483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254014979659932970112851655 381022469489899455169277483)
    ·
      refine ⟨571533704234849182753916225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381022469489899455169277483 571533704234849182753916225)
      ·
        refine ⟨428650278176136887065437169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571533704234849182753916225 428650278176136887065437169)
        ·
          refine ⟨321487708632102665299077877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428650278176136887065437169 321487708632102665299077877)
          ·
            refine ⟨30139472684259624871788551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321487708632102665299077877 30139472684259624871788551)
            ·
              refine ⟨45209209026389437307682827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30139472684259624871788551 45209209026389437307682827)
              ·
                refine ⟨67813813539584155961524241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45209209026389437307682827 67813813539584155961524241)
                ·
                  refine ⟨50860360154688116971143181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67813813539584155961524241 50860360154688116971143181)
                  ·
                    refine ⟨19072635058008043864178693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50860360154688116971143181 19072635058008043864178693)
                    ·
                      refine ⟨3576119073376508224533505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19072635058008043864178693 3576119073376508224533505)
                      ·
                        rfl

theorem cell23_6964467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_6964467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964467 prefixEnd_6964467 := by exact prefixLift 6964467
  have htrace : WordTrace (prefixWord ++ tailWord_6964467) baseStart_6964467 baseEnd_6964467 := by
    simpa [prefixWord, tailWord_6964467, baseEnd_6964467] using wordTrace_append hprefix tailTrace_6964467
  have hstable : (prefixWord ++ tailWord_6964467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964467).length < 2 ^ (prefixWord ++ tailWord_6964467).sum := by decide
  have hdescent : baseEnd_6964467 < baseStart_6964467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964478 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6964478 : Nat := 118140960795 + 6964478 * 2 ^ 59
def prefixEnd_6964478 : Nat := 4983230072969 + 3 ^ 40 * 6964478 * 2
def baseEnd_6964478 : Nat := 3576124721663707681495955

theorem tailTrace_6964478 : CollatzResearch.WordTrace tailWord_6964478 prefixEnd_6964478 3576124721663707681495955 := by
  unfold tailWord_6964478
  simp only [CollatzResearch.WordTrace]
  refine ⟨31751922607861639873937761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169343587241928745994334725 31751922607861639873937761)
  ·
    refine ⟨23813941955896229905453321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31751922607861639873937761 23813941955896229905453321)
    ·
      refine ⟨17860456466922172429089991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23813941955896229905453321 17860456466922172429089991)
      ·
        refine ⟨26790684700383258643634987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17860456466922172429089991 26790684700383258643634987)
        ·
          refine ⟨40186027050574887965452481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26790684700383258643634987 40186027050574887965452481)
          ·
            refine ⟨30139520287931165974089361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40186027050574887965452481 30139520287931165974089361)
            ·
              refine ⟨22604640215948374480567021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30139520287931165974089361 22604640215948374480567021)
              ·
                refine ⟨8476740080980640430212633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22604640215948374480567021 8476740080980640430212633)
                ·
                  refine ⟨6357555060735480322659475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476740080980640430212633 6357555060735480322659475)
                  ·
                    refine ⟨9536332591103220483989213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357555060735480322659475 9536332591103220483989213)
                    ·
                      refine ⟨3576124721663707681495955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9536332591103220483989213 3576124721663707681495955)
                      ·
                        rfl

theorem cell23_6964478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6964478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964478 prefixEnd_6964478 := by exact prefixLift 6964478
  have htrace : WordTrace (prefixWord ++ tailWord_6964478) baseStart_6964478 baseEnd_6964478 := by
    simpa [prefixWord, tailWord_6964478, baseEnd_6964478] using wordTrace_append hprefix tailTrace_6964478
  have hstable : (prefixWord ++ tailWord_6964478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964478).length < 2 ^ (prefixWord ++ tailWord_6964478).sum := by decide
  have hdescent : baseEnd_6964478 < baseStart_6964478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964497 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_6964497 : Nat := 118140960795 + 6964497 * 2 ^ 59
def prefixEnd_6964497 : Nat := 4983230072969 + 3 ^ 40 * 6964497 * 2
def baseEnd_6964497 : Nat := 3576134477796143107158367

theorem tailTrace_6964497 : CollatzResearch.WordTrace tailWord_6964497 prefixEnd_6964497 3576134477796143107158367 := by
  unfold tailWord_6964497
  simp only [CollatzResearch.WordTrace]
  refine ⟨254016073849824285236443745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169344049233216190157629163 254016073849824285236443745)
  ·
    refine ⟨190512055387368213927332809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254016073849824285236443745 190512055387368213927332809)
    ·
      refine ⟨142884041540526160445499607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190512055387368213927332809 142884041540526160445499607)
      ·
        refine ⟨214326062310789240668249411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142884041540526160445499607 214326062310789240668249411)
        ·
          refine ⟨321489093466183861002374117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214326062310789240668249411 321489093466183861002374117)
          ·
            refine ⟨60279205024909473937945147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321489093466183861002374117 60279205024909473937945147)
            ·
              refine ⟨90418807537364210906917721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60279205024909473937945147 90418807537364210906917721)
              ·
                refine ⟨67814105653023158180188291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90418807537364210906917721 67814105653023158180188291)
                ·
                  refine ⟨101721158479534737270282437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67814105653023158180188291 101721158479534737270282437)
                  ·
                    refine ⟨19072717214912763238177957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101721158479534737270282437 19072717214912763238177957)
                    ·
                      refine ⟨3576134477796143107158367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19072717214912763238177957 3576134477796143107158367)
                      ·
                        rfl

theorem cell23_6964497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_6964497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964497 prefixEnd_6964497 := by exact prefixLift 6964497
  have htrace : WordTrace (prefixWord ++ tailWord_6964497) baseStart_6964497 baseEnd_6964497 := by
    simpa [prefixWord, tailWord_6964497, baseEnd_6964497] using wordTrace_append hprefix tailTrace_6964497
  have hstable : (prefixWord ++ tailWord_6964497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964497).length < 2 ^ (prefixWord ++ tailWord_6964497).sum := by decide
  have hdescent : baseEnd_6964497 < baseStart_6964497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964501 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_6964501 : Nat := 118140960795 + 6964501 * 2 ^ 59
def prefixEnd_6964501 : Nat := 4983230072969 + 3 ^ 40 * 6964501 * 2
def baseEnd_6964501 : Nat := 3576136531718761091508349

theorem tailTrace_6964501 : CollatzResearch.WordTrace tailWord_6964501 prefixEnd_6964501 3576136531718761091508349 := by
  unfold tailWord_6964501
  simp only [CollatzResearch.WordTrace]
  refine ⟨254016219741809793919589357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169344146494539862613059571 254016219741809793919589357)
  ·
    refine ⟨95256082403178672719846009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254016219741809793919589357 95256082403178672719846009)
    ·
      refine ⟨71442061802384004539884507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95256082403178672719846009 71442061802384004539884507)
      ·
        refine ⟨107163092703576006809826761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71442061802384004539884507 107163092703576006809826761)
        ·
          refine ⟨80372319527682005107370071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107163092703576006809826761 80372319527682005107370071)
          ·
            refine ⟨120558479291523007661055107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80372319527682005107370071 120558479291523007661055107)
            ·
              refine ⟨180837718937284511491582661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120558479291523007661055107 180837718937284511491582661)
              ·
                refine ⟨33907072300740845904671749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180837718937284511491582661 33907072300740845904671749)
                ·
                  refine ⟨6357576056388908607125953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33907072300740845904671749 6357576056388908607125953)
                  ·
                    refine ⟨4768182042291681455344465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357576056388908607125953 4768182042291681455344465)
                    ·
                      refine ⟨3576136531718761091508349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768182042291681455344465 3576136531718761091508349)
                      ·
                        rfl

theorem cell23_6964501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_6964501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964501 prefixEnd_6964501 := by exact prefixLift 6964501
  have htrace : WordTrace (prefixWord ++ tailWord_6964501) baseStart_6964501 baseEnd_6964501 := by
    simpa [prefixWord, tailWord_6964501, baseEnd_6964501] using wordTrace_append hprefix tailTrace_6964501
  have hstable : (prefixWord ++ tailWord_6964501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964501).length < 2 ^ (prefixWord ++ tailWord_6964501).sum := by decide
  have hdescent : baseEnd_6964501 < baseStart_6964501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964547 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_6964547 : Nat := 118140960795 + 6964547 * 2 ^ 59
def prefixEnd_6964547 : Nat := 4983230072969 + 3 ^ 40 * 6964547 * 2
def baseEnd_6964547 : Nat := 3576160151828867911533137

theorem tailTrace_6964547 : CollatzResearch.WordTrace tailWord_6964547 prefixEnd_6964547 3576160151828867911533137 := by
  unfold tailWord_6964547
  simp only [CollatzResearch.WordTrace]
  refine ⟨254017897499643143775763895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169345264999762095850509263 254017897499643143775763895)
  ·
    refine ⟨381026846249464715663645843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254017897499643143775763895 381026846249464715663645843)
    ·
      refine ⟨571540269374197073495468765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381026846249464715663645843 571540269374197073495468765)
      ·
        refine ⟨214327601015323902560800787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571540269374197073495468765 214327601015323902560800787)
        ·
          refine ⟨321491401522985853841201181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214327601015323902560800787 321491401522985853841201181)
          ·
            refine ⟨120559275571119695190450443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321491401522985853841201181 120559275571119695190450443)
            ·
              refine ⟨180838913356679542785675665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120559275571119695190450443 180838913356679542785675665)
              ·
                refine ⟨135629185017509657089256749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180838913356679542785675665 135629185017509657089256749)
                ·
                  refine ⟨50860944381566121408471281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135629185017509657089256749 50860944381566121408471281)
                  ·
                    refine ⟨38145708286174591056353461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50860944381566121408471281 38145708286174591056353461)
                    ·
                      refine ⟨3576160151828867911533137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38145708286174591056353461 3576160151828867911533137)
                      ·
                        rfl

theorem cell23_6964547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_6964547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964547 prefixEnd_6964547 := by exact prefixLift 6964547
  have htrace : WordTrace (prefixWord ++ tailWord_6964547) baseStart_6964547 baseEnd_6964547 := by
    simpa [prefixWord, tailWord_6964547, baseEnd_6964547] using wordTrace_append hprefix tailTrace_6964547
  have hstable : (prefixWord ++ tailWord_6964547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964547).length < 2 ^ (prefixWord ++ tailWord_6964547).sum := by decide
  have hdescent : baseEnd_6964547 < baseStart_6964547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964564 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_6964564 : Nat := 118140960795 + 6964564 * 2 ^ 59
def prefixEnd_6964564 : Nat := 4983230072969 + 3 ^ 40 * 6964564 * 2
def baseEnd_6964564 : Nat := 3576168880999994345020559

theorem tailTrace_6964564 : CollatzResearch.WordTrace tailWord_6964564 prefixEnd_6964564 3576168880999994345020559 := by
  unfold tailWord_6964564
  simp only [CollatzResearch.WordTrace]
  refine ⟨127009258770290777839566373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169345678360387703786088497 127009258770290777839566373)
  ·
    refine ⟨23814236019429520844918695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127009258770290777839566373 23814236019429520844918695)
    ·
      refine ⟨35721354029144281267378043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23814236019429520844918695 35721354029144281267378043)
      ·
        refine ⟨53582031043716421901067065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35721354029144281267378043 53582031043716421901067065)
        ·
          refine ⟨40186523282787316425800299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53582031043716421901067065 40186523282787316425800299)
          ·
            refine ⟨60279784924180974638700449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40186523282787316425800299 60279784924180974638700449)
            ·
              refine ⟨45209838693135730979025337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60279784924180974638700449 45209838693135730979025337)
              ·
                refine ⟨33907379019851798234269003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45209838693135730979025337 33907379019851798234269003)
                ·
                  refine ⟨50861068529777697351403505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33907379019851798234269003 50861068529777697351403505)
                  ·
                    refine ⟨38145801397333273013552629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50861068529777697351403505 38145801397333273013552629)
                    ·
                      refine ⟨3576168880999994345020559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38145801397333273013552629 3576168880999994345020559)
                      ·
                        rfl

theorem cell23_6964564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_6964564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964564 prefixEnd_6964564 := by exact prefixLift 6964564
  have htrace : WordTrace (prefixWord ++ tailWord_6964564) baseStart_6964564 baseEnd_6964564 := by
    simpa [prefixWord, tailWord_6964564, baseEnd_6964564] using wordTrace_append hprefix tailTrace_6964564
  have hstable : (prefixWord ++ tailWord_6964564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964564).length < 2 ^ (prefixWord ++ tailWord_6964564).sum := by decide
  have hdescent : baseEnd_6964564 < baseStart_6964564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964607 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_6964607 : Nat := 118140960795 + 6964607 * 2 ^ 59
def prefixEnd_6964607 : Nat := 4983230072969 + 3 ^ 40 * 6964607 * 2
def baseEnd_6964607 : Nat := 3576190960668137676782861

theorem tailTrace_6964607 : CollatzResearch.WordTrace tailWord_6964607 prefixEnd_6964607 3576190960668137676782861 := by
  unfold tailWord_6964607
  simp only [CollatzResearch.WordTrace]
  refine ⟨254020085879425774022948075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169346723919617182681965383 254020085879425774022948075)
  ·
    refine ⟨381030128819138661034422113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254020085879425774022948075 381030128819138661034422113)
    ·
      refine ⟨285772596614353995775816585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381030128819138661034422113 285772596614353995775816585)
      ·
        refine ⟨214329447460765496831862439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285772596614353995775816585 214329447460765496831862439)
        ·
          refine ⟨321494171191148245247793659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214329447460765496831862439 321494171191148245247793659)
          ·
            refine ⟨482241256786722367871690489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321494171191148245247793659 482241256786722367871690489)
            ·
              refine ⟨361680942590041775903767867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482241256786722367871690489 361680942590041775903767867)
              ·
                refine ⟨542521413885062663855651801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361680942590041775903767867 542521413885062663855651801)
                ·
                  refine ⟨406891060413796997891738851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542521413885062663855651801 406891060413796997891738851)
                  ·
                    refine ⟨610336590620695496837608277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406891060413796997891738851 610336590620695496837608277)
                    ·
                      refine ⟨3576190960668137676782861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 610336590620695496837608277 3576190960668137676782861)
                      ·
                        rfl

theorem cell23_6964607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_6964607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964607 prefixEnd_6964607 := by exact prefixLift 6964607
  have htrace : WordTrace (prefixWord ++ tailWord_6964607) baseStart_6964607 baseEnd_6964607 := by
    simpa [prefixWord, tailWord_6964607, baseEnd_6964607] using wordTrace_append hprefix tailTrace_6964607
  have hstable : (prefixWord ++ tailWord_6964607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964607).length < 2 ^ (prefixWord ++ tailWord_6964607).sum := by decide
  have hdescent : baseEnd_6964607 < baseStart_6964607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964611 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 3]
def baseStart_6964611 : Nat := 118140960795 + 6964611 * 2 ^ 59
def prefixEnd_6964611 : Nat := 4983230072969 + 3 ^ 40 * 6964611 * 2
def baseEnd_6964611 : Nat := 3576193014590755661132843

theorem tailTrace_6964611 : CollatzResearch.WordTrace tailWord_6964611 prefixEnd_6964611 3576193014590755661132843 := by
  unfold tailWord_6964611
  simp only [CollatzResearch.WordTrace]
  refine ⟨254020231771411282706093687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169346821180940855137395791 254020231771411282706093687)
  ·
    refine ⟨381030347657116924059140531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254020231771411282706093687 381030347657116924059140531)
    ·
      refine ⟨571545521485675386088710797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381030347657116924059140531 571545521485675386088710797)
      ·
        refine ⟨214329570557128269783266549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571545521485675386088710797 214329570557128269783266549)
        ·
          refine ⟨20093397239730775292181239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214329570557128269783266549 20093397239730775292181239)
          ·
            refine ⟨30140095859596162938271859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20093397239730775292181239 30140095859596162938271859)
            ·
              refine ⟨45210143789394244407407789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30140095859596162938271859 45210143789394244407407789)
              ·
                refine ⟨16953803921022841652777921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45210143789394244407407789 16953803921022841652777921)
                ·
                  refine ⟨12715352940767131239583441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16953803921022841652777921 12715352940767131239583441)
                  ·
                    refine ⟨9536514705575348429687581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12715352940767131239583441 9536514705575348429687581)
                    ·
                      refine ⟨3576193014590755661132843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9536514705575348429687581 3576193014590755661132843)
                      ·
                        rfl

theorem cell23_6964611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_6964611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964611 prefixEnd_6964611 := by exact prefixLift 6964611
  have htrace : WordTrace (prefixWord ++ tailWord_6964611) baseStart_6964611 baseEnd_6964611 := by
    simpa [prefixWord, tailWord_6964611, baseEnd_6964611] using wordTrace_append hprefix tailTrace_6964611
  have hstable : (prefixWord ++ tailWord_6964611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964611).length < 2 ^ (prefixWord ++ tailWord_6964611).sum := by decide
  have hdescent : baseEnd_6964611 < baseStart_6964611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964628 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6964628 : Nat := 118140960795 + 6964628 * 2 ^ 59
def prefixEnd_6964628 : Nat := 4983230072969 + 3 ^ 40 * 6964628 * 2
def baseEnd_6964628 : Nat := 3576201743761882094620265

theorem tailTrace_6964628 : CollatzResearch.WordTrace tailWord_6964628 prefixEnd_6964628 3576201743761882094620265 := by
  unfold tailWord_6964628
  simp only [CollatzResearch.WordTrace]
  refine ⟨127010425906174847304731269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169347234541566463072975025 127010425906174847304731269)
  ·
    refine ⟨23814454857407783869637113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127010425906174847304731269 23814454857407783869637113)
    ·
      refine ⟨17860841143055837902227835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23814454857407783869637113 17860841143055837902227835)
      ·
        refine ⟨26791261714583756853341753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17860841143055837902227835 26791261714583756853341753)
        ·
          refine ⟨20093446285937817640006315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26791261714583756853341753 20093446285937817640006315)
          ·
            refine ⟨30140169428906726460009473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20093446285937817640006315 30140169428906726460009473)
            ·
              refine ⟨22605127071680044845007105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30140169428906726460009473 22605127071680044845007105)
              ·
                refine ⟨16953845303760033633755329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22605127071680044845007105 16953845303760033633755329)
                ·
                  refine ⟨12715383977820025225316497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16953845303760033633755329 12715383977820025225316497)
                  ·
                    refine ⟨9536537983365018918987373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12715383977820025225316497 9536537983365018918987373)
                    ·
                      refine ⟨3576201743761882094620265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9536537983365018918987373 3576201743761882094620265)
                      ·
                        rfl

theorem cell23_6964628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6964628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964628 prefixEnd_6964628 := by exact prefixLift 6964628
  have htrace : WordTrace (prefixWord ++ tailWord_6964628) baseStart_6964628 baseEnd_6964628 := by
    simpa [prefixWord, tailWord_6964628, baseEnd_6964628] using wordTrace_append hprefix tailTrace_6964628
  have hstable : (prefixWord ++ tailWord_6964628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964628).length < 2 ^ (prefixWord ++ tailWord_6964628).sum := by decide
  have hdescent : baseEnd_6964628 < baseStart_6964628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964634 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_6964634 : Nat := 118140960795 + 6964634 * 2 ^ 59
def prefixEnd_6964634 : Nat := 4983230072969 + 3 ^ 40 * 6964634 * 2
def baseEnd_6964634 : Nat := 3576204824645809071145237

theorem tailTrace_6964634 : CollatzResearch.WordTrace tailWord_6964634 prefixEnd_6964634 3576204824645809071145237 := by
  unfold tailWord_6964634
  simp only [CollatzResearch.WordTrace]
  refine ⟨63505267662581989408545239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169347380433551971756120637 63505267662581989408545239)
  ·
    refine ⟨95257901493872984112817859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63505267662581989408545239 95257901493872984112817859)
    ·
      refine ⟨142886852240809476169226789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95257901493872984112817859 142886852240809476169226789)
      ·
        refine ⟨26791284795151776781730023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142886852240809476169226789 26791284795151776781730023)
        ·
          refine ⟨40186927192727665172595035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26791284795151776781730023 40186927192727665172595035)
          ·
            refine ⟨60280390789091497758892553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40186927192727665172595035 60280390789091497758892553)
            ·
              refine ⟨45210293091818623319169415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60280390789091497758892553 45210293091818623319169415)
              ·
                refine ⟨67815439637727934978754123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45210293091818623319169415 67815439637727934978754123)
                ·
                  refine ⟨101723159456591902468131185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67815439637727934978754123 101723159456591902468131185)
                  ·
                    refine ⟨76292369592443926851098389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101723159456591902468131185 76292369592443926851098389)
                    ·
                      refine ⟨3576204824645809071145237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76292369592443926851098389 3576204824645809071145237)
                      ·
                        rfl

theorem cell23_6964634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_6964634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964634 prefixEnd_6964634 := by exact prefixLift 6964634
  have htrace : WordTrace (prefixWord ++ tailWord_6964634) baseStart_6964634 baseEnd_6964634 := by
    simpa [prefixWord, tailWord_6964634, baseEnd_6964634] using wordTrace_append hprefix tailTrace_6964634
  have hstable : (prefixWord ++ tailWord_6964634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964634).length < 2 ^ (prefixWord ++ tailWord_6964634).sum := by decide
  have hdescent : baseEnd_6964634 < baseStart_6964634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964661 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_6964661 : Nat := 118140960795 + 6964661 * 2 ^ 59
def prefixEnd_6964661 : Nat := 4983230072969 + 3 ^ 40 * 6964661 * 2
def baseEnd_6964661 : Nat := 1192072896207826821835871

theorem tailTrace_6964661 : CollatzResearch.WordTrace tailWord_6964661 prefixEnd_6964661 1192072896207826821835871 := by
  unfold tailWord_6964661
  simp only [CollatzResearch.WordTrace]
  refine ⟨254022055421230141245413837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169348036947486760830275891 254022055421230141245413837)
  ·
    refine ⟨95258270782961302967030189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254022055421230141245413837 95258270782961302967030189)
    ·
      refine ⟨35721851543610488612636321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95258270782961302967030189 35721851543610488612636321)
      ·
        refine ⟨26791388657707866459477241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35721851543610488612636321 26791388657707866459477241)
        ·
          refine ⟨20093541493280899844607931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26791388657707866459477241 20093541493280899844607931)
          ·
            refine ⟨30140312239921349766911897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20093541493280899844607931 30140312239921349766911897)
            ·
              refine ⟨22605234179941012325183923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30140312239921349766911897 22605234179941012325183923)
              ·
                refine ⟨33907851269911518487775885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22605234179941012325183923 33907851269911518487775885)
                ·
                  refine ⟨12715444226216819432915957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33907851269911518487775885 12715444226216819432915957)
                  ·
                    refine ⟨1192072896207826821835871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12715444226216819432915957 1192072896207826821835871)
                    ·
                      rfl

theorem cell23_6964661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_6964661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964661 prefixEnd_6964661 := by exact prefixLift 6964661
  have htrace : WordTrace (prefixWord ++ tailWord_6964661) baseStart_6964661 baseEnd_6964661 := by
    simpa [prefixWord, tailWord_6964661, baseEnd_6964661] using wordTrace_append hprefix tailTrace_6964661
  have hstable : (prefixWord ++ tailWord_6964661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964661).length < 2 ^ (prefixWord ++ tailWord_6964661).sum := by decide
  have hdescent : baseEnd_6964661 < baseStart_6964661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964701 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6964701 : Nat := 118140960795 + 6964701 * 2 ^ 59
def prefixEnd_6964701 : Nat := 4983230072969 + 3 ^ 40 * 6964701 * 2
def baseEnd_6964701 : Nat := 3576239227849660309007429

theorem tailTrace_6964701 : CollatzResearch.WordTrace tailWord_6964701 prefixEnd_6964701 3576239227849660309007429 := by
  unfold tailWord_6964701
  simp only [CollatzResearch.WordTrace]
  refine ⟨254023514341085228076869957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169349009560723485384579971 254023514341085228076869957)
  ·
    refine ⟨47629408938953480264413117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254023514341085228076869957 47629408938953480264413117)
    ·
      refine ⟨17861028352107555099154919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47629408938953480264413117 17861028352107555099154919)
      ·
        refine ⟨26791542528161332648732379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17861028352107555099154919 26791542528161332648732379)
        ·
          refine ⟨40187313792241998973098569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26791542528161332648732379 40187313792241998973098569)
          ·
            refine ⟨30140485344181499229823927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40187313792241998973098569 30140485344181499229823927)
            ·
              refine ⟨45210728016272248844735891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30140485344181499229823927 45210728016272248844735891)
              ·
                refine ⟨67816092024408373267103837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45210728016272248844735891 67816092024408373267103837)
                ·
                  refine ⟨25431034509153139975163939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67816092024408373267103837 25431034509153139975163939)
                  ·
                    refine ⟨38146551763729709962745909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25431034509153139975163939 38146551763729709962745909)
                    ·
                      refine ⟨3576239227849660309007429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38146551763729709962745909 3576239227849660309007429)
                      ·
                        rfl

theorem cell23_6964701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6964701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964701 prefixEnd_6964701 := by exact prefixLift 6964701
  have htrace : WordTrace (prefixWord ++ tailWord_6964701) baseStart_6964701 baseEnd_6964701 := by
    simpa [prefixWord, tailWord_6964701, baseEnd_6964701] using wordTrace_append hprefix tailTrace_6964701
  have hstable : (prefixWord ++ tailWord_6964701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964701).length < 2 ^ (prefixWord ++ tailWord_6964701).sum := by decide
  have hdescent : baseEnd_6964701 < baseStart_6964701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964711 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6964711 : Nat := 118140960795 + 6964711 * 2 ^ 59
def prefixEnd_6964711 : Nat := 4983230072969 + 3 ^ 40 * 6964711 * 2
def baseEnd_6964711 : Nat := 3576244362656205269882383

theorem tailTrace_6964711 : CollatzResearch.WordTrace tailWord_6964711 prefixEnd_6964711 3576244362656205269882383 := by
  unfold tailWord_6964711
  simp only [CollatzResearch.WordTrace]
  refine ⟨254023879071048999784733987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169349252714032666523155991 254023879071048999784733987)
  ·
    refine ⟨381035818606573499677100981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254023879071048999784733987 381035818606573499677100981)
    ·
      refine ⟨35722107994366265594728217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381035818606573499677100981 35722107994366265594728217)
      ·
        refine ⟨26791580995774699196046163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35722107994366265594728217 26791580995774699196046163)
        ·
          refine ⟨40187371493662048794069245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26791580995774699196046163 40187371493662048794069245)
          ·
            refine ⟨15070264310123268297775967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40187371493662048794069245 15070264310123268297775967)
            ·
              refine ⟨22605396465184902446663951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15070264310123268297775967 22605396465184902446663951)
              ·
                refine ⟨33908094697777353669995927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22605396465184902446663951 33908094697777353669995927)
                ·
                  refine ⟨50862142046666030504993891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33908094697777353669995927 50862142046666030504993891)
                  ·
                    refine ⟨76293213069999045757490837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50862142046666030504993891 76293213069999045757490837)
                    ·
                      refine ⟨3576244362656205269882383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76293213069999045757490837 3576244362656205269882383)
                      ·
                        rfl

theorem cell23_6964711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6964711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964711 prefixEnd_6964711 := by exact prefixLift 6964711
  have htrace : WordTrace (prefixWord ++ tailWord_6964711) baseStart_6964711 baseEnd_6964711 := by
    simpa [prefixWord, tailWord_6964711, baseEnd_6964711] using wordTrace_append hprefix tailTrace_6964711
  have hstable : (prefixWord ++ tailWord_6964711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964711).length < 2 ^ (prefixWord ++ tailWord_6964711).sum := by decide
  have hdescent : baseEnd_6964711 < baseStart_6964711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964721 : List Nat := [1, 2, 2, 2, 3, 2, 4, 7]
def baseStart_6964721 : Nat := 118140960795 + 6964721 * 2 ^ 59
def prefixEnd_6964721 : Nat := 4983230072969 + 3 ^ 40 * 6964721 * 2
def baseEnd_6964721 : Nat := 132453685091212971509531

theorem tailTrace_6964721 : CollatzResearch.WordTrace tailWord_6964721 prefixEnd_6964721 132453685091212971509531 := by
  unfold tailWord_6964721
  simp only [CollatzResearch.WordTrace]
  refine ⟨254024243801012771492598017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169349495867341847661732011 254024243801012771492598017)
  ·
    refine ⟨190518182850759578619448513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254024243801012771492598017 190518182850759578619448513)
    ·
      refine ⟨142888637138069683964586385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190518182850759578619448513 142888637138069683964586385)
      ·
        refine ⟨107166477853552262973439789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142888637138069683964586385 107166477853552262973439789)
        ·
          refine ⟨40187429195082098615039921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107166477853552262973439789 40187429195082098615039921)
          ·
            refine ⟨30140571896311573961279941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40187429195082098615039921 30140571896311573961279941)
            ·
              refine ⟨5651357230558420117739989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30140571896311573961279941 5651357230558420117739989)
              ·
                refine ⟨132453685091212971509531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5651357230558420117739989 132453685091212971509531)
                ·
                  rfl

theorem cell23_6964721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 7].length) (baseStart_6964721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964721 prefixEnd_6964721 := by exact prefixLift 6964721
  have htrace : WordTrace (prefixWord ++ tailWord_6964721) baseStart_6964721 baseEnd_6964721 := by
    simpa [prefixWord, tailWord_6964721, baseEnd_6964721] using wordTrace_append hprefix tailTrace_6964721
  have hstable : (prefixWord ++ tailWord_6964721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964721).length < 2 ^ (prefixWord ++ tailWord_6964721).sum := by decide
  have hdescent : baseEnd_6964721 < baseStart_6964721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964732 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_6964732 : Nat := 118140960795 + 6964732 * 2 ^ 59
def prefixEnd_6964732 : Nat := 4983230072969 + 3 ^ 40 * 6964732 * 2
def baseEnd_6964732 : Nat := 3576255145749949687719787

theorem tailTrace_6964732 : CollatzResearch.WordTrace tailWord_6964732 prefixEnd_6964732 3576255145749949687719787 := by
  unfold tailWord_6964732
  simp only [CollatzResearch.WordTrace]
  refine ⟨127012322501986460185624225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169349763335981946914165633 127012322501986460185624225)
  ·
    refine ⟨95259241876489845139218169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127012322501986460185624225 95259241876489845139218169)
    ·
      refine ⟨71444431407367383854413627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95259241876489845139218169 71444431407367383854413627)
      ·
        refine ⟨107166647111051075781620441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71444431407367383854413627 107166647111051075781620441)
        ·
          refine ⟨80374985333288306836215331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107166647111051075781620441 80374985333288306836215331)
          ·
            refine ⟨120562477999932460254322997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80374985333288306836215331 120562477999932460254322997)
            ·
              refine ⟨11302732312493668148842781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120562477999932460254322997 11302732312493668148842781)
              ·
                refine ⟨4238524617185125555816043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11302732312493668148842781 4238524617185125555816043)
                ·
                  refine ⟨6357786925777688333724065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238524617185125555816043 6357786925777688333724065)
                  ·
                    refine ⟨4768340194333266250293049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357786925777688333724065 4768340194333266250293049)
                    ·
                      refine ⟨3576255145749949687719787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768340194333266250293049 3576255145749949687719787)
                      ·
                        rfl

theorem cell23_6964732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_6964732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964732 prefixEnd_6964732 := by exact prefixLift 6964732
  have htrace : WordTrace (prefixWord ++ tailWord_6964732) baseStart_6964732 baseEnd_6964732 := by
    simpa [prefixWord, tailWord_6964732, baseEnd_6964732] using wordTrace_append hprefix tailTrace_6964732
  have hstable : (prefixWord ++ tailWord_6964732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964732).length < 2 ^ (prefixWord ++ tailWord_6964732).sum := by decide
  have hdescent : baseEnd_6964732 < baseStart_6964732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964738 : List Nat := [3, 4, 1, 2, 1, 3, 9]
def baseStart_6964738 : Nat := 118140960795 + 6964738 * 2 ^ 59
def prefixEnd_6964738 : Nat := 4983230072969 + 3 ^ 40 * 6964738 * 2
def baseEnd_6964738 : Nat := 44151336131282427953639

theorem tailTrace_6964738 : CollatzResearch.WordTrace tailWord_6964738 prefixEnd_6964738 44151336131282427953639 := by
  unfold tailWord_6964738
  simp only [CollatzResearch.WordTrace]
  refine ⟨63506215960487795848991717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169349909227967455597311245 63506215960487795848991717)
  ·
    refine ⟨11907415492591461721685947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63506215960487795848991717 11907415492591461721685947)
    ·
      refine ⟨17861123238887192582528921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11907415492591461721685947 17861123238887192582528921)
      ·
        refine ⟨13395842429165394436896691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17861123238887192582528921 13395842429165394436896691)
        ·
          refine ⟨20093763643748091655345037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13395842429165394436896691 20093763643748091655345037)
          ·
            refine ⟨7535161366405534370754389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20093763643748091655345037 7535161366405534370754389)
            ·
              refine ⟨44151336131282427953639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7535161366405534370754389 44151336131282427953639)
              ·
                rfl

theorem cell23_6964738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 9].length) (baseStart_6964738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964738 prefixEnd_6964738 := by exact prefixLift 6964738
  have htrace : WordTrace (prefixWord ++ tailWord_6964738) baseStart_6964738 baseEnd_6964738 := by
    simpa [prefixWord, tailWord_6964738, baseEnd_6964738] using wordTrace_append hprefix tailTrace_6964738
  have hstable : (prefixWord ++ tailWord_6964738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964738).length < 2 ^ (prefixWord ++ tailWord_6964738).sum := by decide
  have hdescent : baseEnd_6964738 < baseStart_6964738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964765 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_6964765 : Nat := 118140960795 + 6964765 * 2 ^ 59
def prefixEnd_6964765 : Nat := 4983230072969 + 3 ^ 40 * 6964765 * 2
def baseEnd_6964765 : Nat := 3576272090611548058607135

theorem tailTrace_6964765 : CollatzResearch.WordTrace tailWord_6964765 prefixEnd_6964765 3576272090611548058607135 := by
  unfold tailWord_6964765
  simp only [CollatzResearch.WordTrace]
  refine ⟨254025848612853367007199749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169350565741902244671466499 254025848612853367007199749)
  ·
    refine ⟨47629846614910006313849953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254025848612853367007199749 47629846614910006313849953)
    ·
      refine ⟨35722384961182504735387465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47629846614910006313849953 35722384961182504735387465)
      ·
        refine ⟨26791788720886878551540599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35722384961182504735387465 26791788720886878551540599)
        ·
          refine ⟨40187683081330317827310899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26791788720886878551540599 40187683081330317827310899)
          ·
            refine ⟨60281524621995476740966349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40187683081330317827310899 60281524621995476740966349)
            ·
              refine ⟨22605571733248303777862381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60281524621995476740966349 22605571733248303777862381)
              ·
                refine ⟨8477089399968113916698393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22605571733248303777862381 8477089399968113916698393)
                ·
                  refine ⟨6357817049976085437523795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477089399968113916698393 6357817049976085437523795)
                  ·
                    refine ⟨9536725574964128156285693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6357817049976085437523795 9536725574964128156285693)
                    ·
                      refine ⟨3576272090611548058607135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9536725574964128156285693 3576272090611548058607135)
                      ·
                        rfl

theorem cell23_6964765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_6964765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964765 prefixEnd_6964765 := by exact prefixLift 6964765
  have htrace : WordTrace (prefixWord ++ tailWord_6964765) baseStart_6964765 baseEnd_6964765 := by
    simpa [prefixWord, tailWord_6964765, baseEnd_6964765] using wordTrace_append hprefix tailTrace_6964765
  have hstable : (prefixWord ++ tailWord_6964765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964765).length < 2 ^ (prefixWord ++ tailWord_6964765).sum := by decide
  have hdescent : baseEnd_6964765 < baseStart_6964765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964766 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6964766 : Nat := 118140960795 + 6964766 * 2 ^ 59
def prefixEnd_6964766 : Nat := 4983230072969 + 3 ^ 40 * 6964766 * 2
def baseEnd_6964766 : Nat := 3576272604092202554694631

theorem tailTrace_6964766 : CollatzResearch.WordTrace tailWord_6964766 prefixEnd_6964766 3576272604092202554694631 := by
  unfold tailWord_6964766
  simp only [CollatzResearch.WordTrace]
  refine ⟨31753235635731218022248269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169350590057233162785324101 31753235635731218022248269)
  ·
    refine ⟨11907463363399206758343101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31753235635731218022248269 11907463363399206758343101)
    ·
      refine ⟨4465298761274702534378663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11907463363399206758343101 4465298761274702534378663)
      ·
        refine ⟨6697948141912053801567995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465298761274702534378663 6697948141912053801567995)
        ·
          refine ⟨10046922212868080702351993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697948141912053801567995 10046922212868080702351993)
          ·
            refine ⟨7535191659651060526763995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046922212868080702351993 7535191659651060526763995)
            ·
              refine ⟨11302787489476590790145993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535191659651060526763995 11302787489476590790145993)
              ·
                refine ⟨8477090617107443092609495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11302787489476590790145993 8477090617107443092609495)
                ·
                  refine ⟨12715635925661164638914243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8477090617107443092609495 12715635925661164638914243)
                  ·
                    refine ⟨19073453888491746958371365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12715635925661164638914243 19073453888491746958371365)
                    ·
                      refine ⟨3576272604092202554694631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19073453888491746958371365 3576272604092202554694631)
                      ·
                        rfl

theorem cell23_6964766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6964766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964766 prefixEnd_6964766 := by exact prefixLift 6964766
  have htrace : WordTrace (prefixWord ++ tailWord_6964766) baseStart_6964766 baseEnd_6964766 := by
    simpa [prefixWord, tailWord_6964766, baseEnd_6964766] using wordTrace_append hprefix tailTrace_6964766
  have hstable : (prefixWord ++ tailWord_6964766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964766).length < 2 ^ (prefixWord ++ tailWord_6964766).sum := by decide
  have hdescent : baseEnd_6964766 < baseStart_6964766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964791 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_6964791 : Nat := 118140960795 + 6964791 * 2 ^ 59
def prefixEnd_6964791 : Nat := 4983230072969 + 3 ^ 40 * 6964791 * 2
def baseEnd_6964791 : Nat := 3576285441108564956882015

theorem tailTrace_6964791 : CollatzResearch.WordTrace tailWord_6964791 prefixEnd_6964791 3576285441108564956882015 := by
  unfold tailWord_6964791
  simp only [CollatzResearch.WordTrace]
  refine ⟨254026796910759173447646227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169351197940506115631764151 254026796910759173447646227)
  ·
    refine ⟨381040195366138760171469341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254026796910759173447646227 381040195366138760171469341)
    ·
      refine ⟨142890073262302035064301003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381040195366138760171469341 142890073262302035064301003)
      ·
        refine ⟨214335109893453052596451505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142890073262302035064301003 214335109893453052596451505)
        ·
          refine ⟨160751332420089789447338629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214335109893453052596451505 160751332420089789447338629)
          ·
            refine ⟨30140874828766835521375993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160751332420089789447338629 30140874828766835521375993)
            ·
              refine ⟨22605656121575126641031995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30140874828766835521375993 22605656121575126641031995)
              ·
                refine ⟨33908484182362689961547993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22605656121575126641031995 33908484182362689961547993)
                ·
                  refine ⟨25431363136772017471160995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33908484182362689961547993 25431363136772017471160995)
                  ·
                    refine ⟨38147044705158026206741493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25431363136772017471160995 38147044705158026206741493)
                    ·
                      refine ⟨3576285441108564956882015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38147044705158026206741493 3576285441108564956882015)
                      ·
                        rfl

theorem cell23_6964791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_6964791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964791 prefixEnd_6964791 := by exact prefixLift 6964791
  have htrace : WordTrace (prefixWord ++ tailWord_6964791) baseStart_6964791 baseEnd_6964791 := by
    simpa [prefixWord, tailWord_6964791, baseEnd_6964791] using wordTrace_append hprefix tailTrace_6964791
  have hstable : (prefixWord ++ tailWord_6964791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964791).length < 2 ^ (prefixWord ++ tailWord_6964791).sum := by decide
  have hdescent : baseEnd_6964791 < baseStart_6964791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964792 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 1, 3, 2]
def baseStart_6964792 : Nat := 118140960795 + 6964792 * 2 ^ 59
def prefixEnd_6964792 : Nat := 4983230072969 + 3 ^ 40 * 6964792 * 2
def baseEnd_6964792 : Nat := 3576285954589219452969511

theorem tailTrace_6964792 : CollatzResearch.WordTrace tailWord_6964792 prefixEnd_6964792 3576285954589219452969511 := by
  unfold tailWord_6964792
  simp only [CollatzResearch.WordTrace]
  refine ⟨127013416691877775309216315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169351222255837033745621753 127013416691877775309216315)
  ·
    refine ⟨190520125037816662963824473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127013416691877775309216315 190520125037816662963824473)
    ·
      refine ⟨142890093778362497222868355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190520125037816662963824473 142890093778362497222868355)
      ·
        refine ⟨214335140667543745834302533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142890093778362497222868355 214335140667543745834302533)
        ·
          refine ⟨40187838875164452343931725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214335140667543745834302533 40187838875164452343931725)
          ·
            refine ⟨15070439578186669628974397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40187838875164452343931725 15070439578186669628974397)
            ·
              refine ⟨5651414841820001110865399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15070439578186669628974397 5651414841820001110865399)
              ·
                refine ⟨8477122262730001666298099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651414841820001110865399 8477122262730001666298099)
                ·
                  refine ⟨12715683394095002499447149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8477122262730001666298099 12715683394095002499447149)
                  ·
                    refine ⟨4768381272785625937292681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12715683394095002499447149 4768381272785625937292681)
                    ·
                      refine ⟨3576285954589219452969511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768381272785625937292681 3576285954589219452969511)
                      ·
                        rfl

theorem cell23_6964792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_6964792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964792 prefixEnd_6964792 := by exact prefixLift 6964792
  have htrace : WordTrace (prefixWord ++ tailWord_6964792) baseStart_6964792 baseEnd_6964792 := by
    simpa [prefixWord, tailWord_6964792, baseEnd_6964792] using wordTrace_append hprefix tailTrace_6964792
  have hstable : (prefixWord ++ tailWord_6964792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964792).length < 2 ^ (prefixWord ++ tailWord_6964792).sum := by decide
  have hdescent : baseEnd_6964792 < baseStart_6964792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964818 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_6964818 : Nat := 118140960795 + 6964818 * 2 ^ 59
def prefixEnd_6964818 : Nat := 4983230072969 + 3 ^ 40 * 6964818 * 2
def baseEnd_6964818 : Nat := 3576299305086236351244391

theorem tailTrace_6964818 : CollatzResearch.WordTrace tailWord_6964818 prefixEnd_6964818 3576299305086236351244391 := by
  unfold tailWord_6964818
  simp only [CollatzResearch.WordTrace]
  refine ⟨63506945420415339264719777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169351854454440904705919405 63506945420415339264719777)
  ·
    refine ⟨47630209065311504448539833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63506945420415339264719777 47630209065311504448539833)
    ·
      refine ⟨35722656798983628336404875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47630209065311504448539833 35722656798983628336404875)
      ·
        refine ⟨53583985198475442504607313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35722656798983628336404875 53583985198475442504607313)
        ·
          refine ⟨40187988898856581878455485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53583985198475442504607313 40187988898856581878455485)
          ·
            refine ⟨15070495837071218204420807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40187988898856581878455485 15070495837071218204420807)
            ·
              refine ⟨22605743755606827306631211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15070495837071218204420807 22605743755606827306631211)
              ·
                refine ⟨33908615633410240959946817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22605743755606827306631211 33908615633410240959946817)
                ·
                  refine ⟨25431461725057680719960113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33908615633410240959946817 25431461725057680719960113)
                  ·
                    refine ⟨19073596293793260539970085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25431461725057680719960113 19073596293793260539970085)
                    ·
                      refine ⟨3576299305086236351244391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19073596293793260539970085 3576299305086236351244391)
                      ·
                        rfl

theorem cell23_6964818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_6964818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964818 prefixEnd_6964818 := by exact prefixLift 6964818
  have htrace : WordTrace (prefixWord ++ tailWord_6964818) baseStart_6964818 baseEnd_6964818 := by
    simpa [prefixWord, tailWord_6964818, baseEnd_6964818] using wordTrace_append hprefix tailTrace_6964818
  have hstable : (prefixWord ++ tailWord_6964818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964818).length < 2 ^ (prefixWord ++ tailWord_6964818).sum := by decide
  have hdescent : baseEnd_6964818 < baseStart_6964818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964828 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 7]
def baseStart_6964828 : Nat := 118140960795 + 6964828 * 2 ^ 59
def prefixEnd_6964828 : Nat := 4983230072969 + 3 ^ 40 * 6964828 * 2
def baseEnd_6964828 : Nat := 397367159988086812457705

theorem tailTrace_6964828 : CollatzResearch.WordTrace tailWord_6964828 prefixEnd_6964828 397367159988086812457705 := by
  unfold tailWord_6964828
  simp only [CollatzResearch.WordTrace]
  refine ⟨127014073205812564383371569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169352097607750085844495425 127014073205812564383371569)
  ·
    refine ⟨95260554904359423287528677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127014073205812564383371569 95260554904359423287528677)
    ·
      refine ⟨17861354044567391866411627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95260554904359423287528677 17861354044567391866411627)
      ·
        refine ⟨26792031066851087799617441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17861354044567391866411627 26792031066851087799617441)
        ·
          refine ⟨20094023300138315849713081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26792031066851087799617441 20094023300138315849713081)
          ·
            refine ⟨15070517475103736887284811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20094023300138315849713081 15070517475103736887284811)
            ·
              refine ⟨22605776212655605330927217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15070517475103736887284811 22605776212655605330927217)
              ·
                refine ⟨16954332159491703998195413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22605776212655605330927217 16954332159491703998195413)
                ·
                  refine ⟨397367159988086812457705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16954332159491703998195413 397367159988086812457705)
                  ·
                    rfl

theorem cell23_6964828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_6964828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964828 prefixEnd_6964828 := by exact prefixLift 6964828
  have htrace : WordTrace (prefixWord ++ tailWord_6964828) baseStart_6964828 baseEnd_6964828 := by
    simpa [prefixWord, tailWord_6964828, baseEnd_6964828] using wordTrace_append hprefix tailTrace_6964828
  have hstable : (prefixWord ++ tailWord_6964828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964828).length < 2 ^ (prefixWord ++ tailWord_6964828).sum := by decide
  have hdescent : baseEnd_6964828 < baseStart_6964828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964878 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6964878 : Nat := 118140960795 + 6964878 * 2 ^ 59
def prefixEnd_6964878 : Nat := 4983230072969 + 3 ^ 40 * 6964878 * 2
def baseEnd_6964878 : Nat := 3576330113925506116494115

theorem tailTrace_6964878 : CollatzResearch.WordTrace tailWord_6964878 prefixEnd_6964878 3576330113925506116494115 := by
  unfold tailWord_6964878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31753746257680498413257911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169353313374295991537375525 31753746257680498413257911)
  ·
    refine ⟨47630619386520747619886867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31753746257680498413257911 47630619386520747619886867)
    ·
      refine ⟨71445929079781121429830301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47630619386520747619886867 71445929079781121429830301)
      ·
        refine ⟨26792223404917920536186363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71445929079781121429830301 26792223404917920536186363)
        ·
          refine ⟨40188335107376880804279545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26792223404917920536186363 40188335107376880804279545)
          ·
            refine ⟨30141251330532660603209659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40188335107376880804279545 30141251330532660603209659)
            ·
              refine ⟨45211876995798990904814489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30141251330532660603209659 45211876995798990904814489)
              ·
                refine ⟨33908907746849243178610867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45211876995798990904814489 33908907746849243178610867)
                ·
                  refine ⟨50863361620273864767916301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33908907746849243178610867 50863361620273864767916301)
                  ·
                    refine ⟨19073760607602699287968613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50863361620273864767916301 19073760607602699287968613)
                    ·
                      refine ⟨3576330113925506116494115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19073760607602699287968613 3576330113925506116494115)
                      ·
                        rfl

theorem cell23_6964878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6964878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964878 prefixEnd_6964878 := by exact prefixLift 6964878
  have htrace : WordTrace (prefixWord ++ tailWord_6964878) baseStart_6964878 baseEnd_6964878 := by
    simpa [prefixWord, tailWord_6964878, baseEnd_6964878] using wordTrace_append hprefix tailTrace_6964878
  have hstable : (prefixWord ++ tailWord_6964878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964878).length < 2 ^ (prefixWord ++ tailWord_6964878).sum := by decide
  have hdescent : baseEnd_6964878 < baseStart_6964878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964901 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 8]
def baseStart_6964901 : Nat := 118140960795 + 6964901 * 2 ^ 59
def prefixEnd_6964901 : Nat := 4983230072969 + 3 ^ 40 * 6964901 * 2
def baseEnd_6964901 : Nat := 397371324886728836278501

theorem tailTrace_6964901 : CollatzResearch.WordTrace tailWord_6964901 prefixEnd_6964901 397371324886728836278501 := by
  unfold tailWord_6964901
  simp only [CollatzResearch.WordTrace]
  refine ⟨254030808940360662234150557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169353872626907108156100371 254030808940360662234150557)
  ·
    refine ⟨95261553352635248337806459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254030808940360662234150557 95261553352635248337806459)
    ·
      refine ⟨142892330028952872506709689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95261553352635248337806459 142892330028952872506709689)
      ·
        refine ⟨107169247521714654380032267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142892330028952872506709689 107169247521714654380032267)
        ·
          refine ⟨160753871282571981570048401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107169247521714654380032267 160753871282571981570048401)
          ·
            refine ⟨120565403461928986177536301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160753871282571981570048401 120565403461928986177536301)
            ·
              refine ⟨45212026298223369816576113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120565403461928986177536301 45212026298223369816576113)
              ·
                refine ⟨33909019723667527362432085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45212026298223369816576113 33909019723667527362432085)
                ·
                  refine ⟨397371324886728836278501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33909019723667527362432085 397371324886728836278501)
                  ·
                    rfl

theorem cell23_6964901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_6964901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964901 prefixEnd_6964901 := by exact prefixLift 6964901
  have htrace : WordTrace (prefixWord ++ tailWord_6964901) baseStart_6964901 baseEnd_6964901 := by
    simpa [prefixWord, tailWord_6964901, baseEnd_6964901] using wordTrace_append hprefix tailTrace_6964901
  have hstable : (prefixWord ++ tailWord_6964901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964901).length < 2 ^ (prefixWord ++ tailWord_6964901).sum := by decide
  have hdescent : baseEnd_6964901 < baseStart_6964901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964921 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6964921 : Nat := 118140960795 + 6964921 * 2 ^ 59
def prefixEnd_6964921 : Nat := 4983230072969 + 3 ^ 40 * 6964921 * 2
def baseEnd_6964921 : Nat := 3576352193593649448256417

theorem tailTrace_6964921 : CollatzResearch.WordTrace tailWord_6964921 prefixEnd_6964921 3576352193593649448256417 := by
  unfold tailWord_6964921
  simp only [CollatzResearch.WordTrace]
  refine ⟨254031538400288205649878617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169354358933525470433252411 254031538400288205649878617)
  ·
    refine ⟨190523653800216154237408963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254031538400288205649878617 190523653800216154237408963)
    ·
      refine ⟨285785480700324231356113445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190523653800216154237408963 285785480700324231356113445)
      ·
        refine ⟨53584777631310793379271271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285785480700324231356113445 53584777631310793379271271)
        ·
          refine ⟨80377166446966190068906907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53584777631310793379271271 80377166446966190068906907)
          ·
            refine ⟨120565749670449285103360361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80377166446966190068906907 120565749670449285103360361)
            ·
              refine ⟨90424312252836963827520271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120565749670449285103360361 90424312252836963827520271)
              ·
                refine ⟨135636468379255445741280407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90424312252836963827520271 135636468379255445741280407)
                ·
                  refine ⟨203454702568883168611920611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135636468379255445741280407 203454702568883168611920611)
                  ·
                    refine ⟨305182053853324752917880917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203454702568883168611920611 305182053853324752917880917)
                    ·
                      refine ⟨3576352193593649448256417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 305182053853324752917880917 3576352193593649448256417)
                      ·
                        rfl

theorem cell23_6964921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6964921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964921 prefixEnd_6964921 := by exact prefixLift 6964921
  have htrace : WordTrace (prefixWord ++ tailWord_6964921) baseStart_6964921 baseEnd_6964921 := by
    simpa [prefixWord, tailWord_6964921, baseEnd_6964921] using wordTrace_append hprefix tailTrace_6964921
  have hstable : (prefixWord ++ tailWord_6964921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964921).length < 2 ^ (prefixWord ++ tailWord_6964921).sum := by decide
  have hdescent : baseEnd_6964921 < baseStart_6964921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964978 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_6964978 : Nat := 118140960795 + 6964978 * 2 ^ 59
def prefixEnd_6964978 : Nat := 4983230072969 + 3 ^ 40 * 6964978 * 2
def baseEnd_6964978 : Nat := 1192127153996985241747885

theorem tailTrace_6964978 : CollatzResearch.WordTrace tailWord_6964978 prefixEnd_6964978 1192127153996985241747885 := by
  unfold tailWord_6964978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63508404340270426096175897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169355744907387802923135725 63508404340270426096175897)
  ·
    refine ⟨47631303255202819572131923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63508404340270426096175897 47631303255202819572131923)
    ·
      refine ⟨71446954882804229358197885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47631303255202819572131923 71446954882804229358197885)
      ·
        refine ⟨26792608081051586009324207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71446954882804229358197885 26792608081051586009324207)
        ·
          refine ⟨40188912121577379013986311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26792608081051586009324207 40188912121577379013986311)
          ·
            refine ⟨60283368182366068520979467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40188912121577379013986311 60283368182366068520979467)
            ·
              refine ⟨90425052273549102781469201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60283368182366068520979467 90425052273549102781469201)
              ·
                refine ⟨67818789205161827086101901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90425052273549102781469201 67818789205161827086101901)
                ·
                  refine ⟨25432045951935685157288213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67818789205161827086101901 25432045951935685157288213)
                  ·
                    refine ⟨1192127153996985241747885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25432045951935685157288213 1192127153996985241747885)
                    ·
                      rfl

theorem cell23_6964978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_6964978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964978 prefixEnd_6964978 := by exact prefixLift 6964978
  have htrace : WordTrace (prefixWord ++ tailWord_6964978) baseStart_6964978 baseEnd_6964978 := by
    simpa [prefixWord, tailWord_6964978, baseEnd_6964978] using wordTrace_append hprefix tailTrace_6964978
  have hstable : (prefixWord ++ tailWord_6964978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964978).length < 2 ^ (prefixWord ++ tailWord_6964978).sum := by decide
  have hdescent : baseEnd_6964978 < baseStart_6964978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964979 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 1, 1, 3]
def baseStart_6964979 : Nat := 118140960795 + 6964979 * 2 ^ 59
def prefixEnd_6964979 : Nat := 4983230072969 + 3 ^ 40 * 6964979 * 2
def baseEnd_6964979 : Nat := 3576381975471610221331151

theorem tailTrace_6964979 : CollatzResearch.WordTrace tailWord_6964979 prefixEnd_6964979 3576381975471610221331151 := by
  unfold tailWord_6964979
  simp only [CollatzResearch.WordTrace]
  refine ⟨254033653834078081555489991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169355769222718721036993327 254033653834078081555489991)
  ·
    refine ⟨381050480751117122333234987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254033653834078081555489991 381050480751117122333234987)
    ·
      refine ⟨571575721126675683499852481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381050480751117122333234987 571575721126675683499852481)
      ·
        refine ⟨428681790845006762624889361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571575721126675683499852481 428681790845006762624889361)
        ·
          refine ⟨321511343133755071968667021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428681790845006762624889361 321511343133755071968667021)
          ·
            refine ⟨120566753675158151988250133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321511343133755071968667021 120566753675158151988250133)
            ·
              refine ⟨5651566578523038374449225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120566753675158151988250133 5651566578523038374449225)
              ·
                refine ⟨4238674933892278780836919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5651566578523038374449225 4238674933892278780836919)
                ·
                  refine ⟨6358012400838418171255379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238674933892278780836919 6358012400838418171255379)
                  ·
                    refine ⟨9537018601257627256883069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358012400838418171255379 9537018601257627256883069)
                    ·
                      refine ⟨3576381975471610221331151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9537018601257627256883069 3576381975471610221331151)
                      ·
                        rfl

theorem cell23_6964979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 1, 3].length) (baseStart_6964979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964979 prefixEnd_6964979 := by exact prefixLift 6964979
  have htrace : WordTrace (prefixWord ++ tailWord_6964979) baseStart_6964979 baseEnd_6964979 := by
    simpa [prefixWord, tailWord_6964979, baseEnd_6964979] using wordTrace_append hprefix tailTrace_6964979
  have hstable : (prefixWord ++ tailWord_6964979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964979).length < 2 ^ (prefixWord ++ tailWord_6964979).sum := by decide
  have hdescent : baseEnd_6964979 < baseStart_6964979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964988 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_6964988 : Nat := 118140960795 + 6964988 * 2 ^ 59
def prefixEnd_6964988 : Nat := 4983230072969 + 3 ^ 40 * 6964988 * 2
def baseEnd_6964988 : Nat := 3576386596797500686118609

theorem tailTrace_6964988 : CollatzResearch.WordTrace tailWord_6964988 prefixEnd_6964988 3576386596797500686118609 := by
  unfold tailWord_6964988
  simp only [CollatzResearch.WordTrace]
  refine ⟨127016991045522738046283809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169355988060696984061711745 127016991045522738046283809)
  ·
    refine ⟨95262743284142053534712857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127016991045522738046283809 95262743284142053534712857)
    ·
      refine ⟨71447057463106540151034643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95262743284142053534712857 71447057463106540151034643)
      ·
        refine ⟨107170586194659810226551965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71447057463106540151034643 107170586194659810226551965)
        ·
          refine ⟨40188969822997428834956987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107170586194659810226551965 40188969822997428834956987)
          ·
            refine ⟨60283454734496143252435481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40188969822997428834956987 60283454734496143252435481)
            ·
              refine ⟨45212591050872107439326611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60283454734496143252435481 45212591050872107439326611)
              ·
                refine ⟨67818886576308161158989917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45212591050872107439326611 67818886576308161158989917)
                ·
                  refine ⟨25432082466115560434621219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67818886576308161158989917 25432082466115560434621219)
                  ·
                    refine ⟨38148123699173340651931829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25432082466115560434621219 38148123699173340651931829)
                    ·
                      refine ⟨3576386596797500686118609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38148123699173340651931829 3576386596797500686118609)
                      ·
                        rfl

theorem cell23_6964988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_6964988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964988 prefixEnd_6964988 := by exact prefixLift 6964988
  have htrace : WordTrace (prefixWord ++ tailWord_6964988) baseStart_6964988 baseEnd_6964988 := by
    simpa [prefixWord, tailWord_6964988, baseEnd_6964988] using wordTrace_append hprefix tailTrace_6964988
  have hstable : (prefixWord ++ tailWord_6964988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964988).length < 2 ^ (prefixWord ++ tailWord_6964988).sum := by decide
  have hdescent : baseEnd_6964988 < baseStart_6964988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6964995 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 2, 4]
def baseStart_6964995 : Nat := 118140960795 + 6964995 * 2 ^ 59
def prefixEnd_6964995 : Nat := 4983230072969 + 3 ^ 40 * 6964995 * 2
def baseEnd_6964995 : Nat := 1192130063720694052910359

theorem tailTrace_6964995 : CollatzResearch.WordTrace tailWord_6964995 prefixEnd_6964995 1192130063720694052910359 := by
  unfold tailWord_6964995
  simp only [CollatzResearch.WordTrace]
  refine ⟨254034237402020116288072439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169356158268013410858714959 254034237402020116288072439)
  ·
    refine ⟨381051356103030174432108659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254034237402020116288072439 381051356103030174432108659)
    ·
      refine ⟨571577034154545261648162989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381051356103030174432108659 571577034154545261648162989)
      ·
        refine ⟨214341387807954473118061121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571577034154545261648162989 214341387807954473118061121)
        ·
          refine ⟨160756040855965854838545841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214341387807954473118061121 160756040855965854838545841)
          ·
            refine ⟨120567030641974391128909381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160756040855965854838545841 120567030641974391128909381)
            ·
              refine ⟨22606318245370198336670509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120567030641974391128909381 22606318245370198336670509)
              ·
                refine ⟨8477369342013824376251441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22606318245370198336670509 8477369342013824376251441)
                ·
                  refine ⟨6358027006510368282188581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477369342013824376251441 6358027006510368282188581)
                  ·
                    refine ⟨1192130063720694052910359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358027006510368282188581 1192130063720694052910359)
                    ·
                      rfl

theorem cell23_6964995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 4].length) (baseStart_6964995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6964995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6964995 prefixEnd_6964995 := by exact prefixLift 6964995
  have htrace : WordTrace (prefixWord ++ tailWord_6964995) baseStart_6964995 baseEnd_6964995 := by
    simpa [prefixWord, tailWord_6964995, baseEnd_6964995] using wordTrace_append hprefix tailTrace_6964995
  have hstable : (prefixWord ++ tailWord_6964995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6964995).length < 2 ^ (prefixWord ++ tailWord_6964995).sum := by decide
  have hdescent : baseEnd_6964995 < baseStart_6964995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6964995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965002 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_6965002 : Nat := 118140960795 + 6965002 * 2 ^ 59
def prefixEnd_6965002 : Nat := 4983230072969 + 3 ^ 40 * 6965002 * 2
def baseEnd_6965002 : Nat := 3576393785526663631343545

theorem tailTrace_6965002 : CollatzResearch.WordTrace tailWord_6965002 prefixEnd_6965002 3576393785526663631343545 := by
  unfold tailWord_6965002
  simp only [CollatzResearch.WordTrace]
  refine ⟨63508623178248689120894315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169356328475329837655718173 63508623178248689120894315)
  ·
    refine ⟨95262934767373033681341473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63508623178248689120894315 95262934767373033681341473)
    ·
      refine ⟨71447201075529775261006105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95262934767373033681341473 71447201075529775261006105)
      ·
        refine ⟨53585400806647331445754579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71447201075529775261006105 53585400806647331445754579)
        ·
          refine ⟨80378101209970997168631869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53585400806647331445754579 80378101209970997168631869)
          ·
            refine ⟨30141787953739123938236951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80378101209970997168631869 30141787953739123938236951)
            ·
              refine ⟨45212681930608685907355427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30141787953739123938236951 45212681930608685907355427)
              ·
                refine ⟨67819022895913028861033141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45212681930608685907355427 67819022895913028861033141)
                ·
                  refine ⟨6358033396491846455721857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67819022895913028861033141 6358033396491846455721857)
                  ·
                    refine ⟨4768525047368884841791393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358033396491846455721857 4768525047368884841791393)
                    ·
                      refine ⟨3576393785526663631343545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768525047368884841791393 3576393785526663631343545)
                      ·
                        rfl

theorem cell23_6965002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_6965002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965002 prefixEnd_6965002 := by exact prefixLift 6965002
  have htrace : WordTrace (prefixWord ++ tailWord_6965002) baseStart_6965002 baseEnd_6965002 := by
    simpa [prefixWord, tailWord_6965002, baseEnd_6965002] using wordTrace_append hprefix tailTrace_6965002
  have hstable : (prefixWord ++ tailWord_6965002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965002).length < 2 ^ (prefixWord ++ tailWord_6965002).sum := by decide
  have hdescent : baseEnd_6965002 < baseStart_6965002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965015 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6965015 : Nat := 118140960795 + 6965015 * 2 ^ 59
def prefixEnd_6965015 : Nat := 4983230072969 + 3 ^ 40 * 6965015 * 2
def baseEnd_6965015 : Nat := 3576400460775172080480985

theorem tailTrace_6965015 : CollatzResearch.WordTrace tailWord_6965015 prefixEnd_6965015 3576400460775172080480985 := by
  unfold tailWord_6965015
  simp only [CollatzResearch.WordTrace]
  refine ⟨254034966861947659703800499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169356644574631773135866999 254034966861947659703800499)
  ·
    refine ⟨381052450292921489555700749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254034966861947659703800499 381052450292921489555700749)
    ·
      refine ⟨142894668859845558583387781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381052450292921489555700749 142894668859845558583387781)
      ·
        refine ⟨26792750411221042234385209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142894668859845558583387781 26792750411221042234385209)
        ·
          refine ⟨20094562808415781675788907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26792750411221042234385209 20094562808415781675788907)
          ·
            refine ⟨30141844212623672513683361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20094562808415781675788907 30141844212623672513683361)
            ·
              refine ⟨22606383159467754385262521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30141844212623672513683361 22606383159467754385262521)
              ·
                refine ⟨16954787369600815788946891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22606383159467754385262521 16954787369600815788946891)
                ·
                  refine ⟨25432181054401223683420337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16954787369600815788946891 25432181054401223683420337)
                  ·
                    refine ⟨19074135790800917762565253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25432181054401223683420337 19074135790800917762565253)
                    ·
                      refine ⟨3576400460775172080480985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19074135790800917762565253 3576400460775172080480985)
                      ·
                        rfl

theorem cell23_6965015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6965015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965015 prefixEnd_6965015 := by exact prefixLift 6965015
  have htrace : WordTrace (prefixWord ++ tailWord_6965015) baseStart_6965015 baseEnd_6965015 := by
    simpa [prefixWord, tailWord_6965015, baseEnd_6965015] using wordTrace_append hprefix tailTrace_6965015
  have hstable : (prefixWord ++ tailWord_6965015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965015).length < 2 ^ (prefixWord ++ tailWord_6965015).sum := by decide
  have hdescent : baseEnd_6965015 < baseStart_6965015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965046 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_6965046 : Nat := 118140960795 + 6965046 * 2 ^ 59
def prefixEnd_6965046 : Nat := 4983230072969 + 3 ^ 40 * 6965046 * 2
def baseEnd_6965046 : Nat := 1192138792891820486397781

theorem tailTrace_6965046 : CollatzResearch.WordTrace tailWord_6965046 prefixEnd_6965046 1192138792891820486397781 := by
  unfold tailWord_6965046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15877256095302209499886187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169357398349890234665452661 15877256095302209499886187)
  ·
    refine ⟨23815884142953314249829281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15877256095302209499886187 23815884142953314249829281)
    ·
      refine ⟨17861913107214985687371961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23815884142953314249829281 17861913107214985687371961)
      ·
        refine ⟨13396434830411239265528971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17861913107214985687371961 13396434830411239265528971)
        ·
          refine ⟨20094652245616858898293457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396434830411239265528971 20094652245616858898293457)
          ·
            refine ⟨15070989184212644173720093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20094652245616858898293457 15070989184212644173720093)
            ·
              refine ⟨5651620944079741565145035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15070989184212644173720093 5651620944079741565145035)
              ·
                refine ⟨8477431416119612347717553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651620944079741565145035 8477431416119612347717553)
                ·
                  refine ⟨6358073562089709260788165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477431416119612347717553 6358073562089709260788165)
                  ·
                    refine ⟨1192138792891820486397781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358073562089709260788165 1192138792891820486397781)
                    ·
                      rfl

theorem cell23_6965046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_6965046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965046 prefixEnd_6965046 := by exact prefixLift 6965046
  have htrace : WordTrace (prefixWord ++ tailWord_6965046) baseStart_6965046 baseEnd_6965046 := by
    simpa [prefixWord, tailWord_6965046, baseEnd_6965046] using wordTrace_append hprefix tailTrace_6965046
  have hstable : (prefixWord ++ tailWord_6965046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965046).length < 2 ^ (prefixWord ++ tailWord_6965046).sum := by decide
  have hdescent : baseEnd_6965046 < baseStart_6965046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965049 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6965049 : Nat := 118140960795 + 6965049 * 2 ^ 59
def prefixEnd_6965049 : Nat := 4983230072969 + 3 ^ 40 * 6965049 * 2
def baseEnd_6965049 : Nat := 3576417919117424947455829

theorem tailTrace_6965049 : CollatzResearch.WordTrace tailWord_6965049 prefixEnd_6965049 3576417919117424947455829 := by
  unfold tailWord_6965049
  simp only [CollatzResearch.WordTrace]
  refine ⟨254036206943824483510538201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169357471295882989007025467 254036206943824483510538201)
  ·
    refine ⟨190527155207868362632903651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254036206943824483510538201 190527155207868362632903651)
    ·
      refine ⟨285790732811802543949355477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190527155207868362632903651 285790732811802543949355477)
      ·
        refine ⟨6698220300276622123813019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 285790732811802543949355477 6698220300276622123813019)
        ·
          refine ⟨10047330450414933185719529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698220300276622123813019 10047330450414933185719529)
          ·
            refine ⟨7535497837811199889289647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10047330450414933185719529 7535497837811199889289647)
            ·
              refine ⟨11303246756716799833934471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535497837811199889289647 11303246756716799833934471)
              ·
                refine ⟨16954870135075199750901707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11303246756716799833934471 16954870135075199750901707)
                ·
                  refine ⟨25432305202612799626352561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16954870135075199750901707 25432305202612799626352561)
                  ·
                    refine ⟨19074228901959599719764421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25432305202612799626352561 19074228901959599719764421)
                    ·
                      refine ⟨3576417919117424947455829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19074228901959599719764421 3576417919117424947455829)
                      ·
                        rfl

theorem cell23_6965049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6965049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965049 prefixEnd_6965049 := by exact prefixLift 6965049
  have htrace : WordTrace (prefixWord ++ tailWord_6965049) baseStart_6965049 baseEnd_6965049 := by
    simpa [prefixWord, tailWord_6965049, baseEnd_6965049] using wordTrace_append hprefix tailTrace_6965049
  have hstable : (prefixWord ++ tailWord_6965049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965049).length < 2 ^ (prefixWord ++ tailWord_6965049).sum := by decide
  have hdescent : baseEnd_6965049 < baseStart_6965049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965052 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_6965052 : Nat := 118140960795 + 6965052 * 2 ^ 59
def prefixEnd_6965052 : Nat := 4983230072969 + 3 ^ 40 * 6965052 * 2
def baseEnd_6965052 : Nat := 3576419459559388435718315

theorem tailTrace_6965052 : CollatzResearch.WordTrace tailWord_6965052 prefixEnd_6965052 3576419459559388435718315 := by
  unfold tailWord_6965052
  simp only [CollatzResearch.WordTrace]
  refine ⟨127018158181406807511448705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169357544241875743348598273 127018158181406807511448705)
  ·
    refine ⟨95263618636055105633586529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127018158181406807511448705 95263618636055105633586529)
    ·
      refine ⟨71447713977041329225189897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95263618636055105633586529 71447713977041329225189897)
      ·
        refine ⟨53585785482780996918892423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71447713977041329225189897 53585785482780996918892423)
        ·
          refine ⟨80378678224171495378338635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53585785482780996918892423 80378678224171495378338635)
          ·
            refine ⟨120568017336257243067507953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80378678224171495378338635 120568017336257243067507953)
            ·
              refine ⟨90426013002192932300630965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120568017336257243067507953 90426013002192932300630965)
              ·
                refine ⟨8477438718955587403184153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90426013002192932300630965 8477438718955587403184153)
                ·
                  refine ⟨6358079039216690552388115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477438718955587403184153 6358079039216690552388115)
                  ·
                    refine ⟨9537118558825035828582173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358079039216690552388115 9537118558825035828582173)
                    ·
                      refine ⟨3576419459559388435718315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9537118558825035828582173 3576419459559388435718315)
                      ·
                        rfl

theorem cell23_6965052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_6965052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965052 prefixEnd_6965052 := by exact prefixLift 6965052
  have htrace : WordTrace (prefixWord ++ tailWord_6965052) baseStart_6965052 baseEnd_6965052 := by
    simpa [prefixWord, tailWord_6965052, baseEnd_6965052] using wordTrace_append hprefix tailTrace_6965052
  have hstable : (prefixWord ++ tailWord_6965052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965052).length < 2 ^ (prefixWord ++ tailWord_6965052).sum := by decide
  have hdescent : baseEnd_6965052 < baseStart_6965052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965069 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6965069 : Nat := 118140960795 + 6965069 * 2 ^ 59
def prefixEnd_6965069 : Nat := 4983230072969 + 3 ^ 40 * 6965069 * 2
def baseEnd_6965069 : Nat := 3576428188730514869205737

theorem tailTrace_6965069 : CollatzResearch.WordTrace tailWord_6965069 prefixEnd_6965069 3576428188730514869205737 := by
  unfold tailWord_6965069
  simp only [CollatzResearch.WordTrace]
  refine ⟨254036936403752026926266261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169357957602501351284177507 254036936403752026926266261)
  ·
    refine ⟨11907981393925876262168731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 254036936403752026926266261 11907981393925876262168731)
    ·
      refine ⟨17861972090888814393253097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11907981393925876262168731 17861972090888814393253097)
      ·
        refine ⟨13396479068166610794939823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17861972090888814393253097 13396479068166610794939823)
        ·
          refine ⟨20094718602249916192409735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396479068166610794939823 20094718602249916192409735)
          ·
            refine ⟨30142077903374874288614603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20094718602249916192409735 30142077903374874288614603)
            ·
              refine ⟨45213116855062311432921905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30142077903374874288614603 45213116855062311432921905)
              ·
                refine ⟨33909837641296733574691429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45213116855062311432921905 33909837641296733574691429)
                ·
                  refine ⟨6358094557743137545254643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33909837641296733574691429 6358094557743137545254643)
                  ·
                    refine ⟨9537141836614706317881965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358094557743137545254643 9537141836614706317881965)
                    ·
                      refine ⟨3576428188730514869205737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9537141836614706317881965 3576428188730514869205737)
                      ·
                        rfl

theorem cell23_6965069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6965069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965069 prefixEnd_6965069 := by exact prefixLift 6965069
  have htrace : WordTrace (prefixWord ++ tailWord_6965069) baseStart_6965069 baseEnd_6965069 := by
    simpa [prefixWord, tailWord_6965069, baseEnd_6965069] using wordTrace_append hprefix tailTrace_6965069
  have hstable : (prefixWord ++ tailWord_6965069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965069).length < 2 ^ (prefixWord ++ tailWord_6965069).sum := by decide
  have hdescent : baseEnd_6965069 < baseStart_6965069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965095 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_6965095 : Nat := 118140960795 + 6965095 * 2 ^ 59
def prefixEnd_6965095 : Nat := 4983230072969 + 3 ^ 40 * 6965095 * 2
def baseEnd_6965095 : Nat := 3576441539227531767480617

theorem tailTrace_6965095 : CollatzResearch.WordTrace tailWord_6965095 prefixEnd_6965095 3576441539227531767480617 := by
  unfold tailWord_6965095
  simp only [CollatzResearch.WordTrace]
  refine ⟨254037884701657833366712739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169358589801105222244475159 254037884701657833366712739)
  ·
    refine ⟨381056827052486750050069109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254037884701657833366712739 381056827052486750050069109)
    ·
      refine ⟨35724077536170632817193979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381056827052486750050069109 35724077536170632817193979)
      ·
        refine ⟨53586116304255949225790969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35724077536170632817193979 53586116304255949225790969)
        ·
          refine ⟨40189587228191961919343227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53586116304255949225790969 40189587228191961919343227)
          ·
            refine ⟨60284380842287942879014841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40189587228191961919343227 60284380842287942879014841)
            ·
              refine ⟨45213285631715957159261131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60284380842287942879014841 45213285631715957159261131)
              ·
                refine ⟨67819928447573935738891697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45213285631715957159261131 67819928447573935738891697)
                ·
                  refine ⟨50864946335680451804168773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67819928447573935738891697 50864946335680451804168773)
                  ·
                    refine ⟨9537177437940084713281645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50864946335680451804168773 9537177437940084713281645)
                    ·
                      refine ⟨3576441539227531767480617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9537177437940084713281645 3576441539227531767480617)
                      ·
                        rfl

theorem cell23_6965095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_6965095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965095 prefixEnd_6965095 := by exact prefixLift 6965095
  have htrace : WordTrace (prefixWord ++ tailWord_6965095) baseStart_6965095 baseEnd_6965095 := by
    simpa [prefixWord, tailWord_6965095, baseEnd_6965095] using wordTrace_append hprefix tailTrace_6965095
  have hstable : (prefixWord ++ tailWord_6965095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965095).length < 2 ^ (prefixWord ++ tailWord_6965095).sum := by decide
  have hdescent : baseEnd_6965095 < baseStart_6965095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965145 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_6965145 : Nat := 118140960795 + 6965145 * 2 ^ 59
def prefixEnd_6965145 : Nat := 4983230072969 + 3 ^ 40 * 6965145 * 2
def baseEnd_6965145 : Nat := 1192155737753418857285129

theorem tailTrace_6965145 : CollatzResearch.WordTrace tailWord_6965145 prefixEnd_6965145 1192155737753418857285129 := by
  unfold tailWord_6965145
  simp only [CollatzResearch.WordTrace]
  refine ⟨254039708351476691906032889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169359805567651127937355259 254039708351476691906032889)
  ·
    refine ⟨190529781263607518929524667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254039708351476691906032889 190529781263607518929524667)
    ·
      refine ⟨285794671895411278394287001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190529781263607518929524667 285794671895411278394287001)
      ·
        refine ⟨214346003921558458795715251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285794671895411278394287001 214346003921558458795715251)
        ·
          refine ⟨321519005882337688193572877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214346003921558458795715251 321519005882337688193572877)
          ·
            refine ⟨120569627205876633072589829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321519005882337688193572877 120569627205876633072589829)
            ·
              refine ⟨22606805101101868701110593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120569627205876633072589829 22606805101101868701110593)
              ·
                refine ⟨16955103825826401525832945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22606805101101868701110593 16955103825826401525832945)
                ·
                  refine ⟨12716327869369801144374709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16955103825826401525832945 12716327869369801144374709)
                  ·
                    refine ⟨1192155737753418857285129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12716327869369801144374709 1192155737753418857285129)
                    ·
                      rfl

theorem cell23_6965145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_6965145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965145 prefixEnd_6965145 := by exact prefixLift 6965145
  have htrace : WordTrace (prefixWord ++ tailWord_6965145) baseStart_6965145 baseEnd_6965145 := by
    simpa [prefixWord, tailWord_6965145, baseEnd_6965145] using wordTrace_append hprefix tailTrace_6965145
  have hstable : (prefixWord ++ tailWord_6965145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965145).length < 2 ^ (prefixWord ++ tailWord_6965145).sum := by decide
  have hdescent : baseEnd_6965145 < baseStart_6965145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965149 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 5]
def baseStart_6965149 : Nat := 118140960795 + 6965149 * 2 ^ 59
def prefixEnd_6965149 : Nat := 4983230072969 + 3 ^ 40 * 6965149 * 2
def baseEnd_6965149 : Nat := 397385474131430506245041

theorem tailTrace_6965149 : CollatzResearch.WordTrace tailWord_6965149 prefixEnd_6965149 397385474131430506245041 := by
  unfold tailWord_6965149
  simp only [CollatzResearch.WordTrace]
  refine ⟨254039854243462200589178501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169359902828974800392785667 254039854243462200589178501)
  ·
    refine ⟨47632472670649162610470969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254039854243462200589178501 47632472670649162610470969)
    ·
      refine ⟨35724354502986871957853227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47632472670649162610470969 35724354502986871957853227)
      ·
        refine ⟨53586531754480307936779841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35724354502986871957853227 53586531754480307936779841)
        ·
          refine ⟨40189898815860230952584881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53586531754480307936779841 40189898815860230952584881)
          ·
            refine ⟨30142424111895173214438661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40189898815860230952584881 30142424111895173214438661)
            ·
              refine ⟨5651704520980344977707249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30142424111895173214438661 5651704520980344977707249)
              ·
                refine ⟨4238778390735258733280437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5651704520980344977707249 4238778390735258733280437)
                ·
                  refine ⟨397385474131430506245041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4238778390735258733280437 397385474131430506245041)
                  ·
                    rfl

theorem cell23_6965149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_6965149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965149 prefixEnd_6965149 := by exact prefixLift 6965149
  have htrace : WordTrace (prefixWord ++ tailWord_6965149) baseStart_6965149 baseEnd_6965149 := by
    simpa [prefixWord, tailWord_6965149, baseEnd_6965149] using wordTrace_append hprefix tailTrace_6965149
  have hstable : (prefixWord ++ tailWord_6965149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965149).length < 2 ^ (prefixWord ++ tailWord_6965149).sum := by decide
  have hdescent : baseEnd_6965149 < baseStart_6965149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965166 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_6965166 : Nat := 118140960795 + 6965166 * 2 ^ 59
def prefixEnd_6965166 : Nat := 4983230072969 + 3 ^ 40 * 6965166 * 2
def baseEnd_6965166 : Nat := 397386444039333443299199

theorem tailTrace_6965166 : CollatzResearch.WordTrace tailWord_6965166 prefixEnd_6965166 397386444039333443299199 := by
  unfold tailWord_6965166
  simp only [CollatzResearch.WordTrace]
  refine ⟨31755059285550076561568419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169360316189600408328364901 31755059285550076561568419)
  ·
    refine ⟨47632588928325114842352629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31755059285550076561568419 47632588928325114842352629)
    ·
      refine ⟨4465555212030479516470559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47632588928325114842352629 4465555212030479516470559)
      ·
        refine ⟨6698332818045719274705839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465555212030479516470559 6698332818045719274705839)
        ·
          refine ⟨10047499227068578912058759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698332818045719274705839 10047499227068578912058759)
          ·
            refine ⟨15071248840602868368088139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047499227068578912058759 15071248840602868368088139)
            ·
              refine ⟨22606873260904302552132209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15071248840602868368088139 22606873260904302552132209)
              ·
                refine ⟨16955154945678226914099157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22606873260904302552132209 16955154945678226914099157)
                ·
                  refine ⟨397386444039333443299199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16955154945678226914099157 397386444039333443299199)
                  ·
                    rfl

theorem cell23_6965166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_6965166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965166 prefixEnd_6965166 := by exact prefixLift 6965166
  have htrace : WordTrace (prefixWord ++ tailWord_6965166) baseStart_6965166 baseEnd_6965166 := by
    simpa [prefixWord, tailWord_6965166, baseEnd_6965166] using wordTrace_append hprefix tailTrace_6965166
  have hstable : (prefixWord ++ tailWord_6965166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965166).length < 2 ^ (prefixWord ++ tailWord_6965166).sum := by decide
  have hdescent : baseEnd_6965166 < baseStart_6965166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965182 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_6965182 : Nat := 118140960795 + 6965182 * 2 ^ 59
def prefixEnd_6965182 : Nat := 4983230072969 + 3 ^ 40 * 6965182 * 2
def baseEnd_6965182 : Nat := 3576486212044472927092717

theorem tailTrace_6965182 : CollatzResearch.WordTrace tailWord_6965182 prefixEnd_6965182 3576486212044472927092717 := by
  unfold tailWord_6965182
  simp only [CollatzResearch.WordTrace]
  refine ⟨31755132231542830903141225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169360705234895098150086533 31755132231542830903141225)
  ·
    refine ⟨23816349173657123177355919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31755132231542830903141225 23816349173657123177355919)
    ·
      refine ⟨35724523760485684766033879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23816349173657123177355919 35724523760485684766033879)
      ·
        refine ⟨53586785640728527149050819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35724523760485684766033879 53586785640728527149050819)
        ·
          refine ⟨80380178461092790723576229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53586785640728527149050819 80380178461092790723576229)
          ·
            refine ⟨15071283461454898260670543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80380178461092790723576229 15071283461454898260670543)
            ·
              refine ⟨22606925192182347391005815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15071283461454898260670543 22606925192182347391005815)
              ·
                refine ⟨33910387788273521086508723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22606925192182347391005815 33910387788273521086508723)
                ·
                  refine ⟨50865581682410281629763085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33910387788273521086508723 50865581682410281629763085)
                  ·
                    refine ⟨19074593130903855611161157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50865581682410281629763085 19074593130903855611161157)
                    ·
                      refine ⟨3576486212044472927092717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19074593130903855611161157 3576486212044472927092717)
                      ·
                        rfl

theorem cell23_6965182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_6965182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965182 prefixEnd_6965182 := by exact prefixLift 6965182
  have htrace : WordTrace (prefixWord ++ tailWord_6965182) baseStart_6965182 baseEnd_6965182 := by
    simpa [prefixWord, tailWord_6965182, baseEnd_6965182] using wordTrace_append hprefix tailTrace_6965182
  have hstable : (prefixWord ++ tailWord_6965182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965182).length < 2 ^ (prefixWord ++ tailWord_6965182).sum := by decide
  have hdescent : baseEnd_6965182 < baseStart_6965182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965209 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 3, 4]
def baseStart_6965209 : Nat := 118140960795 + 6965209 * 2 ^ 59
def prefixEnd_6965209 : Nat := 4983230072969 + 3 ^ 40 * 6965209 * 2
def baseEnd_6965209 : Nat := 1192166692007381440485031

theorem tailTrace_6965209 : CollatzResearch.WordTrace tailWord_6965209 prefixEnd_6965209 1192166692007381440485031 := by
  unfold tailWord_6965209
  simp only [CollatzResearch.WordTrace]
  refine ⟨254042042623244830836362681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169361361748829887224241787 254042042623244830836362681)
  ·
    refine ⟨190531531967433623127272011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254042042623244830836362681 190531531967433623127272011)
    ·
      refine ⟨285797297951150434690908017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190531531967433623127272011 285797297951150434690908017)
      ·
        refine ⟨214347973463362826018181013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285797297951150434690908017 214347973463362826018181013)
        ·
          refine ⟨10047561256095132469602235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214347973463362826018181013 10047561256095132469602235)
          ·
            refine ⟨15071341884142698704403353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047561256095132469602235 15071341884142698704403353)
            ·
              refine ⟨11303506413107024028302515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15071341884142698704403353 11303506413107024028302515)
              ·
                refine ⟨16955259619660536042453773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11303506413107024028302515 16955259619660536042453773)
                ·
                  refine ⟨6358222357372701015920165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16955259619660536042453773 6358222357372701015920165)
                  ·
                    refine ⟨1192166692007381440485031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358222357372701015920165 1192166692007381440485031)
                    ·
                      rfl

theorem cell23_6965209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_6965209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965209 prefixEnd_6965209 := by exact prefixLift 6965209
  have htrace : WordTrace (prefixWord ++ tailWord_6965209) baseStart_6965209 baseEnd_6965209 := by
    simpa [prefixWord, tailWord_6965209, baseEnd_6965209] using wordTrace_append hprefix tailTrace_6965209
  have hstable : (prefixWord ++ tailWord_6965209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965209).length < 2 ^ (prefixWord ++ tailWord_6965209).sum := by decide
  have hdescent : baseEnd_6965209 < baseStart_6965209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965235 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 3, 5]
def baseStart_6965235 : Nat := 118140960795 + 6965235 * 2 ^ 59
def prefixEnd_6965235 : Nat := 4983230072969 + 3 ^ 40 * 6965235 * 2
def baseEnd_6965235 : Nat := 1192171142173053739909991

theorem tailTrace_6965235 : CollatzResearch.WordTrace tailWord_6965235 prefixEnd_6965235 1192171142173053739909991 := by
  unfold tailWord_6965235
  simp only [CollatzResearch.WordTrace]
  refine ⟨254042990921150637276809159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169361993947433758184539439 254042990921150637276809159)
  ·
    refine ⟨381064486381725955915213739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254042990921150637276809159 381064486381725955915213739)
    ·
      refine ⟨571596729572588933872820609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381064486381725955915213739 571596729572588933872820609)
      ·
        refine ⟨428697547179441700404615457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571596729572588933872820609 428697547179441700404615457)
        ·
          refine ⟨321523160384581275303461593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428697547179441700404615457 321523160384581275303461593)
          ·
            refine ⟨241142370288435956477596195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321523160384581275303461593 241142370288435956477596195)
            ·
              refine ⟨361713555432653934716394293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241142370288435956477596195 361713555432653934716394293)
              ·
                refine ⟨33910645821811306379661965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361713555432653934716394293 33910645821811306379661965)
                ·
                  refine ⟨12716492183179239892373237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33910645821811306379661965 12716492183179239892373237)
                  ·
                    refine ⟨1192171142173053739909991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12716492183179239892373237 1192171142173053739909991)
                    ·
                      rfl

theorem cell23_6965235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 5].length) (baseStart_6965235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965235 prefixEnd_6965235 := by exact prefixLift 6965235
  have htrace : WordTrace (prefixWord ++ tailWord_6965235) baseStart_6965235 baseEnd_6965235 := by
    simpa [prefixWord, tailWord_6965235, baseEnd_6965235] using wordTrace_append hprefix tailTrace_6965235
  have hstable : (prefixWord ++ tailWord_6965235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965235).length < 2 ^ (prefixWord ++ tailWord_6965235).sum := by decide
  have hdescent : baseEnd_6965235 < baseStart_6965235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965259 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 2, 3, 2]
def baseStart_6965259 : Nat := 118140960795 + 6965259 * 2 ^ 59
def prefixEnd_6965259 : Nat := 4983230072969 + 3 ^ 40 * 6965259 * 2
def baseEnd_6965259 : Nat := 3576525750054869125829863

theorem tailTrace_6965259 : CollatzResearch.WordTrace tailWord_6965259 prefixEnd_6965259 3576525750054869125829863 := by
  unfold tailWord_6965259
  simp only [CollatzResearch.WordTrace]
  refine ⟨254043866273063689375682831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169362577515375792917121887 254043866273063689375682831)
  ·
    refine ⟨381065799409595534063524247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254043866273063689375682831 381065799409595534063524247)
    ·
      refine ⟨571598699114393301095286371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381065799409595534063524247 571598699114393301095286371)
      ·
        refine ⟨857398048671589951642929557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571598699114393301095286371 857398048671589951642929557)
        ·
          refine ⟨40190533531480778983262323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 857398048671589951642929557 40190533531480778983262323)
          ·
            refine ⟨60285800297221168474893485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40190533531480778983262323 60285800297221168474893485)
            ·
              refine ⟨22607175111457938178085057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60285800297221168474893485 22607175111457938178085057)
              ·
                refine ⟨16955381333593453633563793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22607175111457938178085057 16955381333593453633563793)
                ·
                  refine ⟨12716536000195090225172845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16955381333593453633563793 12716536000195090225172845)
                  ·
                    refine ⟨4768701000073158834439817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12716536000195090225172845 4768701000073158834439817)
                    ·
                      refine ⟨3576525750054869125829863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768701000073158834439817 3576525750054869125829863)
                      ·
                        rfl

theorem cell23_6965259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3, 2].length) (baseStart_6965259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965259 prefixEnd_6965259 := by exact prefixLift 6965259
  have htrace : WordTrace (prefixWord ++ tailWord_6965259) baseStart_6965259 baseEnd_6965259 := by
    simpa [prefixWord, tailWord_6965259, baseEnd_6965259] using wordTrace_append hprefix tailTrace_6965259
  have hstable : (prefixWord ++ tailWord_6965259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965259).length < 2 ^ (prefixWord ++ tailWord_6965259).sum := by decide
  have hdescent : baseEnd_6965259 < baseStart_6965259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965272 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_6965272 : Nat := 118140960795 + 6965272 * 2 ^ 59
def prefixEnd_6965272 : Nat := 4983230072969 + 3 ^ 40 * 6965272 * 2
def baseEnd_6965272 : Nat := 3576532425303377574967303

theorem tailTrace_6965272 : CollatzResearch.WordTrace tailWord_6965272 prefixEnd_6965272 3576532425303377574967303 := by
  unfold tailWord_6965272
  simp only [CollatzResearch.WordTrace]
  refine ⟨127022170211008296297953035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169362893614677728397270713 127022170211008296297953035)
  ·
    refine ⟨190533255316512444446929553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127022170211008296297953035 190533255316512444446929553)
    ·
      refine ⟨142899941487384333335197165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190533255316512444446929553 142899941487384333335197165)
      ·
        refine ⟨53587478057769125000698937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142899941487384333335197165 53587478057769125000698937)
        ·
          refine ⟨40190608543326843750524203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53587478057769125000698937 40190608543326843750524203)
          ·
            refine ⟨60285912814990265625786305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40190608543326843750524203 60285912814990265625786305)
            ·
              refine ⟨45214434611242699219339729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60285912814990265625786305 45214434611242699219339729)
              ·
                refine ⟨33910825958432024414504797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45214434611242699219339729 33910825958432024414504797)
                ·
                  refine ⟨12716559734412009155439299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33910825958432024414504797 12716559734412009155439299)
                  ·
                    refine ⟨19074839601618013733158949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12716559734412009155439299 19074839601618013733158949)
                    ·
                      refine ⟨3576532425303377574967303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19074839601618013733158949 3576532425303377574967303)
                      ·
                        rfl

theorem cell23_6965272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_6965272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965272 prefixEnd_6965272 := by exact prefixLift 6965272
  have htrace : WordTrace (prefixWord ++ tailWord_6965272) baseStart_6965272 baseEnd_6965272 := by
    simpa [prefixWord, tailWord_6965272, baseEnd_6965272] using wordTrace_append hprefix tailTrace_6965272
  have hstable : (prefixWord ++ tailWord_6965272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965272).length < 2 ^ (prefixWord ++ tailWord_6965272).sum := by decide
  have hdescent : baseEnd_6965272 < baseStart_6965272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965275 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5]
def baseStart_6965275 : Nat := 118140960795 + 6965275 * 2 ^ 59
def prefixEnd_6965275 : Nat := 4983230072969 + 3 ^ 40 * 6965275 * 2
def baseEnd_6965275 : Nat := 3576533965745341063229789

theorem tailTrace_6965275 : CollatzResearch.WordTrace tailWord_6965275 prefixEnd_6965275 3576533965745341063229789 := by
  unfold tailWord_6965275
  simp only [CollatzResearch.WordTrace]
  refine ⟨254044449841005724108265279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169362966560670482738843519 254044449841005724108265279)
  ·
    refine ⟨381066674761508586162397919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254044449841005724108265279 381066674761508586162397919)
    ·
      refine ⟨571600012142262879243596879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381066674761508586162397919 571600012142262879243596879)
      ·
        refine ⟨857400018213394318865395319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571600012142262879243596879 857400018213394318865395319)
        ·
          refine ⟨1286100027320091478298092979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857400018213394318865395319 1286100027320091478298092979)
          ·
            refine ⟨1929150040980137217447139469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286100027320091478298092979 1929150040980137217447139469)
            ·
              refine ⟨723431265367551456542677301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1929150040980137217447139469 723431265367551456542677301)
              ·
                refine ⟨67821681128207949050875997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 723431265367551456542677301 67821681128207949050875997)
                ·
                  refine ⟨25433130423077980894078499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67821681128207949050875997 25433130423077980894078499)
                  ·
                    refine ⟨38149695634616971341117749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25433130423077980894078499 38149695634616971341117749)
                    ·
                      refine ⟨3576533965745341063229789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38149695634616971341117749 3576533965745341063229789)
                      ·
                        rfl

theorem cell23_6965275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_6965275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965275 prefixEnd_6965275 := by exact prefixLift 6965275
  have htrace : WordTrace (prefixWord ++ tailWord_6965275) baseStart_6965275 baseEnd_6965275 := by
    simpa [prefixWord, tailWord_6965275, baseEnd_6965275] using wordTrace_append hprefix tailTrace_6965275
  have hstable : (prefixWord ++ tailWord_6965275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965275).length < 2 ^ (prefixWord ++ tailWord_6965275).sum := by decide
  have hdescent : baseEnd_6965275 < baseStart_6965275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965282 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_6965282 : Nat := 118140960795 + 6965282 * 2 ^ 59
def prefixEnd_6965282 : Nat := 4983230072969 + 3 ^ 40 * 6965282 * 2
def baseEnd_6965282 : Nat := 1192179186703307511947419

theorem tailTrace_6965282 : CollatzResearch.WordTrace tailWord_6965282 prefixEnd_6965282 1192179186703307511947419 := by
  unfold tailWord_6965282
  simp only [CollatzResearch.WordTrace]
  refine ⟨63511176287995091075942525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169363136767986909535846733 63511176287995091075942525)
  ·
    refine ⟨23816691107998159153478447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63511176287995091075942525 23816691107998159153478447)
    ·
      refine ⟨35725036661997238730217671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23816691107998159153478447 35725036661997238730217671)
      ·
        refine ⟨53587554992995858095326507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35725036661997238730217671 53587554992995858095326507)
        ·
          refine ⟨80381332489493787142989761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53587554992995858095326507 80381332489493787142989761)
          ·
            refine ⟨60285999367120340357242321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80381332489493787142989761 60285999367120340357242321)
            ·
              refine ⟨45214499525340255267931741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60285999367120340357242321 45214499525340255267931741)
              ·
                refine ⟨16955437322002595725474403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45214499525340255267931741 16955437322002595725474403)
                ·
                  refine ⟨25433155983003893588211605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16955437322002595725474403 25433155983003893588211605)
                  ·
                    refine ⟨1192179186703307511947419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25433155983003893588211605 1192179186703307511947419)
                    ·
                      rfl

theorem cell23_6965282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_6965282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965282 prefixEnd_6965282 := by exact prefixLift 6965282
  have htrace : WordTrace (prefixWord ++ tailWord_6965282) baseStart_6965282 baseEnd_6965282 := by
    simpa [prefixWord, tailWord_6965282, baseEnd_6965282] using wordTrace_append hprefix tailTrace_6965282
  have hstable : (prefixWord ++ tailWord_6965282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965282).length < 2 ^ (prefixWord ++ tailWord_6965282).sum := by decide
  have hdescent : baseEnd_6965282 < baseStart_6965282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965315 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_6965315 : Nat := 118140960795 + 6965315 * 2 ^ 59
def prefixEnd_6965315 : Nat := 4983230072969 + 3 ^ 40 * 6965315 * 2
def baseEnd_6965315 : Nat := 3576554504971520906729605

theorem tailTrace_6965315 : CollatzResearch.WordTrace tailWord_6965315 prefixEnd_6965315 3576554504971520906729605 := by
  unfold tailWord_6965315
  simp only [CollatzResearch.WordTrace]
  refine ⟨254045908760860810939721399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169363939173907207293147599 254045908760860810939721399)
  ·
    refine ⟨381068863141291216409582099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254045908760860810939721399 381068863141291216409582099)
    ·
      refine ⟨571603294711936824614373149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381068863141291216409582099 571603294711936824614373149)
      ·
        refine ⟨214351235516976309230389931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571603294711936824614373149 214351235516976309230389931)
        ·
          refine ⟨321526853275464463845584897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214351235516976309230389931 321526853275464463845584897)
          ·
            refine ⟨241145139956598347884188673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321526853275464463845584897 241145139956598347884188673)
            ·
              refine ⟨180858854967448760913141505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241145139956598347884188673 180858854967448760913141505)
              ·
                refine ⟨135644141225586570684856129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180858854967448760913141505 135644141225586570684856129)
                ·
                  refine ⟨101733105919189928013642097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135644141225586570684856129 101733105919189928013642097)
                  ·
                    refine ⟨76299829439392446010231573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101733105919189928013642097 76299829439392446010231573)
                    ·
                      refine ⟨3576554504971520906729605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76299829439392446010231573 3576554504971520906729605)
                      ·
                        rfl

theorem cell23_6965315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_6965315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965315 prefixEnd_6965315 := by exact prefixLift 6965315
  have htrace : WordTrace (prefixWord ++ tailWord_6965315) baseStart_6965315 baseEnd_6965315 := by
    simpa [prefixWord, tailWord_6965315, baseEnd_6965315] using wordTrace_append hprefix tailTrace_6965315
  have hstable : (prefixWord ++ tailWord_6965315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965315).length < 2 ^ (prefixWord ++ tailWord_6965315).sum := by decide
  have hdescent : baseEnd_6965315 < baseStart_6965315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965322 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_6965322 : Nat := 118140960795 + 6965322 * 2 ^ 59
def prefixEnd_6965322 : Nat := 4983230072969 + 3 ^ 40 * 6965322 * 2
def baseEnd_6965322 : Nat := 3576558099336102379342073

theorem tailTrace_6965322 : CollatzResearch.WordTrace tailWord_6965322 prefixEnd_6965322 3576558099336102379342073 := by
  unfold tailWord_6965322
  simp only [CollatzResearch.WordTrace]
  refine ⟨63511541017958862783806555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169364109381223634090150813 63511541017958862783806555)
  ·
    refine ⟨95267311526938294175709833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63511541017958862783806555 95267311526938294175709833)
    ·
      refine ⟨71450483645203720631782375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95267311526938294175709833 71450483645203720631782375)
      ·
        refine ⟨107175725467805580947673563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71450483645203720631782375 107175725467805580947673563)
        ·
          refine ⟨160763588201708371421510345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107175725467805580947673563 160763588201708371421510345)
          ·
            refine ⟨120572691151281278566132759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160763588201708371421510345 120572691151281278566132759)
            ·
              refine ⟨180859036726921917849199139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120572691151281278566132759 180859036726921917849199139)
              ·
                refine ⟨271288555090382876773798709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180859036726921917849199139 271288555090382876773798709)
                ·
                  refine ⟨25433302039723394697543629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271288555090382876773798709 25433302039723394697543629)
                  ·
                    refine ⟨9537488264896273011578861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25433302039723394697543629 9537488264896273011578861)
                    ·
                      refine ⟨3576558099336102379342073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9537488264896273011578861 3576558099336102379342073)
                      ·
                        rfl

theorem cell23_6965322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_6965322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965322 prefixEnd_6965322 := by exact prefixLift 6965322
  have htrace : WordTrace (prefixWord ++ tailWord_6965322) baseStart_6965322 baseEnd_6965322 := by
    simpa [prefixWord, tailWord_6965322, baseEnd_6965322] using wordTrace_append hprefix tailTrace_6965322
  have hstable : (prefixWord ++ tailWord_6965322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965322).length < 2 ^ (prefixWord ++ tailWord_6965322).sum := by decide
  have hdescent : baseEnd_6965322 < baseStart_6965322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965346 : List Nat := [3, 3, 2, 2, 2, 1, 3, 7]
def baseStart_6965346 : Nat := 118140960795 + 6965346 * 2 ^ 59
def prefixEnd_6965346 : Nat := 4983230072969 + 3 ^ 40 * 6965346 * 2
def baseEnd_6965346 : Nat := 132465571217474455016369

theorem tailTrace_6965346 : CollatzResearch.WordTrace tailWord_6965346 prefixEnd_6965346 132465571217474455016369 := by
  unfold tailWord_6965346
  simp only [CollatzResearch.WordTrace]
  refine ⟨63511759855937125808524973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169364692949165668822733261 63511759855937125808524973)
  ·
    refine ⟨23816909945976422178196865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63511759855937125808524973 23816909945976422178196865)
    ·
      refine ⟨17862682459482316633647649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23816909945976422178196865 17862682459482316633647649)
      ·
        refine ⟨13397011844611737475235737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17862682459482316633647649 13397011844611737475235737)
        ·
          refine ⟨10047758883458803106426803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13397011844611737475235737 10047758883458803106426803)
          ·
            refine ⟨15071638325188204659640205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047758883458803106426803 15071638325188204659640205)
            ·
              refine ⟨5651864371945576747365077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15071638325188204659640205 5651864371945576747365077)
              ·
                refine ⟨132465571217474455016369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5651864371945576747365077 132465571217474455016369)
                ·
                  rfl

theorem cell23_6965346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_6965346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965346 prefixEnd_6965346 := by exact prefixLift 6965346
  have htrace : WordTrace (prefixWord ++ tailWord_6965346) baseStart_6965346 baseEnd_6965346 := by
    simpa [prefixWord, tailWord_6965346, baseEnd_6965346] using wordTrace_append hprefix tailTrace_6965346
  have hstable : (prefixWord ++ tailWord_6965346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965346).length < 2 ^ (prefixWord ++ tailWord_6965346).sum := by decide
  have hdescent : baseEnd_6965346 < baseStart_6965346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965372 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_6965372 : Nat := 118140960795 + 6965372 * 2 ^ 59
def prefixEnd_6965372 : Nat := 4983230072969 + 3 ^ 40 * 6965372 * 2
def baseEnd_6965372 : Nat := 1192194591122942394572281

theorem tailTrace_6965372 : CollatzResearch.WordTrace tailWord_6965372 prefixEnd_6965372 1192194591122942394572281 := by
  unfold tailWord_6965372
  simp only [CollatzResearch.WordTrace]
  refine ⟨127023993860827154837273185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169365325147769539783030913 127023993860827154837273185)
  ·
    refine ⟨95267995395620366127954889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127023993860827154837273185 95267995395620366127954889)
    ·
      refine ⟨71450996546715274595966167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95267995395620366127954889 71450996546715274595966167)
      ·
        refine ⟨107176494820072911893949251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71450996546715274595966167 107176494820072911893949251)
        ·
          refine ⟨160764742230109367840923877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107176494820072911893949251 160764742230109367840923877)
          ·
            refine ⟨30143389168145506470173227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160764742230109367840923877 30143389168145506470173227)
            ·
              refine ⟨45215083752218259705259841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30143389168145506470173227 45215083752218259705259841)
              ·
                refine ⟨33911312814163694778944881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45215083752218259705259841 33911312814163694778944881)
                ·
                  refine ⟨25433484610622771084208661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33911312814163694778944881 25433484610622771084208661)
                  ·
                    refine ⟨1192194591122942394572281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25433484610622771084208661 1192194591122942394572281)
                    ·
                      rfl

theorem cell23_6965372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_6965372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965372 prefixEnd_6965372 := by exact prefixLift 6965372
  have htrace : WordTrace (prefixWord ++ tailWord_6965372) baseStart_6965372 baseEnd_6965372 := by
    simpa [prefixWord, tailWord_6965372, baseEnd_6965372] using wordTrace_append hprefix tailTrace_6965372
  have hstable : (prefixWord ++ tailWord_6965372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965372).length < 2 ^ (prefixWord ++ tailWord_6965372).sum := by decide
  have hdescent : baseEnd_6965372 < baseStart_6965372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965373 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_6965373 : Nat := 118140960795 + 6965373 * 2 ^ 59
def prefixEnd_6965373 : Nat := 4983230072969 + 3 ^ 40 * 6965373 * 2
def baseEnd_6965373 : Nat := 3576584286849481679804339

theorem tailTrace_6965373 : CollatzResearch.WordTrace tailWord_6965373 prefixEnd_6965373 3576584286849481679804339 := by
  unfold tailWord_6965373
  simp only [CollatzResearch.WordTrace]
  refine ⟨254048024194650686845332773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169365349463100457896888515 254048024194650686845332773)
  ·
    refine ⟨47634004536497003783499895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254048024194650686845332773 47634004536497003783499895)
    ·
      refine ⟨71451006804745505675249843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47634004536497003783499895 71451006804745505675249843)
      ·
        refine ⟨107176510207118258512874765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71451006804745505675249843 107176510207118258512874765)
        ·
          refine ⟨40191191327669346942328037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107176510207118258512874765 40191191327669346942328037)
          ·
            refine ⟨7535848373938002551686507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40191191327669346942328037 7535848373938002551686507)
            ·
              refine ⟨11303772560907003827529761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535848373938002551686507 11303772560907003827529761)
              ·
                refine ⟨8477829420680252870647321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11303772560907003827529761 8477829420680252870647321)
                ·
                  refine ⟨6358372065510189652985491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477829420680252870647321 6358372065510189652985491)
                  ·
                    refine ⟨9537558098265284479478237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358372065510189652985491 9537558098265284479478237)
                    ·
                      refine ⟨3576584286849481679804339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9537558098265284479478237 3576584286849481679804339)
                      ·
                        rfl

theorem cell23_6965373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_6965373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965373 prefixEnd_6965373 := by exact prefixLift 6965373
  have htrace : WordTrace (prefixWord ++ tailWord_6965373) baseStart_6965373 baseEnd_6965373 := by
    simpa [prefixWord, tailWord_6965373, baseEnd_6965373] using wordTrace_append hprefix tailTrace_6965373
  have hstable : (prefixWord ++ tailWord_6965373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965373).length < 2 ^ (prefixWord ++ tailWord_6965373).sum := by decide
  have hdescent : baseEnd_6965373 < baseStart_6965373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965390 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6965390 : Nat := 118140960795 + 6965390 * 2 ^ 59
def prefixEnd_6965390 : Nat := 4983230072969 + 3 ^ 40 * 6965390 * 2
def baseEnd_6965390 : Nat := 3576593016020608113291761

theorem tailTrace_6965390 : CollatzResearch.WordTrace tailWord_6965390 prefixEnd_6965390 3576593016020608113291761 := by
  unfold tailWord_6965390
  simp only [CollatzResearch.WordTrace]
  refine ⟨31756080529448637343587703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169365762823726065832467749 31756080529448637343587703)
  ·
    refine ⟨47634120794172956015381555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31756080529448637343587703 47634120794172956015381555)
    ·
      refine ⟨71451181191259434023072333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47634120794172956015381555 71451181191259434023072333)
      ·
        refine ⟨26794192946722287758652125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71451181191259434023072333 26794192946722287758652125)
        ·
          refine ⟨10047822355020857909494547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26794192946722287758652125 10047822355020857909494547)
          ·
            refine ⟨15071733532531286864241821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047822355020857909494547 15071733532531286864241821)
            ·
              refine ⟨5651900074699232574090683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15071733532531286864241821 5651900074699232574090683)
              ·
                refine ⟨8477850112048848861136025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651900074699232574090683 8477850112048848861136025)
                ·
                  refine ⟨6358387584036636645852019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477850112048848861136025 6358387584036636645852019)
                  ·
                    refine ⟨9537581376054954968778029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358387584036636645852019 9537581376054954968778029)
                    ·
                      refine ⟨3576593016020608113291761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9537581376054954968778029 3576593016020608113291761)
                      ·
                        rfl

theorem cell23_6965390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6965390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965390 prefixEnd_6965390 := by exact prefixLift 6965390
  have htrace : WordTrace (prefixWord ++ tailWord_6965390) baseStart_6965390 baseEnd_6965390 := by
    simpa [prefixWord, tailWord_6965390, baseEnd_6965390] using wordTrace_append hprefix tailTrace_6965390
  have hstable : (prefixWord ++ tailWord_6965390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965390).length < 2 ^ (prefixWord ++ tailWord_6965390).sum := by decide
  have hdescent : baseEnd_6965390 < baseStart_6965390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965392 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_6965392 : Nat := 118140960795 + 6965392 * 2 ^ 59
def prefixEnd_6965392 : Nat := 4983230072969 + 3 ^ 40 * 6965392 * 2
def baseEnd_6965392 : Nat := 3576594042981917105466751

theorem tailTrace_6965392 : CollatzResearch.WordTrace tailWord_6965392 prefixEnd_6965392 3576594042981917105466751 := by
  unfold tailWord_6965392
  simp only [CollatzResearch.WordTrace]
  refine ⟨127024358590790926545137215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169365811454387902060182953 127024358590790926545137215)
  ·
    refine ⟨190536537886186389817705823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127024358590790926545137215 190536537886186389817705823)
    ·
      refine ⟨285804806829279584726558735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190536537886186389817705823 285804806829279584726558735)
      ·
        refine ⟨428707210243919377089838103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285804806829279584726558735 428707210243919377089838103)
        ·
          refine ⟨643060815365879065634757155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428707210243919377089838103 643060815365879065634757155)
          ·
            refine ⟨964591223048818598452135733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643060815365879065634757155 964591223048818598452135733)
            ·
              refine ⟨90430427160826743604887725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 964591223048818598452135733 90430427160826743604887725)
              ·
                refine ⟨33911410185310028851832897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90430427160826743604887725 33911410185310028851832897)
                ·
                  refine ⟨25433557638982521638874673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33911410185310028851832897 25433557638982521638874673)
                  ·
                    refine ⟨19075168229236891229156005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25433557638982521638874673 19075168229236891229156005)
                    ·
                      refine ⟨3576594042981917105466751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19075168229236891229156005 3576594042981917105466751)
                      ·
                        rfl

theorem cell23_6965392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_6965392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965392 prefixEnd_6965392 := by exact prefixLift 6965392
  have htrace : WordTrace (prefixWord ++ tailWord_6965392) baseStart_6965392 baseEnd_6965392 := by
    simpa [prefixWord, tailWord_6965392, baseEnd_6965392] using wordTrace_append hprefix tailTrace_6965392
  have hstable : (prefixWord ++ tailWord_6965392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965392).length < 2 ^ (prefixWord ++ tailWord_6965392).sum := by decide
  have hdescent : baseEnd_6965392 < baseStart_6965392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965436 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 7]
def baseStart_6965436 : Nat := 118140960795 + 6965436 * 2 ^ 59
def prefixEnd_6965436 : Nat := 4983230072969 + 3 ^ 40 * 6965436 * 2
def baseEnd_6965436 : Nat := 397401848458968325924061

theorem tailTrace_6965436 : CollatzResearch.WordTrace tailWord_6965436 prefixEnd_6965436 397401848458968325924061 := by
  unfold tailWord_6965436
  simp only [CollatzResearch.WordTrace]
  refine ⟨127025160996711224302438081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169366881328948299069917441 127025160996711224302438081)
  ·
    refine ⟨95268870747533418226828561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127025160996711224302438081 95268870747533418226828561)
    ·
      refine ⟨71451653060650063670121421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95268870747533418226828561 71451653060650063670121421)
      ·
        refine ⟨26794369897743773876295533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71451653060650063670121421 26794369897743773876295533)
        ·
          refine ⟨10047888711653915203610825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26794369897743773876295533 10047888711653915203610825)
          ·
            refine ⟨7535916533740436402708119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10047888711653915203610825 7535916533740436402708119)
            ·
              refine ⟨11303874800610654604062179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535916533740436402708119 11303874800610654604062179)
              ·
                refine ⟨16955812200915981906093269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11303874800610654604062179 16955812200915981906093269)
                ·
                  refine ⟨397401848458968325924061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16955812200915981906093269 397401848458968325924061)
                  ·
                    rfl

theorem cell23_6965436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_6965436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965436 prefixEnd_6965436 := by exact prefixLift 6965436
  have htrace : WordTrace (prefixWord ++ tailWord_6965436) baseStart_6965436 baseEnd_6965436 := by
    simpa [prefixWord, tailWord_6965436, baseEnd_6965436] using wordTrace_append hprefix tailTrace_6965436
  have hstable : (prefixWord ++ tailWord_6965436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965436).length < 2 ^ (prefixWord ++ tailWord_6965436).sum := by decide
  have hdescent : baseEnd_6965436 < baseStart_6965436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965439 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 2, 5, 2]
def baseStart_6965439 : Nat := 118140960795 + 6965439 * 2 ^ 59
def prefixEnd_6965439 : Nat := 4983230072969 + 3 ^ 40 * 6965439 * 2
def baseEnd_6965439 : Nat := 3576618176572678421579035

theorem tailTrace_6965439 : CollatzResearch.WordTrace tailWord_6965439 prefixEnd_6965439 3576618176572678421579035 := by
  unfold tailWord_6965439
  simp only [CollatzResearch.WordTrace]
  refine ⟨254050431412411580117235371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169366954274941053411490247 254050431412411580117235371)
  ·
    refine ⟨381075647118617370175853057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254050431412411580117235371 381075647118617370175853057)
    ·
      refine ⟨285806735338963027631889793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381075647118617370175853057 285806735338963027631889793)
      ·
        refine ⟨214355051504222270723917345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285806735338963027631889793 214355051504222270723917345)
        ·
          refine ⟨160766288628166703042938009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214355051504222270723917345 160766288628166703042938009)
          ·
            refine ⟨120574716471125027282203507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160766288628166703042938009 120574716471125027282203507)
            ·
              refine ⟨180862074706687540923305261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120574716471125027282203507 180862074706687540923305261)
              ·
                refine ⟨67823278015007827846239473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180862074706687540923305261 67823278015007827846239473)
                ·
                  refine ⟨50867458511255870884679605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67823278015007827846239473 50867458511255870884679605)
                  ·
                    refine ⟨4768824235430237895438713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50867458511255870884679605 4768824235430237895438713)
                    ·
                      refine ⟨3576618176572678421579035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768824235430237895438713 3576618176572678421579035)
                      ·
                        rfl

theorem cell23_6965439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_6965439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965439 prefixEnd_6965439 := by exact prefixLift 6965439
  have htrace : WordTrace (prefixWord ++ tailWord_6965439) baseStart_6965439 baseEnd_6965439 := by
    simpa [prefixWord, tailWord_6965439, baseEnd_6965439] using wordTrace_append hprefix tailTrace_6965439
  have hstable : (prefixWord ++ tailWord_6965439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965439).length < 2 ^ (prefixWord ++ tailWord_6965439).sum := by decide
  have hdescent : baseEnd_6965439 < baseStart_6965439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965486 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_6965486 : Nat := 118140960795 + 6965486 * 2 ^ 59
def prefixEnd_6965486 : Nat := 4983230072969 + 3 ^ 40 * 6965486 * 2
def baseEnd_6965486 : Nat := 3576642310163439737691319

theorem tailTrace_6965486 : CollatzResearch.WordTrace tailWord_6965486 prefixEnd_6965486 3576642310163439737691319 := by
  unfold tailWord_6965486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31756518205405163393024539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169368097095494204762797541 31756518205405163393024539)
  ·
    refine ⟨47634777308107745089536809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31756518205405163393024539 47634777308107745089536809)
    ·
      refine ⟨35726082981080808817152607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47634777308107745089536809 35726082981080808817152607)
      ·
        refine ⟨53589124471621213225728911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726082981080808817152607 53589124471621213225728911)
        ·
          refine ⟨80383686707431819838593367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53589124471621213225728911 80383686707431819838593367)
          ·
            refine ⟨120575530061147729757890051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80383686707431819838593367 120575530061147729757890051)
            ·
              refine ⟨180863295091721594636835077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120575530061147729757890051 180863295091721594636835077)
              ·
                refine ⟨33911867829697798994406577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180863295091721594636835077 33911867829697798994406577)
                ·
                  refine ⟨25433900872273349245804933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33911867829697798994406577 25433900872273349245804933)
                  ·
                    refine ⟨4768856413551252983588425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25433900872273349245804933 4768856413551252983588425)
                    ·
                      refine ⟨3576642310163439737691319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768856413551252983588425 3576642310163439737691319)
                      ·
                        rfl

theorem cell23_6965486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_6965486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965486 prefixEnd_6965486 := by exact prefixLift 6965486
  have htrace : WordTrace (prefixWord ++ tailWord_6965486) baseStart_6965486 baseEnd_6965486 := by
    simpa [prefixWord, tailWord_6965486, baseEnd_6965486] using wordTrace_append hprefix tailTrace_6965486
  have hstable : (prefixWord ++ tailWord_6965486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965486).length < 2 ^ (prefixWord ++ tailWord_6965486).sum := by decide
  have hdescent : baseEnd_6965486 < baseStart_6965486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965530 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_6965530 : Nat := 118140960795 + 6965530 * 2 ^ 59
def prefixEnd_6965530 : Nat := 4983230072969 + 3 ^ 40 * 6965530 * 2
def baseEnd_6965530 : Nat := 1192221634437412521847039

theorem tailTrace_6965530 : CollatzResearch.WordTrace tailWord_6965530 prefixEnd_6965530 1192221634437412521847039 := by
  unfold tailWord_6965530
  simp only [CollatzResearch.WordTrace]
  refine ⟨63513437613770475664699511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169369166970054601772532029 63513437613770475664699511)
  ·
    refine ⟨95270156420655713497049267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63513437613770475664699511 95270156420655713497049267)
    ·
      refine ⟨142905234630983570245573901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95270156420655713497049267 142905234630983570245573901)
      ·
        refine ⟨53589462986618838842090213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142905234630983570245573901 53589462986618838842090213)
        ·
          refine ⟨10048024309991032282891915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53589462986618838842090213 10048024309991032282891915)
          ·
            refine ⟨15072036464986548424337873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048024309991032282891915 15072036464986548424337873)
            ·
              refine ⟨11304027348739911318253405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15072036464986548424337873 11304027348739911318253405)
              ·
                refine ⟨4239010255777466744345027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11304027348739911318253405 4239010255777466744345027)
                ·
                  refine ⟨6358515383666200116517541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239010255777466744345027 6358515383666200116517541)
                  ·
                    refine ⟨1192221634437412521847039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358515383666200116517541 1192221634437412521847039)
                    ·
                      rfl

theorem cell23_6965530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_6965530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965530 prefixEnd_6965530 := by exact prefixLift 6965530
  have htrace : WordTrace (prefixWord ++ tailWord_6965530) baseStart_6965530 baseEnd_6965530 := by
    simpa [prefixWord, tailWord_6965530, baseEnd_6965530] using wordTrace_append hprefix tailTrace_6965530
  have hstable : (prefixWord ++ tailWord_6965530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965530).length < 2 ^ (prefixWord ++ tailWord_6965530).sum := by decide
  have hdescent : baseEnd_6965530 < baseStart_6965530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965559 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_6965559 : Nat := 118140960795 + 6965559 * 2 ^ 59
def prefixEnd_6965559 : Nat := 4983230072969 + 3 ^ 40 * 6965559 * 2
def baseEnd_6965559 : Nat := 3576679794251217952078483

theorem tailTrace_6965559 : CollatzResearch.WordTrace tailWord_6965559 prefixEnd_6965559 3576679794251217952078483 := by
  unfold tailWord_6965559
  simp only [CollatzResearch.WordTrace]
  refine ⟨254054808171976840611603731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169369872114651227074402487 254054808171976840611603731)
  ·
    refine ⟨381082212257965260917405597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254054808171976840611603731 381082212257965260917405597)
    ·
      refine ⟨142905829596736972844027099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381082212257965260917405597 142905829596736972844027099)
      ·
        refine ⟨214358744395105459266040649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142905829596736972844027099 214358744395105459266040649)
        ·
          refine ⟨160769058296329094449530487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214358744395105459266040649 160769058296329094449530487)
          ·
            refine ⟨241153587444493641674295731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160769058296329094449530487 241153587444493641674295731)
            ·
              refine ⟨361730381166740462511443597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241153587444493641674295731 361730381166740462511443597)
              ·
                refine ⟨135648892937527673441791349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361730381166740462511443597 135648892937527673441791349)
                ·
                  refine ⟨12717083712893219385167939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135648892937527673441791349 12717083712893219385167939)
                  ·
                    refine ⟨19075625569339829077751909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12717083712893219385167939 19075625569339829077751909)
                    ·
                      refine ⟨3576679794251217952078483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19075625569339829077751909 3576679794251217952078483)
                      ·
                        rfl

theorem cell23_6965559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_6965559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965559 prefixEnd_6965559 := by exact prefixLift 6965559
  have htrace : WordTrace (prefixWord ++ tailWord_6965559) baseStart_6965559 baseEnd_6965559 := by
    simpa [prefixWord, tailWord_6965559, baseEnd_6965559] using wordTrace_append hprefix tailTrace_6965559
  have hstable : (prefixWord ++ tailWord_6965559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965559).length < 2 ^ (prefixWord ++ tailWord_6965559).sum := by decide
  have hdescent : baseEnd_6965559 < baseStart_6965559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965576 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_6965576 : Nat := 118140960795 + 6965576 * 2 ^ 59
def prefixEnd_6965576 : Nat := 4983230072969 + 3 ^ 40 * 6965576 * 2
def baseEnd_6965576 : Nat := 3576688523422344385565905

theorem tailTrace_6965576 : CollatzResearch.WordTrace tailWord_6965576 prefixEnd_6965576 3576688523422344385565905 := by
  unfold tailWord_6965576
  simp only [CollatzResearch.WordTrace]
  refine ⟨127027714106457626257486291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169370285475276835009981721 127027714106457626257486291)
  ·
    refine ⟨190541571159686439386229437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127027714106457626257486291 190541571159686439386229437)
    ·
      refine ⟨71453089184882414769836039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190541571159686439386229437 71453089184882414769836039)
      ·
        refine ⟨107179633777323622154754059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71453089184882414769836039 107179633777323622154754059)
        ·
          refine ⟨160769450665985433232131089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107179633777323622154754059 160769450665985433232131089)
          ·
            refine ⟨120577087999489074924098317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160769450665985433232131089 120577087999489074924098317)
            ·
              refine ⟨45216407999808403096536869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120577087999489074924098317 45216407999808403096536869)
              ·
                refine ⟨8478076499964075580600663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45216407999808403096536869 8478076499964075580600663)
                ·
                  refine ⟨12717114749946113370900995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478076499964075580600663 12717114749946113370900995)
                  ·
                    refine ⟨19075672124919170056351493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12717114749946113370900995 19075672124919170056351493)
                    ·
                      refine ⟨3576688523422344385565905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19075672124919170056351493 3576688523422344385565905)
                      ·
                        rfl

theorem cell23_6965576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_6965576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965576 prefixEnd_6965576 := by exact prefixLift 6965576
  have htrace : WordTrace (prefixWord ++ tailWord_6965576) baseStart_6965576 baseEnd_6965576 := by
    simpa [prefixWord, tailWord_6965576, baseEnd_6965576] using wordTrace_append hprefix tailTrace_6965576
  have hstable : (prefixWord ++ tailWord_6965576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965576).length < 2 ^ (prefixWord ++ tailWord_6965576).sum := by decide
  have hdescent : baseEnd_6965576 < baseStart_6965576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965586 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_6965586 : Nat := 118140960795 + 6965586 * 2 ^ 59
def prefixEnd_6965586 : Nat := 4983230072969 + 3 ^ 40 * 6965586 * 2
def baseEnd_6965586 : Nat := 1192231219409629782146953

theorem tailTrace_6965586 : CollatzResearch.WordTrace tailWord_6965586 prefixEnd_6965586 1192231219409629782146953 := by
  unfold tailWord_6965586
  simp only [CollatzResearch.WordTrace]
  refine ⟨63513948235719756055709153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169370528628586016148557741 63513948235719756055709153)
  ·
    refine ⟨47635461176789817041781865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63513948235719756055709153 47635461176789817041781865)
    ·
      refine ⟨35726595882592362781336399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47635461176789817041781865 35726595882592362781336399)
      ·
        refine ⟨53589893823888544172004599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726595882592362781336399 53589893823888544172004599)
        ·
          refine ⟨80384840735832816258006899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53589893823888544172004599 80384840735832816258006899)
          ·
            refine ⟨120577261103749224387010349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80384840735832816258006899 120577261103749224387010349)
            ·
              refine ⟨45216472913905959145128881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120577261103749224387010349 45216472913905959145128881)
              ·
                refine ⟨33912354685429469358846661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45216472913905959145128881 33912354685429469358846661)
                ·
                  refine ⟨6358566503518025504783749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33912354685429469358846661 6358566503518025504783749)
                  ·
                    refine ⟨1192231219409629782146953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358566503518025504783749 1192231219409629782146953)
                    ·
                      rfl

theorem cell23_6965586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_6965586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965586 prefixEnd_6965586 := by exact prefixLift 6965586
  have htrace : WordTrace (prefixWord ++ tailWord_6965586) baseStart_6965586 baseEnd_6965586 := by
    simpa [prefixWord, tailWord_6965586, baseEnd_6965586] using wordTrace_append hprefix tailTrace_6965586
  have hstable : (prefixWord ++ tailWord_6965586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965586).length < 2 ^ (prefixWord ++ tailWord_6965586).sum := by decide
  have hdescent : baseEnd_6965586 < baseStart_6965586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965598 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6965598 : Nat := 118140960795 + 6965598 * 2 ^ 59
def prefixEnd_6965598 : Nat := 4983230072969 + 3 ^ 40 * 6965598 * 2
def baseEnd_6965598 : Nat := 1192233273332247766496935

theorem tailTrace_6965598 : CollatzResearch.WordTrace tailWord_6965598 prefixEnd_6965598 1192233273332247766496935 := by
  unfold tailWord_6965598
  simp only [CollatzResearch.WordTrace]
  refine ⟨31757028827354443784034181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169370820412557033514848965 31757028827354443784034181)
  ·
    refine ⟨5954442905128958209506409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31757028827354443784034181 5954442905128958209506409)
    ·
      refine ⟨4465832178846718657129807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5954442905128958209506409 4465832178846718657129807)
      ·
        refine ⟨6698748268270077985694711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465832178846718657129807 6698748268270077985694711)
        ·
          refine ⟨10048122402405116978542067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698748268270077985694711 10048122402405116978542067)
          ·
            refine ⟨15072183603607675467813101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048122402405116978542067 15072183603607675467813101)
            ·
              refine ⟨5652068851352878300429913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15072183603607675467813101 5652068851352878300429913)
              ·
                refine ⟨4239051638514658725322435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5652068851352878300429913 4239051638514658725322435)
                ·
                  refine ⟨6358577457771988087983653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239051638514658725322435 6358577457771988087983653)
                  ·
                    refine ⟨1192233273332247766496935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358577457771988087983653 1192233273332247766496935)
                    ·
                      rfl

theorem cell23_6965598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6965598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965598 prefixEnd_6965598 := by exact prefixLift 6965598
  have htrace : WordTrace (prefixWord ++ tailWord_6965598) baseStart_6965598 baseEnd_6965598 := by
    simpa [prefixWord, tailWord_6965598, baseEnd_6965598] using wordTrace_append hprefix tailTrace_6965598
  have hstable : (prefixWord ++ tailWord_6965598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965598).length < 2 ^ (prefixWord ++ tailWord_6965598).sum := by decide
  have hdescent : baseEnd_6965598 < baseStart_6965598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965649 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_6965649 : Nat := 118140960795 + 6965649 * 2 ^ 59
def prefixEnd_6965649 : Nat := 4983230072969 + 3 ^ 40 * 6965649 * 2
def baseEnd_6965649 : Nat := 3576726007510122599953069

theorem tailTrace_6965649 : CollatzResearch.WordTrace tailWord_6965649 prefixEnd_6965649 3576726007510122599953069 := by
  unfold tailWord_6965649
  simp only [CollatzResearch.WordTrace]
  refine ⟨254058090741650785982380001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169372060494433857321586667 254058090741650785982380001)
  ·
    refine ⟨190543568056238089486785001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254058090741650785982380001 190543568056238089486785001)
    ·
      refine ⟨142907676042178567115088751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190543568056238089486785001 142907676042178567115088751)
      ·
        refine ⟨214361514063267850672633127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142907676042178567115088751 214361514063267850672633127)
        ·
          refine ⟨321542271094901776008949691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214361514063267850672633127 321542271094901776008949691)
          ·
            refine ⟨482313406642352664013424537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321542271094901776008949691 482313406642352664013424537)
            ·
              refine ⟨361735054981764498010068403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482313406642352664013424537 361735054981764498010068403)
              ·
                refine ⟨542602582472646747015102605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361735054981764498010068403 542602582472646747015102605)
                ·
                  refine ⟨203475968427242530130663477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542602582472646747015102605 203475968427242530130663477)
                  ·
                    refine ⟨19075872040053987199749701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203475968427242530130663477 19075872040053987199749701)
                    ·
                      refine ⟨3576726007510122599953069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19075872040053987199749701 3576726007510122599953069)
                      ·
                        rfl

theorem cell23_6965649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_6965649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965649 prefixEnd_6965649 := by exact prefixLift 6965649
  have htrace : WordTrace (prefixWord ++ tailWord_6965649) baseStart_6965649 baseEnd_6965649 := by
    simpa [prefixWord, tailWord_6965649, baseEnd_6965649] using wordTrace_append hprefix tailTrace_6965649
  have hstable : (prefixWord ++ tailWord_6965649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965649).length < 2 ^ (prefixWord ++ tailWord_6965649).sum := by decide
  have hdescent : baseEnd_6965649 < baseStart_6965649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965661 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_6965661 : Nat := 118140960795 + 6965661 * 2 ^ 59
def prefixEnd_6965661 : Nat := 4983230072969 + 3 ^ 40 * 6965661 * 2
def baseEnd_6965661 : Nat := 3576732169277976553003015

theorem tailTrace_6965661 : CollatzResearch.WordTrace tailWord_6965661 prefixEnd_6965661 3576732169277976553003015 := by
  unfold tailWord_6965661
  simp only [CollatzResearch.WordTrace]
  refine ⟨254058528417607312031816837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169372352278404874687877891 254058528417607312031816837)
  ·
    refine ⟨47635974078301371005965657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254058528417607312031816837 47635974078301371005965657)
    ·
      refine ⟨35726980558726028254474243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47635974078301371005965657 35726980558726028254474243)
      ·
        refine ⟨53590470838089042381711365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726980558726028254474243 53590470838089042381711365)
        ·
          refine ⟨10048213282141695446570881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53590470838089042381711365 10048213282141695446570881)
          ·
            refine ⟨7536159961606271584928161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10048213282141695446570881 7536159961606271584928161)
            ·
              refine ⟨5652119971204703688696121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536159961606271584928161 5652119971204703688696121)
              ·
                refine ⟨4239089978403527766522091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5652119971204703688696121 4239089978403527766522091)
                ·
                  refine ⟨6358634967605291649783137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239089978403527766522091 6358634967605291649783137)
                  ·
                    refine ⟨4768976225703968737337353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358634967605291649783137 4768976225703968737337353)
                    ·
                      refine ⟨3576732169277976553003015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768976225703968737337353 3576732169277976553003015)
                      ·
                        rfl

theorem cell23_6965661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_6965661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965661 prefixEnd_6965661 := by exact prefixLift 6965661
  have htrace : WordTrace (prefixWord ++ tailWord_6965661) baseStart_6965661 baseEnd_6965661 := by
    simpa [prefixWord, tailWord_6965661, baseEnd_6965661] using wordTrace_append hprefix tailTrace_6965661
  have hstable : (prefixWord ++ tailWord_6965661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965661).length < 2 ^ (prefixWord ++ tailWord_6965661).sum := by decide
  have hdescent : baseEnd_6965661 < baseStart_6965661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965666 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6965666 : Nat := 118140960795 + 6965666 * 2 ^ 59
def prefixEnd_6965666 : Nat := 4983230072969 + 3 ^ 40 * 6965666 * 2
def baseEnd_6965666 : Nat := 3576734736681249033440491

theorem tailTrace_6965666 : CollatzResearch.WordTrace tailWord_6965666 prefixEnd_6965666 3576734736681249033440491 := by
  unfold tailWord_6965666
  simp only [CollatzResearch.WordTrace]
  refine ⟨63514677695647299471437213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169372473855059465257165901 63514677695647299471437213)
  ·
    refine ⟨23818004135867737301788955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63514677695647299471437213 23818004135867737301788955)
    ·
      refine ⟨35727006203801605952683433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23818004135867737301788955 35727006203801605952683433)
      ·
        refine ⟨26795254652851204464512575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35727006203801605952683433 26795254652851204464512575)
        ·
          refine ⟨40192881979276806696768863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26795254652851204464512575 40192881979276806696768863)
          ·
            refine ⟨60289322968915210045153295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40192881979276806696768863 60289322968915210045153295)
            ·
              refine ⟨90433984453372815067729943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60289322968915210045153295 90433984453372815067729943)
              ·
                refine ⟨135650976680059222601594915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90433984453372815067729943 135650976680059222601594915)
                ·
                  refine ⟨203476465020088833902392373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135650976680059222601594915 203476465020088833902392373)
                  ·
                    refine ⟨19075918595633328178349285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203476465020088833902392373 19075918595633328178349285)
                    ·
                      refine ⟨3576734736681249033440491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19075918595633328178349285 3576734736681249033440491)
                      ·
                        rfl

theorem cell23_6965666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6965666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965666 prefixEnd_6965666 := by exact prefixLift 6965666
  have htrace : WordTrace (prefixWord ++ tailWord_6965666) baseStart_6965666 baseEnd_6965666 := by
    simpa [prefixWord, tailWord_6965666, baseEnd_6965666] using wordTrace_append hprefix tailTrace_6965666
  have hstable : (prefixWord ++ tailWord_6965666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965666).length < 2 ^ (prefixWord ++ tailWord_6965666).sum := by decide
  have hdescent : baseEnd_6965666 < baseStart_6965666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965683 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 8, 2, 2]
def baseStart_6965683 : Nat := 118140960795 + 6965683 * 2 ^ 59
def prefixEnd_6965683 : Nat := 4983230072969 + 3 ^ 40 * 6965683 * 2
def baseEnd_6965683 : Nat := 3576743465852375466927913

theorem tailTrace_6965683 : CollatzResearch.WordTrace tailWord_6965683 prefixEnd_6965683 3576743465852375466927913 := by
  unfold tailWord_6965683
  simp only [CollatzResearch.WordTrace]
  refine ⟨254059330823527609789117703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169372887215685073192745135 254059330823527609789117703)
  ·
    refine ⟨381088996235291414683676555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254059330823527609789117703 381088996235291414683676555)
    ·
      refine ⟨571633494352937122025514833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381088996235291414683676555 571633494352937122025514833)
      ·
        refine ⟨428725120764702841519136125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571633494352937122025514833 428725120764702841519136125)
        ·
          refine ⟨160771920286763565569676047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428725120764702841519136125 160771920286763565569676047)
          ·
            refine ⟨241157880430145348354514071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160771920286763565569676047 241157880430145348354514071)
            ·
              refine ⟨361736820645218022531771107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241157880430145348354514071 361736820645218022531771107)
              ·
                refine ⟨542605230967827033797656661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361736820645218022531771107 542605230967827033797656661)
                ·
                  refine ⟨6358655050404223052316289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 542605230967827033797656661 6358655050404223052316289)
                  ·
                    refine ⟨4768991287803167289237217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358655050404223052316289 4768991287803167289237217)
                    ·
                      refine ⟨3576743465852375466927913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4768991287803167289237217 3576743465852375466927913)
                      ·
                        rfl

theorem cell23_6965683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 2, 2].length) (baseStart_6965683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965683 prefixEnd_6965683 := by exact prefixLift 6965683
  have htrace : WordTrace (prefixWord ++ tailWord_6965683) baseStart_6965683 baseEnd_6965683 := by
    simpa [prefixWord, tailWord_6965683, baseEnd_6965683] using wordTrace_append hprefix tailTrace_6965683
  have hstable : (prefixWord ++ tailWord_6965683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965683).length < 2 ^ (prefixWord ++ tailWord_6965683).sum := by decide
  have hdescent : baseEnd_6965683 < baseStart_6965683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965699 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_6965699 : Nat := 118140960795 + 6965699 * 2 ^ 59
def prefixEnd_6965699 : Nat := 4983230072969 + 3 ^ 40 * 6965699 * 2
def baseEnd_6965699 : Nat := 3576751681542847404327839

theorem tailTrace_6965699 : CollatzResearch.WordTrace tailWord_6965699 prefixEnd_6965699 3576751681542847404327839 := by
  unfold tailWord_6965699
  simp only [CollatzResearch.WordTrace]
  refine ⟨254059914391469644521700151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169373276260979763014466767 254059914391469644521700151)
  ·
    refine ⟨381089871587204466782550227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254059914391469644521700151 381089871587204466782550227)
    ·
      refine ⟨571634807380806700173825341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381089871587204466782550227 571634807380806700173825341)
      ·
        refine ⟨214363052767802512565184503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571634807380806700173825341 214363052767802512565184503)
        ·
          refine ⟨321544579151703768847776755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214363052767802512565184503 321544579151703768847776755)
          ·
            refine ⟨482316868727555653271665133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321544579151703768847776755 482316868727555653271665133)
            ·
              refine ⟨180868825772833369976874425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482316868727555653271665133 180868825772833369976874425)
              ·
                refine ⟨135651619329625027482655819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180868825772833369976874425 135651619329625027482655819)
                ·
                  refine ⟨203477428994437541223983729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135651619329625027482655819 203477428994437541223983729)
                  ·
                    refine ⟨152608071745828155917987797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203477428994437541223983729 152608071745828155917987797)
                    ·
                      refine ⟨3576751681542847404327839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152608071745828155917987797 3576751681542847404327839)
                      ·
                        rfl

theorem cell23_6965699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_6965699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965699 prefixEnd_6965699 := by exact prefixLift 6965699
  have htrace : WordTrace (prefixWord ++ tailWord_6965699) baseStart_6965699 baseEnd_6965699 := by
    simpa [prefixWord, tailWord_6965699, baseEnd_6965699] using wordTrace_append hprefix tailTrace_6965699
  have hstable : (prefixWord ++ tailWord_6965699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965699).length < 2 ^ (prefixWord ++ tailWord_6965699).sum := by decide
  have hdescent : baseEnd_6965699 < baseStart_6965699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965717 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6965717 : Nat := 118140960795 + 6965717 * 2 ^ 59
def prefixEnd_6965717 : Nat := 4983230072969 + 3 ^ 40 * 6965717 * 2
def baseEnd_6965717 : Nat := 3576760924194628333902757

theorem tailTrace_6965717 : CollatzResearch.WordTrace tailWord_6965717 prefixEnd_6965717 3576760924194628333902757 := by
  unfold tailWord_6965717
  simp only [CollatzResearch.WordTrace]
  refine ⟨254060570905404433595855405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169373713936936289063903603 254060570905404433595855405)
  ·
    refine ⟨95272714089526662598445777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254060570905404433595855405 95272714089526662598445777)
    ·
      refine ⟨71454535567144996948834333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95272714089526662598445777 71454535567144996948834333)
      ·
        refine ⟨26795450837679373855812875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71454535567144996948834333 26795450837679373855812875)
        ·
          refine ⟨40193176256519060783719313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26795450837679373855812875 40193176256519060783719313)
          ·
            refine ⟨30144882192389295587789485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40193176256519060783719313 30144882192389295587789485)
            ·
              refine ⟨11304330822145985845421057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30144882192389295587789485 11304330822145985845421057)
              ·
                refine ⟨8478248116609489384065793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11304330822145985845421057 8478248116609489384065793)
                ·
                  refine ⟨6358686087457117038049345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8478248116609489384065793 6358686087457117038049345)
                  ·
                    refine ⟨4769014565592837778537009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358686087457117038049345 4769014565592837778537009)
                    ·
                      refine ⟨3576760924194628333902757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769014565592837778537009 3576760924194628333902757)
                      ·
                        rfl

theorem cell23_6965717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6965717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965717 prefixEnd_6965717 := by exact prefixLift 6965717
  have htrace : WordTrace (prefixWord ++ tailWord_6965717) baseStart_6965717 baseEnd_6965717 := by
    simpa [prefixWord, tailWord_6965717, baseEnd_6965717] using wordTrace_append hprefix tailTrace_6965717
  have hstable : (prefixWord ++ tailWord_6965717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965717).length < 2 ^ (prefixWord ++ tailWord_6965717).sum := by decide
  have hdescent : baseEnd_6965717 < baseStart_6965717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965736 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_6965736 : Nat := 118140960795 + 6965736 * 2 ^ 59
def prefixEnd_6965736 : Nat := 4983230072969 + 3 ^ 40 * 6965736 * 2
def baseEnd_6965736 : Nat := 1192256893442354586521723

theorem tailTrace_6965736 : CollatzResearch.WordTrace tailWord_6965736 prefixEnd_6965736 1192256893442354586521723 := by
  unfold tailWord_6965736
  simp only [CollatzResearch.WordTrace]
  refine ⟨127030631946167799920398531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169374175928223733227198041 127030631946167799920398531)
  ·
    refine ⟨190545947919251699880597797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127030631946167799920398531 190545947919251699880597797)
    ·
      refine ⟨35727365234859693727612087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190545947919251699880597797 35727365234859693727612087)
      ·
        refine ⟨53591047852289540591418131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35727365234859693727612087 53591047852289540591418131)
        ·
          refine ⟨80386571778434310887127197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53591047852289540591418131 80386571778434310887127197)
          ·
            refine ⟨30144964416912866582672699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80386571778434310887127197 30144964416912866582672699)
            ·
              refine ⟨45217446625369299874009049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30144964416912866582672699 45217446625369299874009049)
              ·
                refine ⟨33913084969026974905506787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45217446625369299874009049 33913084969026974905506787)
                ·
                  refine ⟨50869627453540462358260181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33913084969026974905506787 50869627453540462358260181)
                  ·
                    refine ⟨1192256893442354586521723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50869627453540462358260181 1192256893442354586521723)
                    ·
                      rfl

theorem cell23_6965736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_6965736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965736 prefixEnd_6965736 := by exact prefixLift 6965736
  have htrace : WordTrace (prefixWord ++ tailWord_6965736) baseStart_6965736 baseEnd_6965736 := by
    simpa [prefixWord, tailWord_6965736, baseEnd_6965736] using wordTrace_append hprefix tailTrace_6965736
  have hstable : (prefixWord ++ tailWord_6965736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965736).length < 2 ^ (prefixWord ++ tailWord_6965736).sum := by decide
  have hdescent : baseEnd_6965736 < baseStart_6965736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965780 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6965780 : Nat := 118140960795 + 6965780 * 2 ^ 59
def prefixEnd_6965780 : Nat := 4983230072969 + 3 ^ 40 * 6965780 * 2
def baseEnd_6965780 : Nat := 3576793273475861587414967

theorem tailTrace_6965780 : CollatzResearch.WordTrace tailWord_6965780 prefixEnd_6965780 3576793273475861587414967 := by
  unfold tailWord_6965780
  simp only [CollatzResearch.WordTrace]
  refine ⟨127031434352088097677699397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169375245802784130236932529 127031434352088097677699397)
  ·
    refine ⟨23818393941016518314568637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127031434352088097677699397 23818393941016518314568637)
    ·
      refine ⟨8931897727881194367963239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23818393941016518314568637 8931897727881194367963239)
      ·
        refine ⟨13397846591821791551944859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8931897727881194367963239 13397846591821791551944859)
        ·
          refine ⟨20096769887732687327917289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13397846591821791551944859 20096769887732687327917289)
          ·
            refine ⟨15072577415799515495937967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20096769887732687327917289 15072577415799515495937967)
            ·
              refine ⟨22608866123699273243906951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072577415799515495937967 22608866123699273243906951)
              ·
                refine ⟨33913299185548909865860427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22608866123699273243906951 33913299185548909865860427)
                ·
                  refine ⟨50869948778323364798790641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33913299185548909865860427 50869948778323364798790641)
                  ·
                    refine ⟨38152461583742523599092981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50869948778323364798790641 38152461583742523599092981)
                    ·
                      refine ⟨3576793273475861587414967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38152461583742523599092981 3576793273475861587414967)
                      ·
                        rfl

theorem cell23_6965780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6965780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965780 prefixEnd_6965780 := by exact prefixLift 6965780
  have htrace : WordTrace (prefixWord ++ tailWord_6965780) baseStart_6965780 baseEnd_6965780 := by
    simpa [prefixWord, tailWord_6965780, baseEnd_6965780] using wordTrace_append hprefix tailTrace_6965780
  have hstable : (prefixWord ++ tailWord_6965780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965780).length < 2 ^ (prefixWord ++ tailWord_6965780).sum := by decide
  have hdescent : baseEnd_6965780 < baseStart_6965780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965786 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_6965786 : Nat := 118140960795 + 6965786 * 2 ^ 59
def prefixEnd_6965786 : Nat := 4983230072969 + 3 ^ 40 * 6965786 * 2
def baseEnd_6965786 : Nat := 3576796354359788563939939

theorem tailTrace_6965786 : CollatzResearch.WordTrace tailWord_6965786 prefixEnd_6965786 3576796354359788563939939 := by
  unfold tailWord_6965786
  simp only [CollatzResearch.WordTrace]
  refine ⟨63515771885538614595029303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169375391694769638920078141 63515771885538614595029303)
  ·
    refine ⟨95273657828307921892543955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63515771885538614595029303 95273657828307921892543955)
    ·
      refine ⟨142910486742461882838815933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95273657828307921892543955 142910486742461882838815933)
      ·
        refine ⟨53591432528423206064555975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142910486742461882838815933 53591432528423206064555975)
        ·
          refine ⟨80387148792634809096833963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53591432528423206064555975 80387148792634809096833963)
          ·
            refine ⟨120580723188952213645250945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80387148792634809096833963 120580723188952213645250945)
            ·
              refine ⟨90435542391714160233938209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120580723188952213645250945 90435542391714160233938209)
              ·
                refine ⟨67826656793785620175453657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90435542391714160233938209 67826656793785620175453657)
                ·
                  refine ⟨50869992595339215131590243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67826656793785620175453657 50869992595339215131590243)
                  ·
                    refine ⟨76304988893008822697385365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50869992595339215131590243 76304988893008822697385365)
                    ·
                      refine ⟨3576796354359788563939939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76304988893008822697385365 3576796354359788563939939)
                      ·
                        rfl

theorem cell23_6965786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_6965786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965786 prefixEnd_6965786 := by exact prefixLift 6965786
  have htrace : WordTrace (prefixWord ++ tailWord_6965786) baseStart_6965786 baseEnd_6965786 := by
    simpa [prefixWord, tailWord_6965786, baseEnd_6965786] using wordTrace_append hprefix tailTrace_6965786
  have hstable : (prefixWord ++ tailWord_6965786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965786).length < 2 ^ (prefixWord ++ tailWord_6965786).sum := by decide
  have hdescent : baseEnd_6965786 < baseStart_6965786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965793 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6965793 : Nat := 118140960795 + 6965793 * 2 ^ 59
def prefixEnd_6965793 : Nat := 4983230072969 + 3 ^ 40 * 6965793 * 2
def baseEnd_6965793 : Nat := 3576799948724370036552407

theorem tailTrace_6965793 : CollatzResearch.WordTrace tailWord_6965793 prefixEnd_6965793 3576799948724370036552407 := by
  unfold tailWord_6965793
  simp only [CollatzResearch.WordTrace]
  refine ⟨254063342853129098575622033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169375561902086065717081355 254063342853129098575622033)
  ·
    refine ⟨190547507139846823931716525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254063342853129098575622033 190547507139846823931716525)
    ·
      refine ⟨71455315177442558974393697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190547507139846823931716525 71455315177442558974393697)
      ·
        refine ⟨53591486383081919230795273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71455315177442558974393697 53591486383081919230795273)
        ·
          refine ⟨40193614787311439423096455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53591486383081919230795273 40193614787311439423096455)
          ·
            refine ⟨60290422180967159134644683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40193614787311439423096455 60290422180967159134644683)
            ·
              refine ⟨90435633271450738701967025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60290422180967159134644683 90435633271450738701967025)
              ·
                refine ⟨67826724953588054026475269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90435633271450738701967025 67826724953588054026475269)
                ·
                  refine ⟨12717510928797760129964113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67826724953588054026475269 12717510928797760129964113)
                  ·
                    refine ⟨9538133196598320097473085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12717510928797760129964113 9538133196598320097473085)
                    ·
                      refine ⟨3576799948724370036552407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9538133196598320097473085 3576799948724370036552407)
                      ·
                        rfl

theorem cell23_6965793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6965793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965793 prefixEnd_6965793 := by exact prefixLift 6965793
  have htrace : WordTrace (prefixWord ++ tailWord_6965793) baseStart_6965793 baseEnd_6965793 := by
    simpa [prefixWord, tailWord_6965793, baseEnd_6965793] using wordTrace_append hprefix tailTrace_6965793
  have hstable : (prefixWord ++ tailWord_6965793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965793).length < 2 ^ (prefixWord ++ tailWord_6965793).sum := by decide
  have hdescent : baseEnd_6965793 < baseStart_6965793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965833 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 5, 5, 2]
def baseStart_6965833 : Nat := 118140960795 + 6965833 * 2 ^ 59
def prefixEnd_6965833 : Nat := 4983230072969 + 3 ^ 40 * 6965833 * 2
def baseEnd_6965833 : Nat := 3576820487950549880052223

theorem tailTrace_6965833 : CollatzResearch.WordTrace tailWord_6965833 prefixEnd_6965833 3576820487950549880052223 := by
  unfold tailWord_6965833
  simp only [CollatzResearch.WordTrace]
  refine ⟨254064801772984185407078153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169376534515322790271385435 254064801772984185407078153)
  ·
    refine ⟨190548601329738139055308615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254064801772984185407078153 190548601329738139055308615)
    ·
      refine ⟨285822901994607208582962923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190548601329738139055308615 285822901994607208582962923)
      ·
        refine ⟨428734352991910812874444385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285822901994607208582962923 428734352991910812874444385)
        ·
          refine ⟨321550764743933109655833289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428734352991910812874444385 321550764743933109655833289)
          ·
            refine ⟨241163073557949832241874967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321550764743933109655833289 241163073557949832241874967)
            ·
              refine ⟨361744610336924748362812451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241163073557949832241874967 361744610336924748362812451)
              ·
                refine ⟨542616915505387122544218677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361744610336924748362812451 542616915505387122544218677)
                ·
                  refine ⟨50870335828630042738520501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 542616915505387122544218677 50870335828630042738520501)
                  ·
                    refine ⟨4769093983934066506736297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50870335828630042738520501 4769093983934066506736297)
                    ·
                      refine ⟨3576820487950549880052223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769093983934066506736297 3576820487950549880052223)
                      ·
                        rfl

theorem cell23_6965833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 5, 2].length) (baseStart_6965833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965833 prefixEnd_6965833 := by exact prefixLift 6965833
  have htrace : WordTrace (prefixWord ++ tailWord_6965833) baseStart_6965833 baseEnd_6965833 := by
    simpa [prefixWord, tailWord_6965833, baseEnd_6965833] using wordTrace_append hprefix tailTrace_6965833
  have hstable : (prefixWord ++ tailWord_6965833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965833).length < 2 ^ (prefixWord ++ tailWord_6965833).sum := by decide
  have hdescent : baseEnd_6965833 < baseStart_6965833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965834 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_6965834 : Nat := 118140960795 + 6965834 * 2 ^ 59
def prefixEnd_6965834 : Nat := 4983230072969 + 3 ^ 40 * 6965834 * 2
def baseEnd_6965834 : Nat := 1192273667143734792046573

theorem tailTrace_6965834 : CollatzResearch.WordTrace tailWord_6965834 prefixEnd_6965834 1192273667143734792046573 := by
  unfold tailWord_6965834
  simp only [CollatzResearch.WordTrace]
  refine ⟨63516209561495140644466139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169376558830653708385243037 63516209561495140644466139)
  ·
    refine ⟨95274314342242710966699209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63516209561495140644466139 95274314342242710966699209)
    ·
      refine ⟨71455735756682033225024407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95274314342242710966699209 71455735756682033225024407)
      ·
        refine ⟨107183603635023049837536611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71455735756682033225024407 107183603635023049837536611)
        ·
          refine ⟨160775405452534574756304917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107183603635023049837536611 160775405452534574756304917)
          ·
            refine ⟨7536347130587558191701793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160775405452534574756304917 7536347130587558191701793)
            ·
              refine ⟨5652260347940668643776345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536347130587558191701793 5652260347940668643776345)
              ·
                refine ⟨4239195260955501482832259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5652260347940668643776345 4239195260955501482832259)
                ·
                  refine ⟨6358792891433252224248389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239195260955501482832259 6358792891433252224248389)
                  ·
                    refine ⟨1192273667143734792046573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358792891433252224248389 1192273667143734792046573)
                    ·
                      rfl

theorem cell23_6965834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_6965834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965834 prefixEnd_6965834 := by exact prefixLift 6965834
  have htrace : WordTrace (prefixWord ++ tailWord_6965834) baseStart_6965834 baseEnd_6965834 := by
    simpa [prefixWord, tailWord_6965834, baseEnd_6965834] using wordTrace_append hprefix tailTrace_6965834
  have hstable : (prefixWord ++ tailWord_6965834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965834).length < 2 ^ (prefixWord ++ tailWord_6965834).sum := by decide
  have hdescent : baseEnd_6965834 < baseStart_6965834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965877 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6965877 : Nat := 118140960795 + 6965877 * 2 ^ 59
def prefixEnd_6965877 : Nat := 4983230072969 + 3 ^ 40 * 6965877 * 2
def baseEnd_6965877 : Nat := 1192281027033115902634007

theorem tailTrace_6965877 : CollatzResearch.WordTrace tailWord_6965877 prefixEnd_6965877 1192281027033115902634007 := by
  unfold tailWord_6965877
  simp only [CollatzResearch.WordTrace]
  refine ⟨254066406584824780921679885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169377604389883187281119923 254066406584824780921679885)
  ·
    refine ⟨95274902469309292845629957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254066406584824780921679885 95274902469309292845629957)
    ·
      refine ⟨17864044212995492408555617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95274902469309292845629957 17864044212995492408555617)
      ·
        refine ⟨13398033159746619306416713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17864044212995492408555617 13398033159746619306416713)
        ·
          refine ⟨10048524869809964479812535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13398033159746619306416713 10048524869809964479812535)
          ·
            refine ⟨15072787304714946719718803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048524869809964479812535 15072787304714946719718803)
            ·
              refine ⟨22609180957072420079578205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072787304714946719718803 22609180957072420079578205)
              ·
                refine ⟨8478442858902157529841827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22609180957072420079578205 8478442858902157529841827)
                ·
                  refine ⟨12717664288353236294762741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478442858902157529841827 12717664288353236294762741)
                  ·
                    refine ⟨1192281027033115902634007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12717664288353236294762741 1192281027033115902634007)
                    ·
                      rfl

theorem cell23_6965877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6965877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965877 prefixEnd_6965877 := by exact prefixLift 6965877
  have htrace : WordTrace (prefixWord ++ tailWord_6965877) baseStart_6965877 baseEnd_6965877 := by
    simpa [prefixWord, tailWord_6965877, baseEnd_6965877] using wordTrace_append hprefix tailTrace_6965877
  have hstable : (prefixWord ++ tailWord_6965877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965877).length < 2 ^ (prefixWord ++ tailWord_6965877).sum := by decide
  have hdescent : baseEnd_6965877 < baseStart_6965877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965883 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 3]
def baseStart_6965883 : Nat := 118140960795 + 6965883 * 2 ^ 59
def prefixEnd_6965883 : Nat := 4983230072969 + 3 ^ 40 * 6965883 * 2
def baseEnd_6965883 : Nat := 3576846161983274684426993

theorem tailTrace_6965883 : CollatzResearch.WordTrace tailWord_6965883 prefixEnd_6965883 3576846161983274684426993 := by
  unfold tailWord_6965883
  simp only [CollatzResearch.WordTrace]
  refine ⟨254066625422803043946398303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169377750281868695964265535 254066625422803043946398303)
  ·
    refine ⟨381099938134204565919597455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254066625422803043946398303 381099938134204565919597455)
    ·
      refine ⟨571649907201306848879396183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381099938134204565919597455 571649907201306848879396183)
      ·
        refine ⟨857474860801960273319094275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571649907201306848879396183 857474860801960273319094275)
        ·
          refine ⟨1286212291202940409978641413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857474860801960273319094275 1286212291202940409978641413)
          ·
            refine ⟨241164804600551326870995265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1286212291202940409978641413 241164804600551326870995265)
            ·
              refine ⟨180873603450413495153246449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241164804600551326870995265 180873603450413495153246449)
              ·
                refine ⟨135655202587810121364934837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180873603450413495153246449 135655202587810121364934837)
                ·
                  refine ⟨12717675242607198877962641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135655202587810121364934837 12717675242607198877962641)
                  ·
                    refine ⟨9538256431955399158471981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12717675242607198877962641 9538256431955399158471981)
                    ·
                      refine ⟨3576846161983274684426993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9538256431955399158471981 3576846161983274684426993)
                      ·
                        rfl

theorem cell23_6965883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 3].length) (baseStart_6965883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965883 prefixEnd_6965883 := by exact prefixLift 6965883
  have htrace : WordTrace (prefixWord ++ tailWord_6965883) baseStart_6965883 baseEnd_6965883 := by
    simpa [prefixWord, tailWord_6965883, baseEnd_6965883] using wordTrace_append hprefix tailTrace_6965883
  have hstable : (prefixWord ++ tailWord_6965883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965883).length < 2 ^ (prefixWord ++ tailWord_6965883).sum := by decide
  have hdescent : baseEnd_6965883 < baseStart_6965883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965914 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6965914 : Nat := 118140960795 + 6965914 * 2 ^ 59
def prefixEnd_6965914 : Nat := 4983230072969 + 3 ^ 40 * 6965914 * 2
def baseEnd_6965914 : Nat := 3576862079883564063139351

theorem tailTrace_6965914 : CollatzResearch.WordTrace tailWord_6965914 prefixEnd_6965914 3576862079883564063139351 := by
  unfold tailWord_6965914
  simp only [CollatzResearch.WordTrace]
  refine ⟨63516939021422684060194199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169378504057127157493851197 63516939021422684060194199)
  ·
    refine ⟨95275408532134026090291299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63516939021422684060194199 95275408532134026090291299)
    ·
      refine ⟨142913112798201039135436949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95275408532134026090291299 142913112798201039135436949)
      ·
        refine ⟨6699052162415673709473607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142913112798201039135436949 6699052162415673709473607)
        ·
          refine ⟨10048578243623510564210411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6699052162415673709473607 10048578243623510564210411)
          ·
            refine ⟨15072867365435265846315617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048578243623510564210411 15072867365435265846315617)
            ·
              refine ⟨11304650524076449384736713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15072867365435265846315617 11304650524076449384736713)
              ·
                refine ⟨8478487893057337038552535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11304650524076449384736713 8478487893057337038552535)
                ·
                  refine ⟨12717731839586005557828803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478487893057337038552535 12717731839586005557828803)
                  ·
                    refine ⟨19076597759379008336743205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12717731839586005557828803 19076597759379008336743205)
                    ·
                      refine ⟨3576862079883564063139351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19076597759379008336743205 3576862079883564063139351)
                      ·
                        rfl

theorem cell23_6965914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6965914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965914 prefixEnd_6965914 := by exact prefixLift 6965914
  have htrace : WordTrace (prefixWord ++ tailWord_6965914) baseStart_6965914 baseEnd_6965914 := by
    simpa [prefixWord, tailWord_6965914, baseEnd_6965914] using wordTrace_append hprefix tailTrace_6965914
  have hstable : (prefixWord ++ tailWord_6965914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965914).length < 2 ^ (prefixWord ++ tailWord_6965914).sum := by decide
  have hdescent : baseEnd_6965914 < baseStart_6965914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965934 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6965934 : Nat := 118140960795 + 6965934 * 2 ^ 59
def prefixEnd_6965934 : Nat := 4983230072969 + 3 ^ 40 * 6965934 * 2
def baseEnd_6965934 : Nat := 3576872349496653984889259

theorem tailTrace_6965934 : CollatzResearch.WordTrace tailWord_6965934 prefixEnd_6965934 3576872349496653984889259 := by
  unfold tailWord_6965934
  simp only [CollatzResearch.WordTrace]
  refine ⟨31758560693202284957063107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169378990363745519771003237 31758560693202284957063107)
  ·
    refine ⟨47637841039803427435594661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31758560693202284957063107 47637841039803427435594661)
    ·
      refine ⟨8932095194963142644173999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47637841039803427435594661 8932095194963142644173999)
      ·
        refine ⟨13398142792444713966260999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8932095194963142644173999 13398142792444713966260999)
        ·
          refine ⟨20097214188667070949391499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13398142792444713966260999 20097214188667070949391499)
          ·
            refine ⟨30145821283000606424087249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20097214188667070949391499 30145821283000606424087249)
            ·
              refine ⟨22609365962250454818065437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30145821283000606424087249 22609365962250454818065437)
              ·
                refine ⟨8478512235843920556774539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22609365962250454818065437 8478512235843920556774539)
                ·
                  refine ⟨12717768353765880835161809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478512235843920556774539 12717768353765880835161809)
                  ·
                    refine ⟨9538326265324410626371357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12717768353765880835161809 9538326265324410626371357)
                    ·
                      refine ⟨3576872349496653984889259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9538326265324410626371357 3576872349496653984889259)
                      ·
                        rfl

theorem cell23_6965934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6965934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965934 prefixEnd_6965934 := by exact prefixLift 6965934
  have htrace : WordTrace (prefixWord ++ tailWord_6965934) baseStart_6965934 baseEnd_6965934 := by
    simpa [prefixWord, tailWord_6965934, baseEnd_6965934] using wordTrace_append hprefix tailTrace_6965934
  have hstable : (prefixWord ++ tailWord_6965934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965934).length < 2 ^ (prefixWord ++ tailWord_6965934).sum := by decide
  have hdescent : baseEnd_6965934 < baseStart_6965934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965937 : List Nat := [1, 2, 2, 6, 2, 1, 9]
def baseStart_6965937 : Nat := 118140960795 + 6965937 * 2 ^ 59
def prefixEnd_6965937 : Nat := 4983230072969 + 3 ^ 40 * 6965937 * 2
def baseEnd_6965937 : Nat := 44158936912822437940145

theorem tailTrace_6965937 : CollatzResearch.WordTrace tailWord_6965937 prefixEnd_6965937 44158936912822437940145 := by
  unfold tailWord_6965937
  simp only [CollatzResearch.WordTrace]
  refine ⟨254068594964607411168864065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169379063309738274112576043 254068594964607411168864065)
  ·
    refine ⟨190551446223455558376648049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254068594964607411168864065 190551446223455558376648049)
    ·
      refine ⟨142913584667591668782486037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190551446223455558376648049 142913584667591668782486037)
      ·
        refine ⟨6699074281293359474179033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142913584667591668782486037 6699074281293359474179033)
        ·
          refine ⟨5024305710970019605634275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699074281293359474179033 5024305710970019605634275)
          ·
            refine ⟨7536458566455029408451413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024305710970019605634275 7536458566455029408451413)
            ·
              refine ⟨44158936912822437940145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7536458566455029408451413 44158936912822437940145)
              ·
                rfl

theorem cell23_6965937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 9].length) (baseStart_6965937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965937 prefixEnd_6965937 := by exact prefixLift 6965937
  have htrace : WordTrace (prefixWord ++ tailWord_6965937) baseStart_6965937 baseEnd_6965937 := by
    simpa [prefixWord, tailWord_6965937, baseEnd_6965937] using wordTrace_append hprefix tailTrace_6965937
  have hstable : (prefixWord ++ tailWord_6965937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965937).length < 2 ^ (prefixWord ++ tailWord_6965937).sum := by decide
  have hdescent : baseEnd_6965937 < baseStart_6965937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965964 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6965964 : Nat := 118140960795 + 6965964 * 2 ^ 59
def prefixEnd_6965964 : Nat := 4983230072969 + 3 ^ 40 * 6965964 * 2
def baseEnd_6965964 : Nat := 3576887753916288867514121

theorem tailTrace_6965964 : CollatzResearch.WordTrace tailWord_6965964 prefixEnd_6965964 3576887753916288867514121 := by
  unfold tailWord_6965964
  simp only [CollatzResearch.WordTrace]
  refine ⟨127034789867754797390048473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169379719823673063186731297 127034789867754797390048473)
  ·
    refine ⟨95276092400816098042536355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127034789867754797390048473 95276092400816098042536355)
    ·
      refine ⟨142914138601224147063804533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95276092400816098042536355 142914138601224147063804533)
      ·
        refine ⟨13398200493864763787231675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142914138601224147063804533 13398200493864763787231675)
        ·
          refine ⟨20097300740797145680847513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13398200493864763787231675 20097300740797145680847513)
          ·
            refine ⟨15072975555597859260635635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20097300740797145680847513 15072975555597859260635635)
            ·
              refine ⟨22609463333396788890953453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072975555597859260635635 22609463333396788890953453)
              ·
                refine ⟨8478548750023795834107545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22609463333396788890953453 8478548750023795834107545)
                ·
                  refine ⟨6358911562517846875580659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8478548750023795834107545 6358911562517846875580659)
                  ·
                    refine ⟨9538367343776770313370989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358911562517846875580659 9538367343776770313370989)
                    ·
                      refine ⟨3576887753916288867514121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9538367343776770313370989 3576887753916288867514121)
                      ·
                        rfl

theorem cell23_6965964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6965964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965964 prefixEnd_6965964 := by exact prefixLift 6965964
  have htrace : WordTrace (prefixWord ++ tailWord_6965964) baseStart_6965964 baseEnd_6965964 := by
    simpa [prefixWord, tailWord_6965964, baseEnd_6965964] using wordTrace_append hprefix tailTrace_6965964
  have hstable : (prefixWord ++ tailWord_6965964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965964).length < 2 ^ (prefixWord ++ tailWord_6965964).sum := by decide
  have hdescent : baseEnd_6965964 < baseStart_6965964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6965987 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6965987 : Nat := 118140960795 + 6965987 * 2 ^ 59
def prefixEnd_6965987 : Nat := 4983230072969 + 3 ^ 40 * 6965987 * 2
def baseEnd_6965987 : Nat := 3576899563971342277526515

theorem tailTrace_6965987 : CollatzResearch.WordTrace tailWord_6965987 prefixEnd_6965987 3576899563971342277526515 := by
  unfold tailWord_6965987
  simp only [CollatzResearch.WordTrace]
  refine ⟨254070418614426269708184215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169380279076284179805456143 254070418614426269708184215)
  ·
    refine ⟨381105627921639404562276323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254070418614426269708184215 381105627921639404562276323)
    ·
      refine ⟨571658441882459106843414485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381105627921639404562276323 571658441882459106843414485)
      ·
        refine ⟨13398244731620135316642527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 571658441882459106843414485 13398244731620135316642527)
        ·
          refine ⟨20097367097430202974963791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13398244731620135316642527 20097367097430202974963791)
          ·
            refine ⟨30146050646145304462445687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20097367097430202974963791 30146050646145304462445687)
            ·
              refine ⟨45219075969217956693668531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30146050646145304462445687 45219075969217956693668531)
              ·
                refine ⟨67828613953826935040502797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45219075969217956693668531 67828613953826935040502797)
                ·
                  refine ⟨25435730232685100640188549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67828613953826935040502797 25435730232685100640188549)
                  ·
                    refine ⟨4769199418628456370035353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25435730232685100640188549 4769199418628456370035353)
                    ·
                      refine ⟨3576899563971342277526515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769199418628456370035353 3576899563971342277526515)
                      ·
                        rfl

theorem cell23_6965987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6965987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6965987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6965987 prefixEnd_6965987 := by exact prefixLift 6965987
  have htrace : WordTrace (prefixWord ++ tailWord_6965987) baseStart_6965987 baseEnd_6965987 := by
    simpa [prefixWord, tailWord_6965987, baseEnd_6965987] using wordTrace_append hprefix tailTrace_6965987
  have hstable : (prefixWord ++ tailWord_6965987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6965987).length < 2 ^ (prefixWord ++ tailWord_6965987).sum := by decide
  have hdescent : baseEnd_6965987 < baseStart_6965987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6965987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966033 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_6966033 : Nat := 118140960795 + 6966033 * 2 ^ 59
def prefixEnd_6966033 : Nat := 4983230072969 + 3 ^ 40 * 6966033 * 2
def baseEnd_6966033 : Nat := 3576923184081449097551303

theorem tailTrace_6966033 : CollatzResearch.WordTrace tailWord_6966033 prefixEnd_6966033 3576923184081449097551303 := by
  unfold tailWord_6966033
  simp only [CollatzResearch.WordTrace]
  refine ⟨254072096372259619564358753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169381397581506413042905835 254072096372259619564358753)
  ·
    refine ⟨190554072279194714673269065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254072096372259619564358753 190554072279194714673269065)
    ·
      refine ⟨142915554209396036004951799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190554072279194714673269065 142915554209396036004951799)
      ·
        refine ⟨214373331314094054007427699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142915554209396036004951799 214373331314094054007427699)
        ·
          refine ⟨321559996971141081011141549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214373331314094054007427699 321559996971141081011141549)
          ·
            refine ⟨120584998864177905379178081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321559996971141081011141549 120584998864177905379178081)
            ·
              refine ⟨90438749148133429034383561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120584998864177905379178081 90438749148133429034383561)
              ·
                refine ⟨67829061861100071775787671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90438749148133429034383561 67829061861100071775787671)
                ·
                  refine ⟨101743592791650107663681507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67829061861100071775787671 101743592791650107663681507)
                  ·
                    refine ⟨152615389187475161495522261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101743592791650107663681507 152615389187475161495522261)
                    ·
                      refine ⟨3576923184081449097551303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152615389187475161495522261 3576923184081449097551303)
                      ·
                        rfl

theorem cell23_6966033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_6966033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966033 prefixEnd_6966033 := by exact prefixLift 6966033
  have htrace : WordTrace (prefixWord ++ tailWord_6966033) baseStart_6966033 baseEnd_6966033 := by
    simpa [prefixWord, tailWord_6966033, baseEnd_6966033] using wordTrace_append hprefix tailTrace_6966033
  have hstable : (prefixWord ++ tailWord_6966033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966033).length < 2 ^ (prefixWord ++ tailWord_6966033).sum := by decide
  have hdescent : baseEnd_6966033 < baseStart_6966033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966060 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_6966060 : Nat := 118140960795 + 6966060 * 2 ^ 59
def prefixEnd_6966060 : Nat := 4983230072969 + 3 ^ 40 * 6966060 * 2
def baseEnd_6966060 : Nat := 3576937048059120491913679

theorem tailTrace_6966060 : CollatzResearch.WordTrace tailWord_6966060 prefixEnd_6966060 3576937048059120491913679 := by
  unfold tailWord_6966060
  simp only [CollatzResearch.WordTrace]
  refine ⟨127036540571580901587795817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169382054095441202117061089 127036540571580901587795817)
  ·
    refine ⟨95277405428685676190846863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127036540571580901587795817 95277405428685676190846863)
    ·
      refine ⟨142916108143028514286270295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95277405428685676190846863 142916108143028514286270295)
      ·
        refine ⟨214374162214542771429405443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142916108143028514286270295 214374162214542771429405443)
        ·
          refine ⟨321561243321814157144108165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214374162214542771429405443 321561243321814157144108165)
          ·
            refine ⟨60292733122840154464520281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321561243321814157144108165 60292733122840154464520281)
            ·
              refine ⟨45219549842130115848390211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60292733122840154464520281 45219549842130115848390211)
              ·
                refine ⟨67829324763195173772585317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45219549842130115848390211 67829324763195173772585317)
                ·
                  refine ⟨12717998393099095082359747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67829324763195173772585317 12717998393099095082359747)
                  ·
                    refine ⟨19076997589648642623539621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12717998393099095082359747 19076997589648642623539621)
                    ·
                      refine ⟨3576937048059120491913679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19076997589648642623539621 3576937048059120491913679)
                      ·
                        rfl

theorem cell23_6966060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_6966060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966060 prefixEnd_6966060 := by exact prefixLift 6966060
  have htrace : WordTrace (prefixWord ++ tailWord_6966060) baseStart_6966060 baseEnd_6966060 := by
    simpa [prefixWord, tailWord_6966060, baseEnd_6966060] using wordTrace_append hprefix tailTrace_6966060
  have hstable : (prefixWord ++ tailWord_6966060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966060).length < 2 ^ (prefixWord ++ tailWord_6966060).sum := by decide
  have hdescent : baseEnd_6966060 < baseStart_6966060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966134 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_6966134 : Nat := 118140960795 + 6966134 * 2 ^ 59
def prefixEnd_6966134 : Nat := 4983230072969 + 3 ^ 40 * 6966134 * 2
def baseEnd_6966134 : Nat := 397441671736394800265371

theorem tailTrace_6966134 : CollatzResearch.WordTrace tailWord_6966134 prefixEnd_6966134 397441671736394800265371 := by
  unfold tailWord_6966134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879736259055857113361591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169383853429929142542523637 15879736259055857113361591)
  ·
    refine ⟨23819604388583785670042387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15879736259055857113361591 23819604388583785670042387)
    ·
      refine ⟨35729406582875678505063581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23819604388583785670042387 35729406582875678505063581)
      ·
        refine ⟨13398527468578379439398843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35729406582875678505063581 13398527468578379439398843)
        ·
          refine ⟨20097791202867569159098265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13398527468578379439398843 20097791202867569159098265)
          ·
            refine ⟨15073343402150676869323699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20097791202867569159098265 15073343402150676869323699)
            ·
              refine ⟨22610015103226015303985549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073343402150676869323699 22610015103226015303985549)
              ·
                refine ⟨8478755663709755738994581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22610015103226015303985549 8478755663709755738994581)
                ·
                  refine ⟨397441671736394800265371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8478755663709755738994581 397441671736394800265371)
                  ·
                    rfl

theorem cell23_6966134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_6966134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966134 prefixEnd_6966134 := by exact prefixLift 6966134
  have htrace : WordTrace (prefixWord ++ tailWord_6966134) baseStart_6966134 baseEnd_6966134 := by
    simpa [prefixWord, tailWord_6966134, baseEnd_6966134] using wordTrace_append hprefix tailTrace_6966134
  have hstable : (prefixWord ++ tailWord_6966134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966134).length < 2 ^ (prefixWord ++ tailWord_6966134).sum := by decide
  have hdescent : baseEnd_6966134 < baseStart_6966134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966178 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6966178 : Nat := 118140960795 + 6966178 * 2 ^ 59
def prefixEnd_6966178 : Nat := 4983230072969 + 3 ^ 40 * 6966178 * 2
def baseEnd_6966178 : Nat := 3576997638776351030238137

theorem tailTrace_6966178 : CollatzResearch.WordTrace tailWord_6966178 prefixEnd_6966178 3576997638776351030238137 := by
  unfold tailWord_6966178
  simp only [CollatzResearch.WordTrace]
  refine ⟨63519346239183577332096797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169384923304489539552258125 63519346239183577332096797)
  ·
    refine ⟨23819754839693841499536299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63519346239183577332096797 23819754839693841499536299)
    ·
      refine ⟨35729632259540762249304449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23819754839693841499536299 35729632259540762249304449)
      ·
        refine ⟨26797224194655571686978337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35729632259540762249304449 26797224194655571686978337)
        ·
          refine ⟨20097918145991678765233753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26797224194655571686978337 20097918145991678765233753)
          ·
            refine ⟨15073438609493759073925315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20097918145991678765233753 15073438609493759073925315)
            ·
              refine ⟨22610157914240638610887973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073438609493759073925315 22610157914240638610887973)
              ·
                refine ⟨4239404608920119739541495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22610157914240638610887973 4239404608920119739541495)
                ·
                  refine ⟨6359106913380179609312243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239404608920119739541495 6359106913380179609312243)
                  ·
                    refine ⟨9538660370070269413968365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6359106913380179609312243 9538660370070269413968365)
                    ·
                      refine ⟨3576997638776351030238137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9538660370070269413968365 3576997638776351030238137)
                      ·
                        rfl

theorem cell23_6966178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6966178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966178 prefixEnd_6966178 := by exact prefixLift 6966178
  have htrace : WordTrace (prefixWord ++ tailWord_6966178) baseStart_6966178 baseEnd_6966178 := by
    simpa [prefixWord, tailWord_6966178, baseEnd_6966178] using wordTrace_append hprefix tailTrace_6966178
  have hstable : (prefixWord ++ tailWord_6966178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966178).length < 2 ^ (prefixWord ++ tailWord_6966178).sum := by decide
  have hdescent : baseEnd_6966178 < baseStart_6966178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966201 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 3, 2, 2]
def baseStart_6966201 : Nat := 118140960795 + 6966201 * 2 ^ 59
def prefixEnd_6966201 : Nat := 4983230072969 + 3 ^ 40 * 6966201 * 2
def baseEnd_6966201 : Nat := 3577009448831404440250531

theorem tailTrace_6966201 : CollatzResearch.WordTrace tailWord_6966201 prefixEnd_6966201 3577009448831404440250531 := by
  unfold tailWord_6966201
  simp only [CollatzResearch.WordTrace]
  refine ⟨254078223835650984256474457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169385482557100656170982971 254078223835650984256474457)
  ·
    refine ⟨190558667876738238192355843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254078223835650984256474457 190558667876738238192355843)
    ·
      refine ⟨285838001815107357288533765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190558667876738238192355843 285838001815107357288533765)
      ·
        refine ⟨53594625340332629491600081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285838001815107357288533765 53594625340332629491600081)
        ·
          refine ⟨40195969005249472118700061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53594625340332629491600081 40195969005249472118700061)
          ·
            refine ⟨15073488376968552044512523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40195969005249472118700061 15073488376968552044512523)
            ·
              refine ⟨22610232565452828066768785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073488376968552044512523 22610232565452828066768785)
              ·
                refine ⟨16957674424089621050076589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22610232565452828066768785 16957674424089621050076589)
                ·
                  refine ⟨6359127909033607893778721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16957674424089621050076589 6359127909033607893778721)
                  ·
                    refine ⟨4769345931775205920334041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6359127909033607893778721 4769345931775205920334041)
                    ·
                      refine ⟨3577009448831404440250531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769345931775205920334041 3577009448831404440250531)
                      ·
                        rfl

theorem cell23_6966201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_6966201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966201 prefixEnd_6966201 := by exact prefixLift 6966201
  have htrace : WordTrace (prefixWord ++ tailWord_6966201) baseStart_6966201 baseEnd_6966201 := by
    simpa [prefixWord, tailWord_6966201, baseEnd_6966201] using wordTrace_append hprefix tailTrace_6966201
  have hstable : (prefixWord ++ tailWord_6966201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966201).length < 2 ^ (prefixWord ++ tailWord_6966201).sum := by decide
  have hdescent : baseEnd_6966201 < baseStart_6966201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966244 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_6966244 : Nat := 118140960795 + 6966244 * 2 ^ 59
def prefixEnd_6966244 : Nat := 4983230072969 + 3 ^ 40 * 6966244 * 2
def baseEnd_6966244 : Nat := 3577031528499547772012833

theorem tailTrace_6966244 : CollatzResearch.WordTrace tailWord_6966244 prefixEnd_6966244 3577031528499547772012833 := by
  unfold tailWord_6966244
  simp only [CollatzResearch.WordTrace]
  refine ⟨127039896087247601300144893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169386528116330135066859857 127039896087247601300144893)
  ·
    refine ⟨47639961032717850487554335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127039896087247601300144893 47639961032717850487554335)
    ·
      refine ⟨71459941549076775731331503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47639961032717850487554335 71459941549076775731331503)
      ·
        refine ⟨107189912323615163596997255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71459941549076775731331503 107189912323615163596997255)
        ·
          refine ⟨160784868485422745395495883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107189912323615163596997255 160784868485422745395495883)
          ·
            refine ⟨241177302728134118093243825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160784868485422745395495883 241177302728134118093243825)
            ·
              refine ⟨180882977046100588569932869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241177302728134118093243825 180882977046100588569932869)
              ·
                refine ⟨33915558196143860356862413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180882977046100588569932869 33915558196143860356862413)
                ·
                  refine ⟨12718334323553947633823405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33915558196143860356862413 12718334323553947633823405)
                  ·
                    refine ⟨4769375371332730362683777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12718334323553947633823405 4769375371332730362683777)
                    ·
                      refine ⟨3577031528499547772012833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769375371332730362683777 3577031528499547772012833)
                      ·
                        rfl

theorem cell23_6966244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_6966244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966244 prefixEnd_6966244 := by exact prefixLift 6966244
  have htrace : WordTrace (prefixWord ++ tailWord_6966244) baseStart_6966244 baseEnd_6966244 := by
    simpa [prefixWord, tailWord_6966244, baseEnd_6966244] using wordTrace_append hprefix tailTrace_6966244
  have hstable : (prefixWord ++ tailWord_6966244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966244).length < 2 ^ (prefixWord ++ tailWord_6966244).sum := by decide
  have hdescent : baseEnd_6966244 < baseStart_6966244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966258 : List Nat := [3, 2, 1, 5, 2, 1, 2, 7]
def baseStart_6966258 : Nat := 118140960795 + 6966258 * 2 ^ 59
def prefixEnd_6966258 : Nat := 4983230072969 + 3 ^ 40 * 6966258 * 2
def baseEnd_6966258 : Nat := 132482915452915211749547

theorem tailTrace_6966258 : CollatzResearch.WordTrace tailWord_6966258 prefixEnd_6966258 132482915452915211749547 := by
  unfold tailWord_6966258
  simp only [CollatzResearch.WordTrace]
  refine ⟨63520075699111120747824857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169386868530962988660866285 63520075699111120747824857)
  ·
    refine ⟨47640056774333340560868643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63520075699111120747824857 47640056774333340560868643)
    ·
      refine ⟨71460085161500010841302965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47640056774333340560868643 71460085161500010841302965)
      ·
        refine ⟨6699382983890626016372153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71460085161500010841302965 6699382983890626016372153)
        ·
          refine ⟨5024537237917969512279115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699382983890626016372153 5024537237917969512279115)
          ·
            refine ⟨7536805856876954268418673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024537237917969512279115 7536805856876954268418673)
            ·
              refine ⟨5652604392657715701314005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536805856876954268418673 5652604392657715701314005)
              ·
                refine ⟨132482915452915211749547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5652604392657715701314005 132482915452915211749547)
                ·
                  rfl

theorem cell23_6966258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_6966258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966258 prefixEnd_6966258 := by exact prefixLift 6966258
  have htrace : WordTrace (prefixWord ++ tailWord_6966258) baseStart_6966258 baseEnd_6966258 := by
    simpa [prefixWord, tailWord_6966258, baseEnd_6966258] using wordTrace_append hprefix tailTrace_6966258
  have hstable : (prefixWord ++ tailWord_6966258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966258).length < 2 ^ (prefixWord ++ tailWord_6966258).sum := by decide
  have hdescent : baseEnd_6966258 < baseStart_6966258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966277 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_6966277 : Nat := 118140960795 + 6966277 * 2 ^ 59
def prefixEnd_6966277 : Nat := 4983230072969 + 3 ^ 40 * 6966277 * 2
def baseEnd_6966277 : Nat := 3577048473361146142900181

theorem tailTrace_6966277 : CollatzResearch.WordTrace tailWord_6966277 prefixEnd_6966277 3577048473361146142900181 := by
  unfold tailWord_6966277
  simp only [CollatzResearch.WordTrace]
  refine ⟨254080995783375649236241085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169387330522250432824160723 254080995783375649236241085)
  ·
    refine ⟨95280373418765868463590407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254080995783375649236241085 95280373418765868463590407)
    ·
      refine ⟨142920560128148802695385611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95280373418765868463590407 142920560128148802695385611)
      ·
        refine ⟨214380840192223204043078417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142920560128148802695385611 214380840192223204043078417)
        ·
          refine ⟨160785630144167403032308813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214380840192223204043078417 160785630144167403032308813)
          ·
            refine ⟨60294611304062776137115805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160785630144167403032308813 60294611304062776137115805)
            ·
              refine ⟨22610479239023541051418427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60294611304062776137115805 22610479239023541051418427)
              ·
                refine ⟨33915718858535311577127641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22610479239023541051418427 33915718858535311577127641)
                ·
                  refine ⟨25436789143901483682845731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33915718858535311577127641 25436789143901483682845731)
                  ·
                    refine ⟨38155183715852225524268597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25436789143901483682845731 38155183715852225524268597)
                    ·
                      refine ⟨3577048473361146142900181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38155183715852225524268597 3577048473361146142900181)
                      ·
                        rfl

theorem cell23_6966277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_6966277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966277 prefixEnd_6966277 := by exact prefixLift 6966277
  have htrace : WordTrace (prefixWord ++ tailWord_6966277) baseStart_6966277 baseEnd_6966277 := by
    simpa [prefixWord, tailWord_6966277, baseEnd_6966277] using wordTrace_append hprefix tailTrace_6966277
  have hstable : (prefixWord ++ tailWord_6966277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966277).length < 2 ^ (prefixWord ++ tailWord_6966277).sum := by decide
  have hdescent : baseEnd_6966277 < baseStart_6966277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966291 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 2, 2, 2]
def baseStart_6966291 : Nat := 118140960795 + 6966291 * 2 ^ 59
def prefixEnd_6966291 : Nat := 4983230072969 + 3 ^ 40 * 6966291 * 2
def baseEnd_6966291 : Nat := 3577055662090309088125117

theorem tailTrace_6966291 : CollatzResearch.WordTrace tailWord_6966291 prefixEnd_6966291 3577055662090309088125117 := by
  unfold tailWord_6966291
  simp only [CollatzResearch.WordTrace]
  refine ⟨254081506405324929627250727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169387670936883286418167151 254081506405324929627250727)
  ·
    refine ⟨381122259607987394440876091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254081506405324929627250727 381122259607987394440876091)
    ·
      refine ⟨571683389411981091661314137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381122259607987394440876091 571683389411981091661314137)
      ·
        refine ⟨428762542058985818745985603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571683389411981091661314137 428762542058985818745985603)
        ·
          refine ⟨643143813088478728118978405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428762542058985818745985603 643143813088478728118978405)
          ·
            refine ⟨120589464954089761522308451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 643143813088478728118978405 120589464954089761522308451)
            ·
              refine ⟨180884197431134642283462677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120589464954089761522308451 180884197431134642283462677)
              ·
                refine ⟨8478946754584436357037313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180884197431134642283462677 8478946754584436357037313)
                ·
                  refine ⟨6359210065938327267777985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8478946754584436357037313 6359210065938327267777985)
                  ·
                    refine ⟨4769407549453745450833489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6359210065938327267777985 4769407549453745450833489)
                    ·
                      refine ⟨3577055662090309088125117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769407549453745450833489 3577055662090309088125117)
                      ·
                        rfl

theorem cell23_6966291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 2, 2].length) (baseStart_6966291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966291 prefixEnd_6966291 := by exact prefixLift 6966291
  have htrace : WordTrace (prefixWord ++ tailWord_6966291) baseStart_6966291 baseEnd_6966291 := by
    simpa [prefixWord, tailWord_6966291, baseEnd_6966291] using wordTrace_append hprefix tailTrace_6966291
  have hstable : (prefixWord ++ tailWord_6966291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966291).length < 2 ^ (prefixWord ++ tailWord_6966291).sum := by decide
  have hdescent : baseEnd_6966291 < baseStart_6966291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966297 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 7]
def baseStart_6966297 : Nat := 118140960795 + 6966297 * 2 ^ 59
def prefixEnd_6966297 : Nat := 4983230072969 + 3 ^ 40 * 6966297 * 2
def baseEnd_6966297 : Nat := 397450971441581784961121

theorem tailTrace_6966297 : CollatzResearch.WordTrace tailWord_6966297 prefixEnd_6966297 397450971441581784961121 := by
  unfold tailWord_6966297
  simp only [CollatzResearch.WordTrace]
  refine ⟨254081725243303192651969145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169387816828868795101312763 254081725243303192651969145)
  ·
    refine ⟨190561293932477394488976859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254081725243303192651969145 190561293932477394488976859)
    ·
      refine ⟨285841940898716091733465289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190561293932477394488976859 285841940898716091733465289)
      ·
        refine ⟨214381455674037068800098967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285841940898716091733465289 214381455674037068800098967)
        ·
          refine ⟨321572183511055603200148451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214381455674037068800098967 321572183511055603200148451)
          ·
            refine ⟨482358275266583404800222677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321572183511055603200148451 482358275266583404800222677)
            ·
              refine ⟨11305272076560548550005219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 482358275266583404800222677 11305272076560548550005219)
              ·
                refine ⟨16957908114840822825007829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305272076560548550005219 16957908114840822825007829)
                ·
                  refine ⟨397450971441581784961121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16957908114840822825007829 397450971441581784961121)
                  ·
                    rfl

theorem cell23_6966297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_6966297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966297 prefixEnd_6966297 := by exact prefixLift 6966297
  have htrace : WordTrace (prefixWord ++ tailWord_6966297) baseStart_6966297 baseEnd_6966297 := by
    simpa [prefixWord, tailWord_6966297, baseEnd_6966297] using wordTrace_append hprefix tailTrace_6966297
  have hstable : (prefixWord ++ tailWord_6966297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966297).length < 2 ^ (prefixWord ++ tailWord_6966297).sum := by decide
  have hdescent : baseEnd_6966297 < baseStart_6966297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966342 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6966342 : Nat := 118140960795 + 6966342 * 2 ^ 59
def prefixEnd_6966342 : Nat := 4983230072969 + 3 ^ 40 * 6966342 * 2
def baseEnd_6966342 : Nat := 3577081849603688388587383

theorem tailTrace_6966342 : CollatzResearch.WordTrace tailWord_6966342 prefixEnd_6966342 3577081849603688388587383 := by
  unfold tailWord_6966342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7940105204004380166792415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169388911018760110224904853 7940105204004380166792415)
  ·
    refine ⟨11910157806006570250188623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7940105204004380166792415 11910157806006570250188623)
    ·
      refine ⟨17865236709009855375282935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11910157806006570250188623 17865236709009855375282935)
      ·
        refine ⟨26797855063514783062924403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17865236709009855375282935 26797855063514783062924403)
        ·
          refine ⟨40196782595272174594386605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26797855063514783062924403 40196782595272174594386605)
          ·
            refine ⟨15073793473227065472894977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40196782595272174594386605 15073793473227065472894977)
            ·
              refine ⟨11305345104920299104671233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15073793473227065472894977 11305345104920299104671233)
              ·
                refine ⟨8479008828690224328503425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11305345104920299104671233 8479008828690224328503425)
                ·
                  refine ⟨6359256621517668246377569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479008828690224328503425 6359256621517668246377569)
                  ·
                    refine ⟨4769442466138251184783177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6359256621517668246377569 4769442466138251184783177)
                    ·
                      refine ⟨3577081849603688388587383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769442466138251184783177 3577081849603688388587383)
                      ·
                        rfl

theorem cell23_6966342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6966342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966342 prefixEnd_6966342 := by exact prefixLift 6966342
  have htrace : WordTrace (prefixWord ++ tailWord_6966342) baseStart_6966342 baseEnd_6966342 := by
    simpa [prefixWord, tailWord_6966342, baseEnd_6966342] using wordTrace_append hprefix tailTrace_6966342
  have hstable : (prefixWord ++ tailWord_6966342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966342).length < 2 ^ (prefixWord ++ tailWord_6966342).sum := by decide
  have hdescent : baseEnd_6966342 < baseStart_6966342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966354 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_6966354 : Nat := 118140960795 + 6966354 * 2 ^ 59
def prefixEnd_6966354 : Nat := 4983230072969 + 3 ^ 40 * 6966354 * 2
def baseEnd_6966354 : Nat := 3577088011371542341637327

theorem tailTrace_6966354 : CollatzResearch.WordTrace tailWord_6966354 prefixEnd_6966354 3577088011371542341637327 := by
  unfold tailWord_6966354
  simp only [CollatzResearch.WordTrace]
  refine ⟨63520951051024172846698529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169389202802731127591196077 63520951051024172846698529)
  ·
    refine ⟨47640713288268129635023897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63520951051024172846698529 47640713288268129635023897)
    ·
      refine ⟨35730534966201097226267923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47640713288268129635023897 35730534966201097226267923)
      ·
        refine ⟨53595802449301645839401885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35730534966201097226267923 53595802449301645839401885)
        ·
          refine ⟨20098425918488117189775707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53595802449301645839401885 20098425918488117189775707)
          ·
            refine ⟨30147638877732175784663561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20098425918488117189775707 30147638877732175784663561)
            ·
              refine ⟨22610729158299131838497671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30147638877732175784663561 22610729158299131838497671)
              ·
                refine ⟨33916093737448697757746507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22610729158299131838497671 33916093737448697757746507)
                ·
                  refine ⟨50874140606173046636619761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33916093737448697757746507 50874140606173046636619761)
                  ·
                    refine ⟨38155605454629784977464821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50874140606173046636619761 38155605454629784977464821)
                    ·
                      refine ⟨3577088011371542341637327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38155605454629784977464821 3577088011371542341637327)
                      ·
                        rfl

theorem cell23_6966354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_6966354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966354 prefixEnd_6966354 := by exact prefixLift 6966354
  have htrace : WordTrace (prefixWord ++ tailWord_6966354) baseStart_6966354 baseEnd_6966354 := by
    simpa [prefixWord, tailWord_6966354, baseEnd_6966354] using wordTrace_append hprefix tailTrace_6966354
  have hstable : (prefixWord ++ tailWord_6966354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966354).length < 2 ^ (prefixWord ++ tailWord_6966354).sum := by decide
  have hdescent : baseEnd_6966354 < baseStart_6966354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966364 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6966364 : Nat := 118140960795 + 6966364 * 2 ^ 59
def prefixEnd_6966364 : Nat := 4983230072969 + 3 ^ 40 * 6966364 * 2
def baseEnd_6966364 : Nat := 3577093146178087302512281

theorem tailTrace_6966364 : CollatzResearch.WordTrace tailWord_6966364 prefixEnd_6966364 3577093146178087302512281 := by
  unfold tailWord_6966364
  simp only [CollatzResearch.WordTrace]
  refine ⟨127042084467030231547329073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169389445956040308729772097 127042084467030231547329073)
  ·
    refine ⟨95281563350272673660496805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127042084467030231547329073 95281563350272673660496805)
    ·
      refine ⟨17865293128176126311343151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95281563350272673660496805 17865293128176126311343151)
      ·
        refine ⟨26797939692264189467014727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17865293128176126311343151 26797939692264189467014727)
        ·
          refine ⟨40196909538396284200522091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26797939692264189467014727 40196909538396284200522091)
          ·
            refine ⟨60295364307594426300783137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40196909538396284200522091 60295364307594426300783137)
            ·
              refine ⟨45221523230695819725587353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60295364307594426300783137 45221523230695819725587353)
              ·
                refine ⟨33916142423021864794190515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45221523230695819725587353 33916142423021864794190515)
                ·
                  refine ⟨50874213634532797191285773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33916142423021864794190515 50874213634532797191285773)
                  ·
                    refine ⟨19077830112949798946732165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50874213634532797191285773 19077830112949798946732165)
                    ·
                      refine ⟨3577093146178087302512281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19077830112949798946732165 3577093146178087302512281)
                      ·
                        rfl

theorem cell23_6966364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6966364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966364 prefixEnd_6966364 := by exact prefixLift 6966364
  have htrace : WordTrace (prefixWord ++ tailWord_6966364) baseStart_6966364 baseEnd_6966364 := by
    simpa [prefixWord, tailWord_6966364, baseEnd_6966364] using wordTrace_append hprefix tailTrace_6966364
  have hstable : (prefixWord ++ tailWord_6966364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966364).length < 2 ^ (prefixWord ++ tailWord_6966364).sum := by decide
  have hdescent : baseEnd_6966364 < baseStart_6966364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966381 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_6966381 : Nat := 118140960795 + 6966381 * 2 ^ 59
def prefixEnd_6966381 : Nat := 4983230072969 + 3 ^ 40 * 6966381 * 2
def baseEnd_6966381 : Nat := 3577101875349213735999703

theorem tailTrace_6966381 : CollatzResearch.WordTrace tailWord_6966381 prefixEnd_6966381 3577101875349213735999703 := by
  unfold tailWord_6966381
  simp only [CollatzResearch.WordTrace]
  refine ⟨254084788974998874998026997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169389859316665916665351331 254084788974998874998026997)
  ·
    refine ⟨23820448966406144531065031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254084788974998874998026997 23820448966406144531065031)
    ·
      refine ⟨35730673449609216796597547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23820448966406144531065031 35730673449609216796597547)
      ·
        refine ⟨53596010174413825194896321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35730673449609216796597547 53596010174413825194896321)
        ·
          refine ⟨40197007630810368896172241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53596010174413825194896321 40197007630810368896172241)
          ·
            refine ⟨30147755723107776672129181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40197007630810368896172241 30147755723107776672129181)
            ·
              refine ⟨11305408396165416252048443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30147755723107776672129181 11305408396165416252048443)
              ·
                refine ⟨16958112594248124378072665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305408396165416252048443 16958112594248124378072665)
                ·
                  refine ⟨12718584445686093283554499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16958112594248124378072665 12718584445686093283554499)
                  ·
                    refine ⟨19077876668529139925331749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12718584445686093283554499 19077876668529139925331749)
                    ·
                      refine ⟨3577101875349213735999703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19077876668529139925331749 3577101875349213735999703)
                      ·
                        rfl

theorem cell23_6966381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_6966381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966381 prefixEnd_6966381 := by exact prefixLift 6966381
  have htrace : WordTrace (prefixWord ++ tailWord_6966381) baseStart_6966381 baseEnd_6966381 := by
    simpa [prefixWord, tailWord_6966381, baseEnd_6966381] using wordTrace_append hprefix tailTrace_6966381
  have hstable : (prefixWord ++ tailWord_6966381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966381).length < 2 ^ (prefixWord ++ tailWord_6966381).sum := by decide
  have hdescent : baseEnd_6966381 < baseStart_6966381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966384 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_6966384 : Nat := 118140960795 + 6966384 * 2 ^ 59
def prefixEnd_6966384 : Nat := 4983230072969 + 3 ^ 40 * 6966384 * 2
def baseEnd_6966384 : Nat := 3577103415791177224262189

theorem tailTrace_6966384 : CollatzResearch.WordTrace tailWord_6966384 prefixEnd_6966384 3577103415791177224262189 := by
  unfold tailWord_6966384
  simp only [CollatzResearch.WordTrace]
  refine ⟨127042449196994003255193103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169389932262658671006924137 127042449196994003255193103)
  ·
    refine ⟨190563673795491004882789655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127042449196994003255193103 190563673795491004882789655)
    ·
      refine ⟨285845510693236507324184483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190563673795491004882789655 285845510693236507324184483)
      ·
        refine ⟨428768266039854760986276725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285845510693236507324184483 428768266039854760986276725)
        ·
          refine ⟨40197024941236383842463443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 428768266039854760986276725 40197024941236383842463443)
          ·
            refine ⟨60295537411854575763695165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40197024941236383842463443 60295537411854575763695165)
            ·
              refine ⟨22610826529445465911385687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60295537411854575763695165 22610826529445465911385687)
              ·
                refine ⟨33916239794168198867078531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22610826529445465911385687 33916239794168198867078531)
                ·
                  refine ⟨50874359691252298300617797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33916239794168198867078531 50874359691252298300617797)
                  ·
                    refine ⟨9538942442109805931365837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50874359691252298300617797 9538942442109805931365837)
                    ·
                      refine ⟨3577103415791177224262189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9538942442109805931365837 3577103415791177224262189)
                      ·
                        rfl

theorem cell23_6966384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_6966384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966384 prefixEnd_6966384 := by exact prefixLift 6966384
  have htrace : WordTrace (prefixWord ++ tailWord_6966384) baseStart_6966384 baseEnd_6966384 := by
    simpa [prefixWord, tailWord_6966384, baseEnd_6966384] using wordTrace_append hprefix tailTrace_6966384
  have hstable : (prefixWord ++ tailWord_6966384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966384).length < 2 ^ (prefixWord ++ tailWord_6966384).sum := by decide
  have hdescent : baseEnd_6966384 < baseStart_6966384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966404 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 8]
def baseStart_6966404 : Nat := 118140960795 + 6966404 * 2 ^ 59
def prefixEnd_6966404 : Nat := 4983230072969 + 3 ^ 40 * 6966404 * 2
def baseEnd_6966404 : Nat := 397457076156029682890233

theorem tailTrace_6966404 : CollatzResearch.WordTrace tailWord_6966404 prefixEnd_6966404 397457076156029682890233 := by
  unfold tailWord_6966404
  simp only [CollatzResearch.WordTrace]
  refine ⟨127042813926957774963057133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169390418569277033284076177 127042813926957774963057133)
  ·
    refine ⟨47641055222609165611146425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127042813926957774963057133 47641055222609165611146425)
    ·
      refine ⟨35730791416956874208359819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47641055222609165611146425 35730791416956874208359819)
      ·
        refine ⟨53596187125435311312539729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35730791416956874208359819 53596187125435311312539729)
        ·
          refine ⟨40197140344076483484404797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53596187125435311312539729 40197140344076483484404797)
          ·
            refine ⟨15073927629028681306651799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40197140344076483484404797 15073927629028681306651799)
            ·
              refine ⟨22610891443543021959977699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073927629028681306651799 22610891443543021959977699)
              ·
                refine ⟨33916337165314532939966549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22610891443543021959977699 33916337165314532939966549)
                ·
                  refine ⟨397457076156029682890233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33916337165314532939966549 397457076156029682890233)
                  ·
                    rfl

theorem cell23_6966404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_6966404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966404 prefixEnd_6966404 := by exact prefixLift 6966404
  have htrace : WordTrace (prefixWord ++ tailWord_6966404) baseStart_6966404 baseEnd_6966404 := by
    simpa [prefixWord, tailWord_6966404, baseEnd_6966404] using wordTrace_append hprefix tailTrace_6966404
  have hstable : (prefixWord ++ tailWord_6966404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966404).length < 2 ^ (prefixWord ++ tailWord_6966404).sum := by decide
  have hdescent : baseEnd_6966404 < baseStart_6966404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966408 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 3, 4]
def baseStart_6966408 : Nat := 118140960795 + 6966408 * 2 ^ 59
def prefixEnd_6966408 : Nat := 4983230072969 + 3 ^ 40 * 6966408 * 2
def baseEnd_6966408 : Nat := 1192371913108961710120693

theorem tailTrace_6966408 : CollatzResearch.WordTrace tailWord_6966408 prefixEnd_6966408 1192371913108961710120693 := by
  unfold tailWord_6966408
  simp only [CollatzResearch.WordTrace]
  refine ⟨127042886872950529304629939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169390515830600705739506585 127042886872950529304629939)
  ·
    refine ⟨190564330309425793956944909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127042886872950529304629939 190564330309425793956944909)
    ·
      refine ⟨71461623866034672733854341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190564330309425793956944909 71461623866034672733854341)
      ·
        refine ⟨13399054474881501137597689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71461623866034672733854341 13399054474881501137597689)
        ·
          refine ⟨10049290856161125853198267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13399054474881501137597689 10049290856161125853198267)
          ·
            refine ⟨15073936284241688779797401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10049290856161125853198267 15073936284241688779797401)
            ·
              refine ⟨11305452213181266584848051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15073936284241688779797401 11305452213181266584848051)
              ·
                refine ⟨16958178319771899877272077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305452213181266584848051 16958178319771899877272077)
                ·
                  refine ⟨6359316869914462453977029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16958178319771899877272077 6359316869914462453977029)
                  ·
                    refine ⟨1192371913108961710120693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359316869914462453977029 1192371913108961710120693)
                    ·
                      rfl

theorem cell23_6966408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_6966408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966408 prefixEnd_6966408 := by exact prefixLift 6966408
  have htrace : WordTrace (prefixWord ++ tailWord_6966408) baseStart_6966408 baseEnd_6966408 := by
    simpa [prefixWord, tailWord_6966408, baseEnd_6966408] using wordTrace_append hprefix tailTrace_6966408
  have hstable : (prefixWord ++ tailWord_6966408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966408).length < 2 ^ (prefixWord ++ tailWord_6966408).sum := by decide
  have hdescent : baseEnd_6966408 < baseStart_6966408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966442 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6966442 : Nat := 118140960795 + 6966442 * 2 ^ 59
def prefixEnd_6966442 : Nat := 4983230072969 + 3 ^ 40 * 6966442 * 2
def baseEnd_6966442 : Nat := 1192377732556379332445641

theorem tailTrace_6966442 : CollatzResearch.WordTrace tailWord_6966442 prefixEnd_6966442 1192377732556379332445641 := by
  unfold tailWord_6966442
  simp only [CollatzResearch.WordTrace]
  refine ⟨63521753456944470603999395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169391342551851921610665053 63521753456944470603999395)
  ·
    refine ⟨95282630185416705905999093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63521753456944470603999395 95282630185416705905999093)
    ·
      refine ⟨8932746579882816178687415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95282630185416705905999093 8932746579882816178687415)
      ·
        refine ⟨13399119869824224268031123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8932746579882816178687415 13399119869824224268031123)
        ·
          refine ⟨20098679804736336402046685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399119869824224268031123 20098679804736336402046685)
          ·
            refine ⟨7537004926776126150767507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20098679804736336402046685 7537004926776126150767507)
            ·
              refine ⟨11305507390164189226151261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537004926776126150767507 11305507390164189226151261)
              ·
                refine ⟨4239565271311570959806723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11305507390164189226151261 4239565271311570959806723)
                ·
                  refine ⟨6359347906967356439710085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239565271311570959806723 6359347906967356439710085)
                  ·
                    refine ⟨1192377732556379332445641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359347906967356439710085 1192377732556379332445641)
                    ·
                      rfl

theorem cell23_6966442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6966442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966442 prefixEnd_6966442 := by exact prefixLift 6966442
  have htrace : WordTrace (prefixWord ++ tailWord_6966442) baseStart_6966442 baseEnd_6966442 := by
    simpa [prefixWord, tailWord_6966442, baseEnd_6966442] using wordTrace_append hprefix tailTrace_6966442
  have hstable : (prefixWord ++ tailWord_6966442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966442).length < 2 ^ (prefixWord ++ tailWord_6966442).sum := by decide
  have hdescent : baseEnd_6966442 < baseStart_6966442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966465 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6966465 : Nat := 118140960795 + 6966465 * 2 ^ 59
def prefixEnd_6966465 : Nat := 4983230072969 + 3 ^ 40 * 6966465 * 2
def baseEnd_6966465 : Nat := 3577145007724191407349317

theorem tailTrace_6966465 : CollatzResearch.WordTrace tailWord_6966465 prefixEnd_6966465 3577145007724191407349317 := by
  unfold tailWord_6966465
  simp only [CollatzResearch.WordTrace]
  refine ⟨254087852706694557344084849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169391901804463038229389899 254087852706694557344084849)
  ·
    refine ⟨190565889530020918008063637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254087852706694557344084849 190565889530020918008063637)
    ·
      refine ⟨8932776071719730531627983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190565889530020918008063637 8932776071719730531627983)
      ·
        refine ⟨13399164107579595797441975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8932776071719730531627983 13399164107579595797441975)
        ·
          refine ⟨20098746161369393696162963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399164107579595797441975 20098746161369393696162963)
          ·
            refine ⟨30148119242054090544244445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20098746161369393696162963 30148119242054090544244445)
            ·
              refine ⟨11305544715770283954091667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30148119242054090544244445 11305544715770283954091667)
              ·
                refine ⟨16958317073655425931137501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305544715770283954091667 16958317073655425931137501)
                ·
                  refine ⟨6359368902620784724176563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16958317073655425931137501 6359368902620784724176563)
                  ·
                    refine ⟨9539053353931177086264845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6359368902620784724176563 9539053353931177086264845)
                    ·
                      refine ⟨3577145007724191407349317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539053353931177086264845 3577145007724191407349317)
                      ·
                        rfl

theorem cell23_6966465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6966465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966465 prefixEnd_6966465 := by exact prefixLift 6966465
  have htrace : WordTrace (prefixWord ++ tailWord_6966465) baseStart_6966465 baseEnd_6966465 := by
    simpa [prefixWord, tailWord_6966465, baseEnd_6966465] using wordTrace_append hprefix tailTrace_6966465
  have hstable : (prefixWord ++ tailWord_6966465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966465).length < 2 ^ (prefixWord ++ tailWord_6966465).sum := by decide
  have hdescent : baseEnd_6966465 < baseStart_6966465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966516 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6966516 : Nat := 118140960795 + 6966516 * 2 ^ 59
def prefixEnd_6966516 : Nat := 4983230072969 + 3 ^ 40 * 6966516 * 2
def baseEnd_6966516 : Nat := 3577171195237570707811583

theorem tailTrace_6966516 : CollatzResearch.WordTrace tailWord_6966516 prefixEnd_6966516 3577171195237570707811583 := by
  unfold tailWord_6966516
  simp only [CollatzResearch.WordTrace]
  refine ⟨127044856414754896527095701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169393141886339862036127601 127044856414754896527095701)
  ·
    refine ⟨5955227644441635774707611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127044856414754896527095701 5955227644441635774707611)
    ·
      refine ⟨8932841466662453662061417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955227644441635774707611 8932841466662453662061417)
      ·
        refine ⟨6699631099996840246546063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8932841466662453662061417 6699631099996840246546063)
        ·
          refine ⟨10049446649995260369819095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6699631099996840246546063 10049446649995260369819095)
          ·
            refine ⟨15074169974992890554728643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10049446649995260369819095 15074169974992890554728643)
            ·
              refine ⟨22611254962489335832092965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15074169974992890554728643 22611254962489335832092965)
              ·
                refine ⟨4239610305466750468517431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22611254962489335832092965 4239610305466750468517431)
                ·
                  refine ⟨6359415458200125702776147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239610305466750468517431 6359415458200125702776147)
                  ·
                    refine ⟨9539123187300188554164221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6359415458200125702776147 9539123187300188554164221)
                    ·
                      refine ⟨3577171195237570707811583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539123187300188554164221 3577171195237570707811583)
                      ·
                        rfl

theorem cell23_6966516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6966516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966516 prefixEnd_6966516 := by exact prefixLift 6966516
  have htrace : WordTrace (prefixWord ++ tailWord_6966516) baseStart_6966516 baseEnd_6966516 := by
    simpa [prefixWord, tailWord_6966516, baseEnd_6966516] using wordTrace_append hprefix tailTrace_6966516
  have hstable : (prefixWord ++ tailWord_6966516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966516).length < 2 ^ (prefixWord ++ tailWord_6966516).sum := by decide
  have hdescent : baseEnd_6966516 < baseStart_6966516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966565 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 1, 3, 2]
def baseStart_6966565 : Nat := 118140960795 + 6966565 * 2 ^ 59
def prefixEnd_6966565 : Nat := 4983230072969 + 3 ^ 40 * 6966565 * 2
def baseEnd_6966565 : Nat := 3577196355789641016098857

theorem tailTrace_6966565 : CollatzResearch.WordTrace tailWord_6966565 prefixEnd_6966565 3577196355789641016098857 := by
  unfold tailWord_6966565
  simp only [CollatzResearch.WordTrace]
  refine ⟨254091500006332274422725149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169394333337554849615150099 254091500006332274422725149)
  ·
    refine ⟨95284312502374602908521931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254091500006332274422725149 95284312502374602908521931)
    ·
      refine ⟨142926468753561904362782897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95284312502374602908521931 142926468753561904362782897)
      ·
        refine ⟨107194851565171428272087173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142926468753561904362782897 107194851565171428272087173)
        ·
          refine ⟨20099034668469642801016345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107194851565171428272087173 20099034668469642801016345)
          ·
            refine ⟨15074276001352232100762259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20099034668469642801016345 15074276001352232100762259)
            ·
              refine ⟨22611414002028348151143389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15074276001352232100762259 22611414002028348151143389)
              ·
                refine ⟨8479280250760630556678771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22611414002028348151143389 8479280250760630556678771)
                ·
                  refine ⟨12718920376140945835018157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8479280250760630556678771 12718920376140945835018157)
                  ·
                    refine ⟨4769595141052854688131809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12718920376140945835018157 4769595141052854688131809)
                    ·
                      refine ⟨3577196355789641016098857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769595141052854688131809 3577196355789641016098857)
                      ·
                        rfl

theorem cell23_6966565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_6966565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966565 prefixEnd_6966565 := by exact prefixLift 6966565
  have htrace : WordTrace (prefixWord ++ tailWord_6966565) baseStart_6966565 baseEnd_6966565 := by
    simpa [prefixWord, tailWord_6966565, baseEnd_6966565] using wordTrace_append hprefix tailTrace_6966565
  have hstable : (prefixWord ++ tailWord_6966565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966565).length < 2 ^ (prefixWord ++ tailWord_6966565).sum := by decide
  have hdescent : baseEnd_6966565 < baseStart_6966565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966589 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6966589 : Nat := 118140960795 + 6966589 * 2 ^ 59
def prefixEnd_6966589 : Nat := 4983230072969 + 3 ^ 40 * 6966589 * 2
def baseEnd_6966589 : Nat := 3577208679325348922198747

theorem tailTrace_6966589 : CollatzResearch.WordTrace tailWord_6966589 prefixEnd_6966589 3577208679325348922198747 := by
  unfold tailWord_6966589
  simp only [CollatzResearch.WordTrace]
  refine ⟨254092375358245326521598821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169394916905496884347732547 254092375358245326521598821)
  ·
    refine ⟨47642320379670998722799779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254092375358245326521598821 47642320379670998722799779)
    ·
      refine ⟨71463480569506498084199669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47642320379670998722799779 71463480569506498084199669)
      ·
        refine ⟨6699701303391234195393719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71463480569506498084199669 6699701303391234195393719)
        ·
          refine ⟨10049551955086851293090579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6699701303391234195393719 10049551955086851293090579)
          ·
            refine ⟨15074327932630276939635869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10049551955086851293090579 15074327932630276939635869)
            ·
              refine ⟨5652872974736353852363451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15074327932630276939635869 5652872974736353852363451)
              ·
                refine ⟨8479309462104530778545177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5652872974736353852363451 8479309462104530778545177)
                ·
                  refine ⟨6359482096578398083908883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479309462104530778545177 6359482096578398083908883)
                  ·
                    refine ⟨9539223144867597125863325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6359482096578398083908883 9539223144867597125863325)
                    ·
                      refine ⟨3577208679325348922198747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539223144867597125863325 3577208679325348922198747)
                      ·
                        rfl

theorem cell23_6966589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6966589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966589 prefixEnd_6966589 := by exact prefixLift 6966589
  have htrace : WordTrace (prefixWord ++ tailWord_6966589) baseStart_6966589 baseEnd_6966589 := by
    simpa [prefixWord, tailWord_6966589, baseEnd_6966589] using wordTrace_append hprefix tailTrace_6966589
  have hstable : (prefixWord ++ tailWord_6966589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966589).length < 2 ^ (prefixWord ++ tailWord_6966589).sum := by decide
  have hdescent : baseEnd_6966589 < baseStart_6966589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966591 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_6966591 : Nat := 118140960795 + 6966591 * 2 ^ 59
def prefixEnd_6966591 : Nat := 4983230072969 + 3 ^ 40 * 6966591 * 2
def baseEnd_6966591 : Nat := 3577209706286657914373737

theorem tailTrace_6966591 : CollatzResearch.WordTrace tailWord_6966591 prefixEnd_6966591 3577209706286657914373737 := by
  unfold tailWord_6966591
  simp only [CollatzResearch.WordTrace]
  refine ⟨254092448304238080863171627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169394965536158720575447751 254092448304238080863171627)
  ·
    refine ⟨381138672456357121294757441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254092448304238080863171627 381138672456357121294757441)
    ·
      refine ⟨285854004342267840971068081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381138672456357121294757441 285854004342267840971068081)
      ·
        refine ⟨214390503256700880728301061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285854004342267840971068081 214390503256700880728301061)
        ·
          refine ⟨40198219360631415136556449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214390503256700880728301061 40198219360631415136556449)
          ·
            refine ⟨30148664520473561352417337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40198219360631415136556449 30148664520473561352417337)
            ·
              refine ⟨22611498390355171014313003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30148664520473561352417337 22611498390355171014313003)
              ·
                refine ⟨33917247585532756521469505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22611498390355171014313003 33917247585532756521469505)
                ·
                  refine ⟨25437935689149567391102129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33917247585532756521469505 25437935689149567391102129)
                  ·
                    refine ⟨19078451766862175543326597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25437935689149567391102129 19078451766862175543326597)
                    ·
                      refine ⟨3577209706286657914373737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19078451766862175543326597 3577209706286657914373737)
                      ·
                        rfl

theorem cell23_6966591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_6966591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966591 prefixEnd_6966591 := by exact prefixLift 6966591
  have htrace : WordTrace (prefixWord ++ tailWord_6966591) baseStart_6966591 baseEnd_6966591 := by
    simpa [prefixWord, tailWord_6966591, baseEnd_6966591] using wordTrace_append hprefix tailTrace_6966591
  have hstable : (prefixWord ++ tailWord_6966591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966591).length < 2 ^ (prefixWord ++ tailWord_6966591).sum := by decide
  have hdescent : baseEnd_6966591 < baseStart_6966591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966618 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_6966618 : Nat := 118140960795 + 6966618 * 2 ^ 59
def prefixEnd_6966618 : Nat := 4983230072969 + 3 ^ 40 * 6966618 * 2
def baseEnd_6966618 : Nat := 397469285584925478748457

theorem tailTrace_6966618 : CollatzResearch.WordTrace tailWord_6966618 prefixEnd_6966618 397469285584925478748457 := by
  unfold tailWord_6966618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63523358268785066118601127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169395622050093509649603005 63523358268785066118601127)
  ·
    refine ⟨95285037403177599177901691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63523358268785066118601127 95285037403177599177901691)
    ·
      refine ⟨142927556104766398766852537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95285037403177599177901691 142927556104766398766852537)
      ·
        refine ⟨107195667078574799075139403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142927556104766398766852537 107195667078574799075139403)
        ·
          refine ⟨160793500617862198612709105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107195667078574799075139403 160793500617862198612709105)
          ·
            refine ⟨120595125463396648959531829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160793500617862198612709105 120595125463396648959531829)
            ·
              refine ⟨11305793012193435839956109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120595125463396648959531829 11305793012193435839956109)
              ·
                refine ⟨4239672379572538439983541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11305793012193435839956109 4239672379572538439983541)
                ·
                  refine ⟨397469285584925478748457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239672379572538439983541 397469285584925478748457)
                  ·
                    rfl

theorem cell23_6966618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_6966618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966618 prefixEnd_6966618 := by exact prefixLift 6966618
  have htrace : WordTrace (prefixWord ++ tailWord_6966618) baseStart_6966618 baseEnd_6966618 := by
    simpa [prefixWord, tailWord_6966618, baseEnd_6966618] using wordTrace_append hprefix tailTrace_6966618
  have hstable : (prefixWord ++ tailWord_6966618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966618).length < 2 ^ (prefixWord ++ tailWord_6966618).sum := by decide
  have hdescent : baseEnd_6966618 < baseStart_6966618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966651 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 4]
def baseStart_6966651 : Nat := 118140960795 + 6966651 * 2 ^ 59
def prefixEnd_6966651 : Nat := 4983230072969 + 3 ^ 40 * 6966651 * 2
def baseEnd_6966651 : Nat := 3577240515125927679623461

theorem tailTrace_6966651 : CollatzResearch.WordTrace tailWord_6966651 prefixEnd_6966651 3577240515125927679623461 := by
  unfold tailWord_6966651
  simp only [CollatzResearch.WordTrace]
  refine ⟨254094636684020711110355807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169396424456013807406903871 254094636684020711110355807)
  ·
    refine ⟨381141955026031066665533711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254094636684020711110355807 381141955026031066665533711)
    ·
      refine ⟨571712932539046599998300567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381141955026031066665533711 571712932539046599998300567)
      ·
        refine ⟨857569398808569899997450851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571712932539046599998300567 857569398808569899997450851)
        ·
          refine ⟨1286354098212854849996176277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857569398808569899997450851 1286354098212854849996176277)
          ·
            refine ⟨60297848353727571093570763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1286354098212854849996176277 60297848353727571093570763)
            ·
              refine ⟨90446772530591356640356145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60297848353727571093570763 90446772530591356640356145)
              ·
                refine ⟨67835079397943517480267109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90446772530591356640356145 67835079397943517480267109)
                ·
                  refine ⟨12719077387114409527550083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67835079397943517480267109 12719077387114409527550083)
                  ·
                    refine ⟨19078616080671614291325125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12719077387114409527550083 19078616080671614291325125)
                    ·
                      refine ⟨3577240515125927679623461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19078616080671614291325125 3577240515125927679623461)
                      ·
                        rfl

theorem cell23_6966651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 4].length) (baseStart_6966651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966651 prefixEnd_6966651 := by exact prefixLift 6966651
  have htrace : WordTrace (prefixWord ++ tailWord_6966651) baseStart_6966651 baseEnd_6966651 := by
    simpa [prefixWord, tailWord_6966651, baseEnd_6966651] using wordTrace_append hprefix tailTrace_6966651
  have hstable : (prefixWord ++ tailWord_6966651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966651).length < 2 ^ (prefixWord ++ tailWord_6966651).sum := by decide
  have hdescent : baseEnd_6966651 < baseStart_6966651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966668 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_6966668 : Nat := 118140960795 + 6966668 * 2 ^ 59
def prefixEnd_6966668 : Nat := 4983230072969 + 3 ^ 40 * 6966668 * 2
def baseEnd_6966668 : Nat := 3577249244297054113110883

theorem tailTrace_6966668 : CollatzResearch.WordTrace tailWord_6966668 prefixEnd_6966668 3577249244297054113110883 := by
  unfold tailWord_6966668
  simp only [CollatzResearch.WordTrace]
  refine ⟨127047628362479561506862329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169396837816639415342483105 127047628362479561506862329)
  ·
    refine ⟨95285721271859671130146747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127047628362479561506862329 95285721271859671130146747)
    ·
      refine ⟨142928581907789506695220121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95285721271859671130146747 142928581907789506695220121)
      ·
        refine ⟨107196436430842130021415091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142928581907789506695220121 107196436430842130021415091)
        ·
          refine ⟨160794654646263195032122637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107196436430842130021415091 160794654646263195032122637)
          ·
            refine ⟨60297995492348698137045989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160794654646263195032122637 60297995492348698137045989)
            ·
              refine ⟨11305874154815380900696123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60297995492348698137045989 11305874154815380900696123)
              ·
                refine ⟨16958811232223071351044185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305874154815380900696123 16958811232223071351044185)
                ·
                  refine ⟨12719108424167303513283139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16958811232223071351044185 12719108424167303513283139)
                  ·
                    refine ⟨19078662636250955269924709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12719108424167303513283139 19078662636250955269924709)
                    ·
                      refine ⟨3577249244297054113110883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19078662636250955269924709 3577249244297054113110883)
                      ·
                        rfl

theorem cell23_6966668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_6966668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966668 prefixEnd_6966668 := by exact prefixLift 6966668
  have htrace : WordTrace (prefixWord ++ tailWord_6966668) baseStart_6966668 baseEnd_6966668 := by
    simpa [prefixWord, tailWord_6966668, baseEnd_6966668] using wordTrace_append hprefix tailTrace_6966668
  have hstable : (prefixWord ++ tailWord_6966668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966668).length < 2 ^ (prefixWord ++ tailWord_6966668).sum := by decide
  have hdescent : baseEnd_6966668 < baseStart_6966668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966686 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_6966686 : Nat := 118140960795 + 6966686 * 2 ^ 59
def prefixEnd_6966686 : Nat := 4983230072969 + 3 ^ 40 * 6966686 * 2
def baseEnd_6966686 : Nat := 397473165216537226965089

theorem tailTrace_6966686 : CollatzResearch.WordTrace tailWord_6966686 prefixEnd_6966686 397473165216537226965089 := by
  unfold tailWord_6966686
  simp only [CollatzResearch.WordTrace]
  refine ⟨31761989154861739010984989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169397275492595941391919941 31761989154861739010984989)
  ·
    refine ⟨11910745933073152129119371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31761989154861739010984989 11910745933073152129119371)
    ·
      refine ⟨17866118899609728193679057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11910745933073152129119371 17866118899609728193679057)
      ·
        refine ⟨13399589174707296145259293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17866118899609728193679057 13399589174707296145259293)
        ·
          refine ⟨5024845940515236054472235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13399589174707296145259293 5024845940515236054472235)
          ·
            refine ⟨7537268910772854081708353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024845940515236054472235 7537268910772854081708353)
            ·
              refine ⟨5652951683079640561281265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537268910772854081708353 5652951683079640561281265)
              ·
                refine ⟨4239713762309730420960949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5652951683079640561281265 4239713762309730420960949)
                ·
                  refine ⟨397473165216537226965089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239713762309730420960949 397473165216537226965089)
                  ·
                    rfl

theorem cell23_6966686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_6966686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966686 prefixEnd_6966686 := by exact prefixLift 6966686
  have htrace : WordTrace (prefixWord ++ tailWord_6966686) baseStart_6966686 baseEnd_6966686 := by
    simpa [prefixWord, tailWord_6966686, baseEnd_6966686] using wordTrace_append hprefix tailTrace_6966686
  have hstable : (prefixWord ++ tailWord_6966686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966686).length < 2 ^ (prefixWord ++ tailWord_6966686).sum := by decide
  have hdescent : baseEnd_6966686 < baseStart_6966686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966688 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_6966688 : Nat := 118140960795 + 6966688 * 2 ^ 59
def prefixEnd_6966688 : Nat := 4983230072969 + 3 ^ 40 * 6966688 * 2
def baseEnd_6966688 : Nat := 3577259513910144034860791

theorem tailTrace_6966688 : CollatzResearch.WordTrace tailWord_6966688 prefixEnd_6966688 3577259513910144034860791 := by
  unfold tailWord_6966688
  simp only [CollatzResearch.WordTrace]
  refine ⟨127047993092443333214726359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169397324123257777619635145 127047993092443333214726359)
  ·
    refine ⟨190571989638664999822089539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127047993092443333214726359 190571989638664999822089539)
    ·
      refine ⟨285857984457997499733134309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190571989638664999822089539 285857984457997499733134309)
      ·
        refine ⟨53598372085874531199962683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285857984457997499733134309 53598372085874531199962683)
        ·
          refine ⟨80397558128811796799944025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53598372085874531199962683 80397558128811796799944025)
          ·
            refine ⟨60298168596608847599958019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80397558128811796799944025 60298168596608847599958019)
            ·
              refine ⟨90447252894913271399937029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60298168596608847599958019 90447252894913271399937029)
              ·
                refine ⟨16958859917796238387488193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90447252894913271399937029 16958859917796238387488193)
                ·
                  refine ⟨12719144938347178790616145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16958859917796238387488193 12719144938347178790616145)
                  ·
                    refine ⟨9539358703760384092962109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12719144938347178790616145 9539358703760384092962109)
                    ·
                      refine ⟨3577259513910144034860791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539358703760384092962109 3577259513910144034860791)
                      ·
                        rfl

theorem cell23_6966688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_6966688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966688 prefixEnd_6966688 := by exact prefixLift 6966688
  have htrace : WordTrace (prefixWord ++ tailWord_6966688) baseStart_6966688 baseEnd_6966688 := by
    simpa [prefixWord, tailWord_6966688, baseEnd_6966688] using wordTrace_append hprefix tailTrace_6966688
  have hstable : (prefixWord ++ tailWord_6966688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966688).length < 2 ^ (prefixWord ++ tailWord_6966688).sum := by decide
  have hdescent : baseEnd_6966688 < baseStart_6966688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966742 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_6966742 : Nat := 118140960795 + 6966742 * 2 ^ 59
def prefixEnd_6966742 : Nat := 4983230072969 + 3 ^ 40 * 6966742 * 2
def baseEnd_6966742 : Nat := 397476360207276313731727

theorem tailTrace_6966742 : CollatzResearch.WordTrace tailWord_6966742 prefixEnd_6966742 397476360207276313731727 := by
  unfold tailWord_6966742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881122232918189603244905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169398637151127355767945653 15881122232918189603244905)
  ·
    refine ⟨11910841674688642202433679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15881122232918189603244905 11910841674688642202433679)
    ·
      refine ⟨17866262512032963303650519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11910841674688642202433679 17866262512032963303650519)
      ·
        refine ⟨26799393768049444955475779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17866262512032963303650519 26799393768049444955475779)
        ·
          refine ⟨40199090652074167433213669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26799393768049444955475779 40199090652074167433213669)
          ·
            refine ⟨7537329497263906393727563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40199090652074167433213669 7537329497263906393727563)
            ·
              refine ⟨11305994245895859590591345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537329497263906393727563 11305994245895859590591345)
              ·
                refine ⟨8479495684421894692943509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11305994245895859590591345 8479495684421894692943509)
                ·
                  refine ⟨397476360207276313731727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8479495684421894692943509 397476360207276313731727)
                  ·
                    rfl

theorem cell23_6966742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_6966742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966742 prefixEnd_6966742 := by exact prefixLift 6966742
  have htrace : WordTrace (prefixWord ++ tailWord_6966742) baseStart_6966742 baseEnd_6966742 := by
    simpa [prefixWord, tailWord_6966742, baseEnd_6966742] using wordTrace_append hprefix tailTrace_6966742
  have hstable : (prefixWord ++ tailWord_6966742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966742).length < 2 ^ (prefixWord ++ tailWord_6966742).sum := by decide
  have hdescent : baseEnd_6966742 < baseStart_6966742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966768 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 1, 6]
def baseStart_6966768 : Nat := 118140960795 + 6966768 * 2 ^ 59
def prefixEnd_6966768 : Nat := 4983230072969 + 3 ^ 40 * 6966768 * 2
def baseEnd_6966768 : Nat := 1192433530787501240620141

theorem tailTrace_6966768 : CollatzResearch.WordTrace tailWord_6966768 prefixEnd_6966768 1192433530787501240620141 := by
  unfold tailWord_6966768
  simp only [CollatzResearch.WordTrace]
  refine ⟨127049452012298420046182479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169399269349731226728243305 127049452012298420046182479)
  ·
    refine ⟨190574178018447630069273719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127049452012298420046182479 190574178018447630069273719)
    ·
      refine ⟨285861267027671445103910579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190574178018447630069273719 285861267027671445103910579)
      ·
        refine ⟨428791900541507167655865869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285861267027671445103910579 428791900541507167655865869)
        ·
          refine ⟨160796962703065187870949701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428791900541507167655865869 160796962703065187870949701)
          ·
            refine ⟨30149430506824722725803069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160796962703065187870949701 30149430506824722725803069)
            ·
              refine ⟨11306036440059271022176151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30149430506824722725803069 11306036440059271022176151)
              ·
                refine ⟨16959054660088906533264227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306036440059271022176151 16959054660088906533264227)
                ·
                  refine ⟨25438581990133359799896341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16959054660088906533264227 25438581990133359799896341)
                  ·
                    refine ⟨1192433530787501240620141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25438581990133359799896341 1192433530787501240620141)
                    ·
                      rfl

theorem cell23_6966768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_6966768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966768 prefixEnd_6966768 := by exact prefixLift 6966768
  have htrace : WordTrace (prefixWord ++ tailWord_6966768) baseStart_6966768 baseEnd_6966768 := by
    simpa [prefixWord, tailWord_6966768, baseEnd_6966768] using wordTrace_append hprefix tailTrace_6966768
  have hstable : (prefixWord ++ tailWord_6966768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966768).length < 2 ^ (prefixWord ++ tailWord_6966768).sum := by decide
  have hdescent : baseEnd_6966768 < baseStart_6966768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966775 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 5, 2, 2]
def baseStart_6966775 : Nat := 118140960795 + 6966775 * 2 ^ 59
def prefixEnd_6966775 : Nat := 4983230072969 + 3 ^ 40 * 6966775 * 2
def baseEnd_6966775 : Nat := 3577304186727085194472891

theorem tailTrace_6966775 : CollatzResearch.WordTrace tailWord_6966775 prefixEnd_6966775 3577304186727085194472891 := by
  unfold tailWord_6966775
  simp only [CollatzResearch.WordTrace]
  refine ⟨254099159335571480287869779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169399439557047653525246519 254099159335571480287869779)
  ·
    refine ⟨381148739003357220431804669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254099159335571480287869779 381148739003357220431804669)
    ·
      refine ⟨142930777126258957661926751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381148739003357220431804669 142930777126258957661926751)
      ·
        refine ⟨214396165689388436492890127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142930777126258957661926751 214396165689388436492890127)
        ·
          refine ⟨321594248534082654739335191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214396165689388436492890127 321594248534082654739335191)
          ·
            refine ⟨482391372801123982109002787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321594248534082654739335191 482391372801123982109002787)
            ·
              refine ⟨723587059201685973163504181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482391372801123982109002787 723587059201685973163504181)
              ·
                refine ⟨67836286800158059984078517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 723587059201685973163504181 67836286800158059984078517)
                ·
                  refine ⟨6359651887514818123507361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67836286800158059984078517 6359651887514818123507361)
                  ·
                    refine ⟨4769738915636113592630521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6359651887514818123507361 4769738915636113592630521)
                    ·
                      refine ⟨3577304186727085194472891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769738915636113592630521 3577304186727085194472891)
                      ·
                        rfl

theorem cell23_6966775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_6966775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966775 prefixEnd_6966775 := by exact prefixLift 6966775
  have htrace : WordTrace (prefixWord ++ tailWord_6966775) baseStart_6966775 baseEnd_6966775 := by
    simpa [prefixWord, tailWord_6966775, baseEnd_6966775] using wordTrace_append hprefix tailTrace_6966775
  have hstable : (prefixWord ++ tailWord_6966775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966775).length < 2 ^ (prefixWord ++ tailWord_6966775).sum := by decide
  have hdescent : baseEnd_6966775 < baseStart_6966775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966786 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6966786 : Nat := 118140960795 + 6966786 * 2 ^ 59
def prefixEnd_6966786 : Nat := 4983230072969 + 3 ^ 40 * 6966786 * 2
def baseEnd_6966786 : Nat := 3577309835014284651435341

theorem tailTrace_6966786 : CollatzResearch.WordTrace tailWord_6966786 prefixEnd_6966786 3577309835014284651435341 := by
  unfold tailWord_6966786
  simp only [CollatzResearch.WordTrace]
  refine ⟨63524890134632907291630053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169399707025687752777680141 63524890134632907291630053)
  ·
    refine ⟨11910916900243670117180635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63524890134632907291630053 11910916900243670117180635)
    ·
      refine ⟨17866375350365505175770953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11910916900243670117180635 17866375350365505175770953)
      ·
        refine ⟨13399781512774128881828215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17866375350365505175770953 13399781512774128881828215)
        ·
          refine ⟨20099672269161193322742323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399781512774128881828215 20099672269161193322742323)
          ·
            refine ⟨30149508403741789984113485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20099672269161193322742323 30149508403741789984113485)
            ·
              refine ⟨11306065651403171244042557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30149508403741789984113485 11306065651403171244042557)
              ·
                refine ⟨4239774619276189216515959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11306065651403171244042557 4239774619276189216515959)
                ·
                  refine ⟨6359661928914283824773939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239774619276189216515959 6359661928914283824773939)
                  ·
                    refine ⟨9539492893371425737160909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6359661928914283824773939 9539492893371425737160909)
                    ·
                      refine ⟨3577309835014284651435341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9539492893371425737160909 3577309835014284651435341)
                      ·
                        rfl

theorem cell23_6966786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6966786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966786 prefixEnd_6966786 := by exact prefixLift 6966786
  have htrace : WordTrace (prefixWord ++ tailWord_6966786) baseStart_6966786 baseEnd_6966786 := by
    simpa [prefixWord, tailWord_6966786, baseEnd_6966786] using wordTrace_append hprefix tailTrace_6966786
  have hstable : (prefixWord ++ tailWord_6966786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966786).length < 2 ^ (prefixWord ++ tailWord_6966786).sum := by decide
  have hdescent : baseEnd_6966786 < baseStart_6966786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966795 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 5]
def baseStart_6966795 : Nat := 118140960795 + 6966795 * 2 ^ 59
def prefixEnd_6966795 : Nat := 4983230072969 + 3 ^ 40 * 6966795 * 2
def baseEnd_6966795 : Nat := 3577314456340175116222799

theorem tailTrace_6966795 : CollatzResearch.WordTrace tailWord_6966795 prefixEnd_6966795 3577314456340175116222799 := by
  unfold tailWord_6966795
  simp only [CollatzResearch.WordTrace]
  refine ⟨254099888795499023703597839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169399925863666015802398559 254099888795499023703597839)
  ·
    refine ⟨381149833193248535555396759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254099888795499023703597839 381149833193248535555396759)
    ·
      refine ⟨571724749789872803333095139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381149833193248535555396759 571724749789872803333095139)
      ·
        refine ⟨857587124684809204999642709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571724749789872803333095139 857587124684809204999642709)
        ·
          refine ⟨10049849117400107871089563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 857587124684809204999642709 10049849117400107871089563)
          ·
            refine ⟨15074773676100161806634345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10049849117400107871089563 15074773676100161806634345)
            ·
              refine ⟨11306080257075121354975759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15074773676100161806634345 11306080257075121354975759)
              ·
                refine ⟨16959120385612682032463639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306080257075121354975759 16959120385612682032463639)
                ·
                  refine ⟨25438680578419023048695459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16959120385612682032463639 25438680578419023048695459)
                  ·
                    refine ⟨38158020867628534573043189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25438680578419023048695459 38158020867628534573043189)
                    ·
                      refine ⟨3577314456340175116222799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38158020867628534573043189 3577314456340175116222799)
                      ·
                        rfl

theorem cell23_6966795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 5].length) (baseStart_6966795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966795 prefixEnd_6966795 := by exact prefixLift 6966795
  have htrace : WordTrace (prefixWord ++ tailWord_6966795) baseStart_6966795 baseEnd_6966795 := by
    simpa [prefixWord, tailWord_6966795, baseEnd_6966795] using wordTrace_append hprefix tailTrace_6966795
  have hstable : (prefixWord ++ tailWord_6966795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966795).length < 2 ^ (prefixWord ++ tailWord_6966795).sum := by decide
  have hdescent : baseEnd_6966795 < baseStart_6966795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966819 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 2, 4]
def baseStart_6966819 : Nat := 118140960795 + 6966819 * 2 ^ 59
def prefixEnd_6966819 : Nat := 4983230072969 + 3 ^ 40 * 6966819 * 2
def baseEnd_6966819 : Nat := 1192442259958627674107563

theorem tailTrace_6966819 : CollatzResearch.WordTrace tailWord_6966819 prefixEnd_6966819 1192442259958627674107563 := by
  unfold tailWord_6966819
  simp only [CollatzResearch.WordTrace]
  refine ⟨254100764147412075802471511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169400509431608050534981007 254100764147412075802471511)
  ·
    refine ⟨381151146221118113703707267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254100764147412075802471511 381151146221118113703707267)
    ·
      refine ⟨571726719331677170555560901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381151146221118113703707267 571726719331677170555560901)
      ·
        refine ⟨107198759874689469479167669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 571726719331677170555560901 107198759874689469479167669)
        ·
          refine ⟨10049883738252137763671969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107198759874689469479167669 10049883738252137763671969)
          ·
            refine ⟨7537412803689103322753977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10049883738252137763671969 7537412803689103322753977)
            ·
              refine ⟨5653059602766827492065483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537412803689103322753977 5653059602766827492065483)
              ·
                refine ⟨8479589404150241238098225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653059602766827492065483 8479589404150241238098225)
                ·
                  refine ⟨6359692053112680928573669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479589404150241238098225 6359692053112680928573669)
                  ·
                    refine ⟨1192442259958627674107563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359692053112680928573669 1192442259958627674107563)
                    ·
                      rfl

theorem cell23_6966819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 4].length) (baseStart_6966819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966819 prefixEnd_6966819 := by exact prefixLift 6966819
  have htrace : WordTrace (prefixWord ++ tailWord_6966819) baseStart_6966819 baseEnd_6966819 := by
    simpa [prefixWord, tailWord_6966819, baseEnd_6966819] using wordTrace_append hprefix tailTrace_6966819
  have hstable : (prefixWord ++ tailWord_6966819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966819).length < 2 ^ (prefixWord ++ tailWord_6966819).sum := by decide
  have hdescent : baseEnd_6966819 < baseStart_6966819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966858 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_6966858 : Nat := 118140960795 + 6966858 * 2 ^ 59
def prefixEnd_6966858 : Nat := 4983230072969 + 3 ^ 40 * 6966858 * 2
def baseEnd_6966858 : Nat := 1192448935207136123245003

theorem tailTrace_6966858 : CollatzResearch.WordTrace tailWord_6966858 prefixEnd_6966858 1192448935207136123245003 := by
  unfold tailWord_6966858
  simp only [CollatzResearch.WordTrace]
  refine ⟨63525546648567696365785307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169401457729513856975427485 63525546648567696365785307)
  ·
    refine ⟨95288319972851544548677961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63525546648567696365785307 95288319972851544548677961)
    ·
      refine ⟨71466239979638658411508471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95288319972851544548677961 71466239979638658411508471)
      ·
        refine ⟨107199359969457987617262707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71466239979638658411508471 107199359969457987617262707)
        ·
          refine ⟨160799039954186981425894061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107199359969457987617262707 160799039954186981425894061)
          ·
            refine ⟨60299639982820118034710273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160799039954186981425894061 60299639982820118034710273)
            ·
              refine ⟨45224729987115088526032705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60299639982820118034710273 45224729987115088526032705)
              ·
                refine ⟨33918547490336316394524529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45224729987115088526032705 33918547490336316394524529)
                ·
                  refine ⟨25438910617752237295893397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33918547490336316394524529 25438910617752237295893397)
                  ·
                    refine ⟨1192448935207136123245003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25438910617752237295893397 1192448935207136123245003)
                    ·
                      rfl

theorem cell23_6966858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_6966858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966858 prefixEnd_6966858 := by exact prefixLift 6966858
  have htrace : WordTrace (prefixWord ++ tailWord_6966858) baseStart_6966858 baseEnd_6966858 := by
    simpa [prefixWord, tailWord_6966858, baseEnd_6966858] using wordTrace_append hprefix tailTrace_6966858
  have hstable : (prefixWord ++ tailWord_6966858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966858).length < 2 ^ (prefixWord ++ tailWord_6966858).sum := by decide
  have hdescent : baseEnd_6966858 < baseStart_6966858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966865 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 3, 4, 2]
def baseStart_6966865 : Nat := 118140960795 + 6966865 * 2 ^ 59
def prefixEnd_6966865 : Nat := 4983230072969 + 3 ^ 40 * 6966865 * 2
def baseEnd_6966865 : Nat := 3577350399985989842347477

theorem tailTrace_6966865 : CollatzResearch.WordTrace tailWord_6966865 prefixEnd_6966865 3577350399985989842347477 := by
  unfold tailWord_6966865
  simp only [CollatzResearch.WordTrace]
  refine ⟨254102441905245425658646049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169401627936830283772430699 254102441905245425658646049)
  ·
    refine ⟨190576831428934069243984537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254102441905245425658646049 190576831428934069243984537)
    ·
      refine ⟨142932623571700551932988403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190576831428934069243984537 142932623571700551932988403)
      ·
        refine ⟨214398935357550827899482605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142932623571700551932988403 214398935357550827899482605)
        ·
          refine ⟨80399600759081560462305977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214398935357550827899482605 80399600759081560462305977)
          ·
            refine ⟨60299700569311170346729483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80399600759081560462305977 60299700569311170346729483)
            ·
              refine ⟨90449550853966755520094225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60299700569311170346729483 90449550853966755520094225)
              ·
                refine ⟨67837163140475066640070669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90449550853966755520094225 67837163140475066640070669)
                ·
                  refine ⟨25438936177678149990026501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67837163140475066640070669 25438936177678149990026501)
                  ·
                    refine ⟨4769800533314653123129969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25438936177678149990026501 4769800533314653123129969)
                    ·
                      refine ⟨3577350399985989842347477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4769800533314653123129969 3577350399985989842347477)
                      ·
                        rfl

theorem cell23_6966865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_6966865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966865 prefixEnd_6966865 := by exact prefixLift 6966865
  have htrace : WordTrace (prefixWord ++ tailWord_6966865) baseStart_6966865 baseEnd_6966865 := by
    simpa [prefixWord, tailWord_6966865, baseEnd_6966865] using wordTrace_append hprefix tailTrace_6966865
  have hstable : (prefixWord ++ tailWord_6966865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966865).length < 2 ^ (prefixWord ++ tailWord_6966865).sum := by decide
  have hdescent : baseEnd_6966865 < baseStart_6966865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966922 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_6966922 : Nat := 118140960795 + 6966922 * 2 ^ 59
def prefixEnd_6966922 : Nat := 4983230072969 + 3 ^ 40 * 6966922 * 2
def baseEnd_6966922 : Nat := 397486629820366235481635

theorem tailTrace_6966922 : CollatzResearch.WordTrace tailWord_6966922 prefixEnd_6966922 397486629820366235481635 := by
  unfold tailWord_6966922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63526130216509731098367755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169403013910692616262314013 63526130216509731098367755)
  ·
    refine ⟨95289195324764596647551633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63526130216509731098367755 95289195324764596647551633)
    ·
      refine ⟨71466896493573447485663725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95289195324764596647551633 71466896493573447485663725)
      ·
        refine ⟨26800086185090042807123897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71466896493573447485663725 26800086185090042807123897)
        ·
          refine ⟨20100064638817532105342923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26800086185090042807123897 20100064638817532105342923)
          ·
            refine ⟨30150096958226298158014385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20100064638817532105342923 30150096958226298158014385)
            ·
              refine ⟨22612572718669723618510789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30150096958226298158014385 22612572718669723618510789)
              ·
                refine ⟨4239857384750573178470773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22612572718669723618510789 4239857384750573178470773)
                ·
                  refine ⟨397486629820366235481635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239857384750573178470773 397486629820366235481635)
                  ·
                    rfl

theorem cell23_6966922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_6966922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966922 prefixEnd_6966922 := by exact prefixLift 6966922
  have htrace : WordTrace (prefixWord ++ tailWord_6966922) baseStart_6966922 baseEnd_6966922 := by
    simpa [prefixWord, tailWord_6966922, baseEnd_6966922] using wordTrace_append hprefix tailTrace_6966922
  have hstable : (prefixWord ++ tailWord_6966922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966922).length < 2 ^ (prefixWord ++ tailWord_6966922).sum := by decide
  have hdescent : baseEnd_6966922 < baseStart_6966922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966928 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_6966928 : Nat := 118140960795 + 6966928 * 2 ^ 59
def prefixEnd_6966928 : Nat := 4983230072969 + 3 ^ 40 * 6966928 * 2
def baseEnd_6966928 : Nat := 3577382749267223095859687

theorem tailTrace_6966928 : CollatzResearch.WordTrace tailWord_6966928 prefixEnd_6966928 3577382749267223095859687 := by
  unfold tailWord_6966928
  simp only [CollatzResearch.WordTrace]
  refine ⟨127052369852008593709094719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169403159802678124945459625 127052369852008593709094719)
  ·
    refine ⟨190578554778012890563642079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127052369852008593709094719 190578554778012890563642079)
    ·
      refine ⟨285867832167019335845463119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190578554778012890563642079 285867832167019335845463119)
      ·
        refine ⟨428801748250529003768194679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285867832167019335845463119 428801748250529003768194679)
        ·
          refine ⟨643202622375793505652292019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428801748250529003768194679 643202622375793505652292019)
          ·
            refine ⟨964803933563690258478438029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643202622375793505652292019 964803933563690258478438029)
            ·
              refine ⟨361801475086383846929414261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964803933563690258478438029 361801475086383846929414261)
              ·
                refine ⟨33918888289348485649632587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361801475086383846929414261 33918888289348485649632587)
                ·
                  refine ⟨50878332434022728474448881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33918888289348485649632587 50878332434022728474448881)
                  ·
                    refine ⟨38158749325517046355836661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50878332434022728474448881 38158749325517046355836661)
                    ·
                      refine ⟨3577382749267223095859687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38158749325517046355836661 3577382749267223095859687)
                      ·
                        rfl

theorem cell23_6966928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_6966928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966928 prefixEnd_6966928 := by exact prefixLift 6966928
  have htrace : WordTrace (prefixWord ++ tailWord_6966928) baseStart_6966928 baseEnd_6966928 := by
    simpa [prefixWord, tailWord_6966928, baseEnd_6966928] using wordTrace_append hprefix tailTrace_6966928
  have hstable : (prefixWord ++ tailWord_6966928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966928).length < 2 ^ (prefixWord ++ tailWord_6966928).sum := by decide
  have hdescent : baseEnd_6966928 < baseStart_6966928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6966968 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_6966968 : Nat := 118140960795 + 6966968 * 2 ^ 59
def prefixEnd_6966968 : Nat := 4983230072969 + 3 ^ 40 * 6966968 * 2
def baseEnd_6966968 : Nat := 3577403288493402939359503

theorem tailTrace_6966968 : CollatzResearch.WordTrace tailWord_6966968 prefixEnd_6966968 3577403288493402939359503 := by
  unfold tailWord_6966968
  simp only [CollatzResearch.WordTrace]
  refine ⟨127053099311936137124822779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169404132415914849499763705 127053099311936137124822779)
  ·
    refine ⟨190579648967904205687234169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127053099311936137124822779 190579648967904205687234169)
    ·
      refine ⟨142934736725928154265425627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190579648967904205687234169 142934736725928154265425627)
      ·
        refine ⟨214402105088892231398138441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142934736725928154265425627 214402105088892231398138441)
        ·
          refine ⟨160801578816669173548603831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214402105088892231398138441 160801578816669173548603831)
          ·
            refine ⟨241202368225003760322905747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160801578816669173548603831 241202368225003760322905747)
            ·
              refine ⟨361803552337505640484358621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241202368225003760322905747 361803552337505640484358621)
              ·
                refine ⟨135676332126564615181634483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361803552337505640484358621 135676332126564615181634483)
                ·
                  refine ⟨203514498189846922772451725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135676332126564615181634483 203514498189846922772451725)
                  ·
                    refine ⟨76317936821192596039669397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203514498189846922772451725 76317936821192596039669397)
                    ·
                      refine ⟨3577403288493402939359503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76317936821192596039669397 3577403288493402939359503)
                      ·
                        rfl

theorem cell23_6966968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_6966968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6966968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6966968 prefixEnd_6966968 := by exact prefixLift 6966968
  have htrace : WordTrace (prefixWord ++ tailWord_6966968) baseStart_6966968 baseEnd_6966968 := by
    simpa [prefixWord, tailWord_6966968, baseEnd_6966968] using wordTrace_append hprefix tailTrace_6966968
  have hstable : (prefixWord ++ tailWord_6966968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6966968).length < 2 ^ (prefixWord ++ tailWord_6966968).sum := by decide
  have hdescent : baseEnd_6966968 < baseStart_6966968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6966968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
