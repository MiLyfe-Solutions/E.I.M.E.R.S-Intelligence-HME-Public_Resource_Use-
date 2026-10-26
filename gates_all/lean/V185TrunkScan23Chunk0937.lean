import V185TrunkScan23Chunk0936

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5545812 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_5545812 : Nat := 118140960795 + 5545812 * 2 ^ 59
def prefixEnd_5545812 : Nat := 4983230072969 + 3 ^ 40 * 5545812 * 2
def baseEnd_5545812 : Nat := 949222391824120406248427

theorem tailTrace_5545812 : CollatzResearch.WordTrace tailWord_5545812 prefixEnd_5545812 949222391824120406248427 := by
  unfold tailWord_5545812
  simp only [CollatzResearch.WordTrace]
  refine ⟨101136190492238874064151845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134848253989651832085535793 101136190492238874064151845)
  ·
    refine ⟨18963035717294788887028471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101136190492238874064151845 18963035717294788887028471)
    ·
      refine ⟨28444553575942183330542707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18963035717294788887028471 28444553575942183330542707)
      ·
        refine ⟨42666830363913274995814061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28444553575942183330542707 42666830363913274995814061)
        ·
          refine ⟨16000061386467478123430273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42666830363913274995814061 16000061386467478123430273)
          ·
            refine ⟨12000046039850608592572705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16000061386467478123430273 12000046039850608592572705)
            ·
              refine ⟨9000034529887956444429529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12000046039850608592572705 9000034529887956444429529)
              ·
                refine ⟨6750025897415967333322147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9000034529887956444429529 6750025897415967333322147)
                ·
                  refine ⟨10125038846123950999983221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750025897415967333322147 10125038846123950999983221)
                  ·
                    refine ⟨949222391824120406248427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10125038846123950999983221 949222391824120406248427)
                    ·
                      rfl

theorem cell23_5545812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_5545812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545812 prefixEnd_5545812 := by exact prefixLift 5545812
  have htrace : WordTrace (prefixWord ++ tailWord_5545812) baseStart_5545812 baseEnd_5545812 := by
    simpa [prefixWord, tailWord_5545812, baseEnd_5545812] using wordTrace_append hprefix tailTrace_5545812
  have hstable : (prefixWord ++ tailWord_5545812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545812).length < 2 ^ (prefixWord ++ tailWord_5545812).sum := by decide
  have hdescent : baseEnd_5545812 < baseStart_5545812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545818 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_5545818 : Nat := 118140960795 + 5545818 * 2 ^ 59
def prefixEnd_5545818 : Nat := 4983230072969 + 3 ^ 40 * 5545818 * 2
def baseEnd_5545818 : Nat := 2847670256356288195270253

theorem tailTrace_5545818 : CollatzResearch.WordTrace tailWord_5545818 prefixEnd_5545818 2847670256356288195270253 := by
  unfold tailWord_5545818
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568149955614002788255527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134848399881637340768681405 50568149955614002788255527)
  ·
    refine ⟨75852224933421004182383291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50568149955614002788255527 75852224933421004182383291)
    ·
      refine ⟨113778337400131506273574937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75852224933421004182383291 113778337400131506273574937)
      ·
        refine ⟨85333753050098629705181203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113778337400131506273574937 85333753050098629705181203)
        ·
          refine ⟨128000629575147944557771805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85333753050098629705181203 128000629575147944557771805)
          ·
            refine ⟨48000236090680479209164427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128000629575147944557771805 48000236090680479209164427)
            ·
              refine ⟨72000354136020718813746641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48000236090680479209164427 72000354136020718813746641)
              ·
                refine ⟨54000265602015539110309981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72000354136020718813746641 54000265602015539110309981)
                ·
                  refine ⟨20250099600755827166366243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54000265602015539110309981 20250099600755827166366243)
                  ·
                    refine ⟨30375149401133740749549365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20250099600755827166366243 30375149401133740749549365)
                    ·
                      refine ⟨2847670256356288195270253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30375149401133740749549365 2847670256356288195270253)
                      ·
                        rfl

theorem cell23_5545818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_5545818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545818 prefixEnd_5545818 := by exact prefixLift 5545818
  have htrace : WordTrace (prefixWord ++ tailWord_5545818) baseStart_5545818 baseEnd_5545818 := by
    simpa [prefixWord, tailWord_5545818, baseEnd_5545818] using wordTrace_append hprefix tailTrace_5545818
  have hstable : (prefixWord ++ tailWord_5545818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545818).length < 2 ^ (prefixWord ++ tailWord_5545818).sum := by decide
  have hdescent : baseEnd_5545818 < baseStart_5545818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545826 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_5545826 : Nat := 118140960795 + 5545826 * 2 ^ 59
def prefixEnd_5545826 : Nat := 4983230072969 + 3 ^ 40 * 5545826 * 2
def baseEnd_5545826 : Nat := 2847674364201524163970217

theorem tailTrace_5545826 : CollatzResearch.WordTrace tailWord_5545826 prefixEnd_5545826 2847674364201524163970217 := by
  unfold tailWord_5545826
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568222901606757129828333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134848594404284685679542221 50568222901606757129828333)
  ·
    refine ⟨18963083588102533923685625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50568222901606757129828333 18963083588102533923685625)
    ·
      refine ⟨14222312691076900442764219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18963083588102533923685625 14222312691076900442764219)
      ·
        refine ⟨21333469036615350664146329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14222312691076900442764219 21333469036615350664146329)
        ·
          refine ⟨16000101777461512998109747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21333469036615350664146329 16000101777461512998109747)
          ·
            refine ⟨24000152666192269497164621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16000101777461512998109747 24000152666192269497164621)
            ·
              refine ⟨9000057249822101061436733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24000152666192269497164621 9000057249822101061436733)
              ·
                refine ⟨3375021468683287898038775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9000057249822101061436733 3375021468683287898038775)
                ·
                  refine ⟨5062532203024931847058163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375021468683287898038775 5062532203024931847058163)
                  ·
                    refine ⟨7593798304537397770587245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062532203024931847058163 7593798304537397770587245)
                    ·
                      refine ⟨2847674364201524163970217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593798304537397770587245 2847674364201524163970217)
                      ·
                        rfl

theorem cell23_5545826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_5545826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545826 prefixEnd_5545826 := by exact prefixLift 5545826
  have htrace : WordTrace (prefixWord ++ tailWord_5545826) baseStart_5545826 baseEnd_5545826 := by
    simpa [prefixWord, tailWord_5545826, baseEnd_5545826] using wordTrace_append hprefix tailTrace_5545826
  have hstable : (prefixWord ++ tailWord_5545826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545826).length < 2 ^ (prefixWord ++ tailWord_5545826).sum := by decide
  have hdescent : baseEnd_5545826 < baseStart_5545826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545859 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 2, 4]
def baseStart_5545859 : Nat := 118140960795 + 5545859 * 2 ^ 59
def prefixEnd_5545859 : Nat := 4983230072969 + 3 ^ 40 * 5545859 * 2
def baseEnd_5545859 : Nat := 949230436354374178285855

theorem tailTrace_5545859 : CollatzResearch.WordTrace tailWord_5545859 prefixEnd_5545859 949230436354374178285855 := by
  unfold tailWord_5545859
  simp only [CollatzResearch.WordTrace]
  refine ⟨202274095215307475155264631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134849396810204983436843087 202274095215307475155264631)
  ·
    refine ⟨303411142822961212732896947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202274095215307475155264631 303411142822961212732896947)
    ·
      refine ⟨455116714234441819099345421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303411142822961212732896947 455116714234441819099345421)
      ·
        refine ⟨170668767837915682162254533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455116714234441819099345421 170668767837915682162254533)
        ·
          refine ⟨32000393969609190405422725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170668767837915682162254533 32000393969609190405422725)
          ·
            refine ⟨6000073869301723201016761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32000393969609190405422725 6000073869301723201016761)
            ·
              refine ⟨4500055401976292400762571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6000073869301723201016761 4500055401976292400762571)
              ·
                refine ⟨6750083102964438601143857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500055401976292400762571 6750083102964438601143857)
                ·
                  refine ⟨5062562327223328950857893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750083102964438601143857 5062562327223328950857893)
                  ·
                    refine ⟨949230436354374178285855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5062562327223328950857893 949230436354374178285855)
                    ·
                      rfl

theorem cell23_5545859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 4].length) (baseStart_5545859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545859 prefixEnd_5545859 := by exact prefixLift 5545859
  have htrace : WordTrace (prefixWord ++ tailWord_5545859) baseStart_5545859 baseEnd_5545859 := by
    simpa [prefixWord, tailWord_5545859, baseEnd_5545859] using wordTrace_append hprefix tailTrace_5545859
  have hstable : (prefixWord ++ tailWord_5545859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545859).length < 2 ^ (prefixWord ++ tailWord_5545859).sum := by decide
  have hdescent : baseEnd_5545859 < baseStart_5545859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545865 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_5545865 : Nat := 118140960795 + 5545865 * 2 ^ 59
def prefixEnd_5545865 : Nat := 4983230072969 + 3 ^ 40 * 5545865 * 2
def baseEnd_5545865 : Nat := 2847694389947049511382537

theorem tailTrace_5545865 : CollatzResearch.WordTrace tailWord_5545865 prefixEnd_5545865 2847694389947049511382537 := by
  unfold tailWord_5545865
  simp only [CollatzResearch.WordTrace]
  refine ⟨202274314053285738179983049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134849542702190492119988699 202274314053285738179983049)
  ·
    refine ⟨151705735539964303634987287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202274314053285738179983049 151705735539964303634987287)
    ·
      refine ⟨227558603309946455452480931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151705735539964303634987287 227558603309946455452480931)
      ·
        refine ⟨341337904964919683178721397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227558603309946455452480931 341337904964919683178721397)
        ·
          refine ⟨32000428590461220298005131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 341337904964919683178721397 32000428590461220298005131)
          ·
            refine ⟨48000642885691830447007697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32000428590461220298005131 48000642885691830447007697)
            ·
              refine ⟨36000482164268872835255773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48000642885691830447007697 36000482164268872835255773)
              ·
                refine ⟨13500180811600827313220915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36000482164268872835255773 13500180811600827313220915)
                ·
                  refine ⟨20250271217401240969831373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13500180811600827313220915 20250271217401240969831373)
                  ·
                    refine ⟨7593851706525465363686765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20250271217401240969831373 7593851706525465363686765)
                    ·
                      refine ⟨2847694389947049511382537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593851706525465363686765 2847694389947049511382537)
                      ·
                        rfl

theorem cell23_5545865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_5545865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545865 prefixEnd_5545865 := by exact prefixLift 5545865
  have htrace : WordTrace (prefixWord ++ tailWord_5545865) baseStart_5545865 baseEnd_5545865 := by
    simpa [prefixWord, tailWord_5545865, baseEnd_5545865] using wordTrace_append hprefix tailTrace_5545865
  have hstable : (prefixWord ++ tailWord_5545865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545865).length < 2 ^ (prefixWord ++ tailWord_5545865).sum := by decide
  have hdescent : baseEnd_5545865 < baseStart_5545865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545866 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_5545866 : Nat := 118140960795 + 5545866 * 2 ^ 59
def prefixEnd_5545866 : Nat := 4983230072969 + 3 ^ 40 * 5545866 * 2
def baseEnd_5545866 : Nat := 2847694903427704007470033

theorem tailTrace_5545866 : CollatzResearch.WordTrace tailWord_5545866 prefixEnd_5545866 2847694903427704007470033 := by
  unfold tailWord_5545866
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568587631570528837692363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134849567017521410233846301 50568587631570528837692363)
  ·
    refine ⟨75852881447355793256538545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50568587631570528837692363 75852881447355793256538545)
    ·
      refine ⟨56889661085516844942403909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75852881447355793256538545 56889661085516844942403909)
      ·
        refine ⟨10666811453534408426700733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56889661085516844942403909 10666811453534408426700733)
        ·
          refine ⟨4000054295075403160012775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10666811453534408426700733 4000054295075403160012775)
          ·
            refine ⟨6000081442613104740019163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000054295075403160012775 6000081442613104740019163)
            ·
              refine ⟨9000122163919657110028745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000081442613104740019163 9000122163919657110028745)
              ·
                refine ⟨6750091622939742832521559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9000122163919657110028745 6750091622939742832521559)
                ·
                  refine ⟨10125137434409614248782339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750091622939742832521559 10125137434409614248782339)
                  ·
                    refine ⟨15187706151614421373173509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10125137434409614248782339 15187706151614421373173509)
                    ·
                      refine ⟨2847694903427704007470033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15187706151614421373173509 2847694903427704007470033)
                      ·
                        rfl

theorem cell23_5545866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_5545866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545866 prefixEnd_5545866 := by exact prefixLift 5545866
  have htrace : WordTrace (prefixWord ++ tailWord_5545866) baseStart_5545866 baseEnd_5545866 := by
    simpa [prefixWord, tailWord_5545866, baseEnd_5545866] using wordTrace_append hprefix tailTrace_5545866
  have hstable : (prefixWord ++ tailWord_5545866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545866).length < 2 ^ (prefixWord ++ tailWord_5545866).sum := by decide
  have hdescent : baseEnd_5545866 < baseStart_5545866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545882 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5545882 : Nat := 118140960795 + 5545882 * 2 ^ 59
def prefixEnd_5545882 : Nat := 4983230072969 + 3 ^ 40 * 5545882 * 2
def baseEnd_5545882 : Nat := 2847703119118175944869959

theorem tailTrace_5545882 : CollatzResearch.WordTrace tailWord_5545882 prefixEnd_5545882 2847703119118175944869959 := by
  unfold tailWord_5545882
  simp only [CollatzResearch.WordTrace]
  refine ⟨50568733523556037520837975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134849956062816100055567933 50568733523556037520837975)
  ·
    refine ⟨75853100285334056281256963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50568733523556037520837975 75853100285334056281256963)
    ·
      refine ⟨113779650428001084421885445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75853100285334056281256963 113779650428001084421885445)
      ·
        refine ⟨21333684455250203329103521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113779650428001084421885445 21333684455250203329103521)
        ·
          refine ⟨16000263341437652496827641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21333684455250203329103521 16000263341437652496827641)
          ·
            refine ⟨12000197506078239372620731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16000263341437652496827641 12000197506078239372620731)
            ·
              refine ⟨18000296259117359058931097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12000197506078239372620731 18000296259117359058931097)
              ·
                refine ⟨13500222194338019294198323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18000296259117359058931097 13500222194338019294198323)
                ·
                  refine ⟨20250333291507028941297485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13500222194338019294198323 20250333291507028941297485)
                  ·
                    refine ⟨7593874984315135852986557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20250333291507028941297485 7593874984315135852986557)
                    ·
                      refine ⟨2847703119118175944869959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593874984315135852986557 2847703119118175944869959)
                      ·
                        rfl

theorem cell23_5545882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5545882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545882 prefixEnd_5545882 := by exact prefixLift 5545882
  have htrace : WordTrace (prefixWord ++ tailWord_5545882) baseStart_5545882 baseEnd_5545882 := by
    simpa [prefixWord, tailWord_5545882, baseEnd_5545882] using wordTrace_append hprefix tailTrace_5545882
  have hstable : (prefixWord ++ tailWord_5545882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545882).length < 2 ^ (prefixWord ++ tailWord_5545882).sum := by decide
  have hdescent : baseEnd_5545882 < baseStart_5545882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545886 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5545886 : Nat := 118140960795 + 5545886 * 2 ^ 59
def prefixEnd_5545886 : Nat := 4983230072969 + 3 ^ 40 * 5545886 * 2
def baseEnd_5545886 : Nat := 2847705173040793929219941

theorem tailTrace_5545886 : CollatzResearch.WordTrace tailWord_5545886 prefixEnd_5545886 2847705173040793929219941 := by
  unfold tailWord_5545886
  simp only [CollatzResearch.WordTrace]
  refine ⟨25284384998276207345812189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134850053324139772510998341 25284384998276207345812189)
  ·
    refine ⟨9481644374353577754679571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25284384998276207345812189 9481644374353577754679571)
    ·
      refine ⟨14222466561530366632019357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9481644374353577754679571 14222466561530366632019357)
      ·
        refine ⟨5333424960573887487007259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14222466561530366632019357 5333424960573887487007259)
        ·
          refine ⟨8000137440860831230510889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333424960573887487007259 8000137440860831230510889)
          ·
            refine ⟨6000103080645623422883167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8000137440860831230510889 6000103080645623422883167)
            ·
              refine ⟨9000154620968435134324751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000103080645623422883167 9000154620968435134324751)
              ·
                refine ⟨13500231931452652701487127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9000154620968435134324751 13500231931452652701487127)
                ·
                  refine ⟨20250347897178979052230691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13500231931452652701487127 20250347897178979052230691)
                  ·
                    refine ⟨30375521845768468578346037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20250347897178979052230691 30375521845768468578346037)
                    ·
                      refine ⟨2847705173040793929219941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30375521845768468578346037 2847705173040793929219941)
                      ·
                        rfl

theorem cell23_5545886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5545886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545886 prefixEnd_5545886 := by exact prefixLift 5545886
  have htrace : WordTrace (prefixWord ++ tailWord_5545886) baseStart_5545886 baseEnd_5545886 := by
    simpa [prefixWord, tailWord_5545886, baseEnd_5545886] using wordTrace_append hprefix tailTrace_5545886
  have hstable : (prefixWord ++ tailWord_5545886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545886).length < 2 ^ (prefixWord ++ tailWord_5545886).sum := by decide
  have hdescent : baseEnd_5545886 < baseStart_5545886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545905 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5545905 : Nat := 118140960795 + 5545905 * 2 ^ 59
def prefixEnd_5545905 : Nat := 4983230072969 + 3 ^ 40 * 5545905 * 2
def baseEnd_5545905 : Nat := 2847714929173229354882353

theorem tailTrace_5545905 : CollatzResearch.WordTrace tailWord_5545905 prefixEnd_5545905 2847714929173229354882353 := by
  unfold tailWord_5545905
  simp only [CollatzResearch.WordTrace]
  refine ⟨202275772973140825011439169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134850515315427216674292779 202275772973140825011439169)
  ·
    refine ⟨151706829729855618758579377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202275772973140825011439169 151706829729855618758579377)
    ·
      refine ⟨113780122297391714068934533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151706829729855618758579377 113780122297391714068934533)
      ·
        refine ⟨21333772930760946387925225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113780122297391714068934533 21333772930760946387925225)
        ·
          refine ⟨16000329698070709790943919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21333772930760946387925225 16000329698070709790943919)
          ·
            refine ⟨24000494547106064686415879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16000329698070709790943919 24000494547106064686415879)
            ·
              refine ⟨36000741820659097029623819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24000494547106064686415879 36000741820659097029623819)
              ·
                refine ⟨54001112730988645544435729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36000741820659097029623819 54001112730988645544435729)
                ·
                  refine ⟨40500834548241484158326797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54001112730988645544435729 40500834548241484158326797)
                  ·
                    refine ⟨15187812955590556559372549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40500834548241484158326797 15187812955590556559372549)
                    ·
                      refine ⟨2847714929173229354882353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15187812955590556559372549 2847714929173229354882353)
                      ·
                        rfl

theorem cell23_5545905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5545905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545905 prefixEnd_5545905 := by exact prefixLift 5545905
  have htrace : WordTrace (prefixWord ++ tailWord_5545905) baseStart_5545905 baseEnd_5545905 := by
    simpa [prefixWord, tailWord_5545905, baseEnd_5545905] using wordTrace_append hprefix tailTrace_5545905
  have hstable : (prefixWord ++ tailWord_5545905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545905).length < 2 ^ (prefixWord ++ tailWord_5545905).sum := by decide
  have hdescent : baseEnd_5545905 < baseStart_5545905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545962 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_5545962 : Nat := 118140960795 + 5545962 * 2 ^ 59
def prefixEnd_5545962 : Nat := 4983230072969 + 3 ^ 40 * 5545962 * 2
def baseEnd_5545962 : Nat := 316416021952281736874399

theorem tailTrace_5545962 : CollatzResearch.WordTrace tailWord_5545962 prefixEnd_5545962 316416021952281736874399 := by
  unfold tailWord_5545962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50569462983483580936566035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134851901289289549164176093 50569462983483580936566035)
  ·
    refine ⟨75854194475225371404849053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50569462983483580936566035 75854194475225371404849053)
    ·
      refine ⟨28445322928209514276818395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75854194475225371404849053 28445322928209514276818395)
      ·
        refine ⟨42667984392314271415227593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28445322928209514276818395 42667984392314271415227593)
        ·
          refine ⟨32000988294235703561420695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42667984392314271415227593 32000988294235703561420695)
          ·
            refine ⟨48001482441353555342131043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32000988294235703561420695 48001482441353555342131043)
            ·
              refine ⟨72002223662030333013196565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48001482441353555342131043 72002223662030333013196565)
              ·
                refine ⟨3375104234157671859993589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72002223662030333013196565 3375104234157671859993589)
                ·
                  refine ⟨316416021952281736874399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375104234157671859993589 316416021952281736874399)
                  ·
                    rfl

theorem cell23_5545962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_5545962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545962 prefixEnd_5545962 := by exact prefixLift 5545962
  have htrace : WordTrace (prefixWord ++ tailWord_5545962) baseStart_5545962 baseEnd_5545962 := by
    simpa [prefixWord, tailWord_5545962, baseEnd_5545962] using wordTrace_append hprefix tailTrace_5545962
  have hstable : (prefixWord ++ tailWord_5545962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545962).length < 2 ^ (prefixWord ++ tailWord_5545962).sum := by decide
  have hdescent : baseEnd_5545962 < baseStart_5545962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545995 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4]
def baseStart_5545995 : Nat := 118140960795 + 5545995 * 2 ^ 59
def prefixEnd_5545995 : Nat := 4983230072969 + 3 ^ 40 * 5545995 * 2
def baseEnd_5545995 : Nat := 2847761142432134002756939

theorem tailTrace_5545995 : CollatzResearch.WordTrace tailWord_5545995 prefixEnd_5545995 2847761142432134002756939 := by
  unfold tailWord_5545995
  simp only [CollatzResearch.WordTrace]
  refine ⟨202279055542814770382215439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134852703695209846921476959 202279055542814770382215439)
  ·
    refine ⟨303418583314222155573323159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202279055542814770382215439 303418583314222155573323159)
    ·
      refine ⟨455127874971333233359984739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303418583314222155573323159 455127874971333233359984739)
      ·
        refine ⟨682691812456999850039977109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455127874971333233359984739 682691812456999850039977109)
        ·
          refine ⟨32001178708921867970623927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 682691812456999850039977109 32001178708921867970623927)
          ·
            refine ⟨48001768063382801955935891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32001178708921867970623927 48001768063382801955935891)
            ·
              refine ⟨72002652095074202933903837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48001768063382801955935891 72002652095074202933903837)
              ·
                refine ⟨27000994535652826100213939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72002652095074202933903837 27000994535652826100213939)
                ·
                  refine ⟨40501491803479239150320909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27000994535652826100213939 40501491803479239150320909)
                  ·
                    refine ⟨15188059426304714681370341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40501491803479239150320909 15188059426304714681370341)
                    ·
                      refine ⟨2847761142432134002756939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15188059426304714681370341 2847761142432134002756939)
                      ·
                        rfl

theorem cell23_5545995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_5545995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545995 prefixEnd_5545995 := by exact prefixLift 5545995
  have htrace : WordTrace (prefixWord ++ tailWord_5545995) baseStart_5545995 baseEnd_5545995 := by
    simpa [prefixWord, tailWord_5545995, baseEnd_5545995] using wordTrace_append hprefix tailTrace_5545995
  have hstable : (prefixWord ++ tailWord_5545995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545995).length < 2 ^ (prefixWord ++ tailWord_5545995).sum := by decide
  have hdescent : baseEnd_5545995 < baseStart_5545995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546012 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_5546012 : Nat := 118140960795 + 5546012 * 2 ^ 59
def prefixEnd_5546012 : Nat := 4983230072969 + 3 ^ 40 * 5546012 * 2
def baseEnd_5546012 : Nat := 2847769871603260436244361

theorem tailTrace_5546012 : CollatzResearch.WordTrace tailWord_5546012 prefixEnd_5546012 2847769871603260436244361 := by
  unfold tailWord_5546012
  simp only [CollatzResearch.WordTrace]
  refine ⟨101139837791876591142792145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134853117055835454857056193 101139837791876591142792145)
  ·
    refine ⟨75854878343907443357094109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101139837791876591142792145 75854878343907443357094109)
    ·
      refine ⟨28445579378965291258910291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75854878343907443357094109 28445579378965291258910291)
      ·
        refine ⟨42668369068447936888365437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28445579378965291258910291 42668369068447936888365437)
        ·
          refine ⟨16000638400667976333137039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42668369068447936888365437 16000638400667976333137039)
          ·
            refine ⟨24000957601001964499705559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16000638400667976333137039 24000957601001964499705559)
            ·
              refine ⟨36001436401502946749558339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24000957601001964499705559 36001436401502946749558339)
              ·
                refine ⟨54002154602254420124337509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36001436401502946749558339 54002154602254420124337509)
                ·
                  refine ⟨10125403987922703773313283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54002154602254420124337509 10125403987922703773313283)
                  ·
                    refine ⟨15188105981884055659969925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10125403987922703773313283 15188105981884055659969925)
                    ·
                      refine ⟨2847769871603260436244361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15188105981884055659969925 2847769871603260436244361)
                      ·
                        rfl

theorem cell23_5546012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_5546012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546012 prefixEnd_5546012 := by exact prefixLift 5546012
  have htrace : WordTrace (prefixWord ++ tailWord_5546012) baseStart_5546012 baseEnd_5546012 := by
    simpa [prefixWord, tailWord_5546012, baseEnd_5546012] using wordTrace_append hprefix tailTrace_5546012
  have hstable : (prefixWord ++ tailWord_5546012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546012).length < 2 ^ (prefixWord ++ tailWord_5546012).sum := by decide
  have hdescent : baseEnd_5546012 < baseStart_5546012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546046 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_5546046 : Nat := 118140960795 + 5546046 * 2 ^ 59
def prefixEnd_5546046 : Nat := 4983230072969 + 3 ^ 40 * 5546046 * 2
def baseEnd_5546046 : Nat := 2847787329945513303219205

theorem tailTrace_5546046 : CollatzResearch.WordTrace tailWord_5546046 prefixEnd_5546046 2847787329945513303219205 := by
  unfold tailWord_5546046
  simp only [CollatzResearch.WordTrace]
  refine ⟨25285114458203750761540249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134853943777086670728214661 25285114458203750761540249)
  ·
    refine ⟨18963835843652813071155187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25285114458203750761540249 18963835843652813071155187)
    ·
      refine ⟨28445753765479219606732781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18963835843652813071155187 28445753765479219606732781)
      ·
        refine ⟨10667157662054707352524793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28445753765479219606732781 10667157662054707352524793)
        ·
          refine ⟨8000368246541030514393595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10667157662054707352524793 8000368246541030514393595)
          ·
            refine ⟨12000552369811545771590393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8000368246541030514393595 12000552369811545771590393)
            ·
              refine ⟨9000414277358659328692795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12000552369811545771590393 9000414277358659328692795)
              ·
                refine ⟨13500621416037988993039193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9000414277358659328692795 13500621416037988993039193)
                ·
                  refine ⟨10125466062028491744779395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13500621416037988993039193 10125466062028491744779395)
                  ·
                    refine ⟨15188199093042737617169093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10125466062028491744779395 15188199093042737617169093)
                    ·
                      refine ⟨2847787329945513303219205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15188199093042737617169093 2847787329945513303219205)
                      ·
                        rfl

theorem cell23_5546046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_5546046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546046 prefixEnd_5546046 := by exact prefixLift 5546046
  have htrace : WordTrace (prefixWord ++ tailWord_5546046) baseStart_5546046 baseEnd_5546046 := by
    simpa [prefixWord, tailWord_5546046, baseEnd_5546046] using wordTrace_append hprefix tailTrace_5546046
  have hstable : (prefixWord ++ tailWord_5546046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546046).length < 2 ^ (prefixWord ++ tailWord_5546046).sum := by decide
  have hdescent : baseEnd_5546046 < baseStart_5546046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546049 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_5546049 : Nat := 118140960795 + 5546049 * 2 ^ 59
def prefixEnd_5546049 : Nat := 4983230072969 + 3 ^ 40 * 5546049 * 2
def baseEnd_5546049 : Nat := 2847788870387476791481691

theorem tailTrace_5546049 : CollatzResearch.WordTrace tailWord_5546049 prefixEnd_5546049 2847788870387476791481691 := by
  unfold tailWord_5546049
  simp only [CollatzResearch.WordTrace]
  refine ⟨202281025084619137604681201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134854016723079425069787467 202281025084619137604681201)
  ·
    refine ⟨151710768813464353203510901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202281025084619137604681201 151710768813464353203510901)
    ·
      refine ⟨14222884576262283112829147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151710768813464353203510901 14222884576262283112829147)
      ·
        refine ⟨21334326864393424669243721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14222884576262283112829147 21334326864393424669243721)
        ·
          refine ⟨16000745148295068501932791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21334326864393424669243721 16000745148295068501932791)
          ·
            refine ⟨24001117722442602752899187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16000745148295068501932791 24001117722442602752899187)
            ·
              refine ⟨36001676583663904129348781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24001117722442602752899187 36001676583663904129348781)
              ·
                refine ⟨13500628718873964048505793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36001676583663904129348781 13500628718873964048505793)
                ·
                  refine ⟨10125471539155473036379345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13500628718873964048505793 10125471539155473036379345)
                  ·
                    refine ⟨7594103654366604777284509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10125471539155473036379345 7594103654366604777284509)
                    ·
                      refine ⟨2847788870387476791481691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594103654366604777284509 2847788870387476791481691)
                      ·
                        rfl

theorem cell23_5546049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_5546049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546049 prefixEnd_5546049 := by exact prefixLift 5546049
  have htrace : WordTrace (prefixWord ++ tailWord_5546049) baseStart_5546049 baseEnd_5546049 := by
    simpa [prefixWord, tailWord_5546049, baseEnd_5546049] using wordTrace_append hprefix tailTrace_5546049
  have hstable : (prefixWord ++ tailWord_5546049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546049).length < 2 ^ (prefixWord ++ tailWord_5546049).sum := by decide
  have hdescent : baseEnd_5546049 < baseStart_5546049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546112 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 4, 4]
def baseStart_5546112 : Nat := 118140960795 + 5546112 * 2 ^ 59
def prefixEnd_5546112 : Nat := 4983230072969 + 3 ^ 40 * 5546112 * 2
def baseEnd_5546112 : Nat := 949273739889570014997967

theorem tailTrace_5546112 : CollatzResearch.WordTrace tailWord_5546112 prefixEnd_5546112 949273739889570014997967 := by
  unfold tailWord_5546112
  simp only [CollatzResearch.WordTrace]
  refine ⟨101141661441695449682112295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134855548588927266242816393 101141661441695449682112295)
  ·
    refine ⟨151712492162543174523168443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101141661441695449682112295 151712492162543174523168443)
    ·
      refine ⟨227568738243814761784752665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151712492162543174523168443 227568738243814761784752665)
      ·
        refine ⟨170676553682861071338564499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227568738243814761784752665 170676553682861071338564499)
        ·
          refine ⟨256014830524291607007846749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170676553682861071338564499 256014830524291607007846749)
          ·
            refine ⟨96005561446609352627942531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256014830524291607007846749 96005561446609352627942531)
            ·
              refine ⟨144008342169914028941913797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96005561446609352627942531 144008342169914028941913797)
              ·
                refine ⟨27001564156858880426608837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144008342169914028941913797 27001564156858880426608837)
                ·
                  refine ⟨5062793279411040079989157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27001564156858880426608837 5062793279411040079989157)
                  ·
                    refine ⟨949273739889570014997967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5062793279411040079989157 949273739889570014997967)
                    ·
                      rfl

theorem cell23_5546112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_5546112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546112 prefixEnd_5546112 := by exact prefixLift 5546112
  have htrace : WordTrace (prefixWord ++ tailWord_5546112) baseStart_5546112 baseEnd_5546112 := by
    simpa [prefixWord, tailWord_5546112, baseEnd_5546112] using wordTrace_append hprefix tailTrace_5546112
  have hstable : (prefixWord ++ tailWord_5546112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546112).length < 2 ^ (prefixWord ++ tailWord_5546112).sum := by decide
  have hdescent : baseEnd_5546112 < baseStart_5546112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546146 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_5546146 : Nat := 118140960795 + 5546146 * 2 ^ 59
def prefixEnd_5546146 : Nat := 4983230072969 + 3 ^ 40 * 5546146 * 2
def baseEnd_5546146 : Nat := 949279559336987637322915

theorem tailTrace_5546146 : CollatzResearch.WordTrace tailWord_5546146 prefixEnd_5546146 949279559336987637322915 := by
  unfold tailWord_5546146
  simp only [CollatzResearch.WordTrace]
  refine ⟨50571140741316930792740573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134856375310178482113974861 50571140741316930792740573)
  ·
    refine ⟨18964177777993849047277715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50571140741316930792740573 18964177777993849047277715)
    ·
      refine ⟨28446266666990773570916573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18964177777993849047277715 28446266666990773570916573)
      ·
        refine ⟨10667350000121540089093715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28446266666990773570916573 10667350000121540089093715)
        ·
          refine ⟨16001025000182310133640573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10667350000121540089093715 16001025000182310133640573)
          ·
            refine ⟨6000384375068366300115215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16001025000182310133640573 6000384375068366300115215)
            ·
              refine ⟨9000576562602549450172823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000384375068366300115215 9000576562602549450172823)
              ·
                refine ⟨13500864843903824175259235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9000576562602549450172823 13500864843903824175259235)
                ·
                  refine ⟨20251297265855736262888853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13500864843903824175259235 20251297265855736262888853)
                  ·
                    refine ⟨949279559336987637322915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20251297265855736262888853 949279559336987637322915)
                    ·
                      rfl

theorem cell23_5546146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_5546146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546146 prefixEnd_5546146 := by exact prefixLift 5546146
  have htrace : WordTrace (prefixWord ++ tailWord_5546146) baseStart_5546146 baseEnd_5546146 := by
    simpa [prefixWord, tailWord_5546146, baseEnd_5546146] using wordTrace_append hprefix tailTrace_5546146
  have hstable : (prefixWord ++ tailWord_5546146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546146).length < 2 ^ (prefixWord ++ tailWord_5546146).sum := by decide
  have hdescent : baseEnd_5546146 < baseStart_5546146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546155 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 9]
def baseStart_5546155 : Nat := 118140960795 + 5546155 * 2 ^ 59
def prefixEnd_5546155 : Nat := 4983230072969 + 3 ^ 40 * 5546155 * 2
def baseEnd_5546155 : Nat := 949281099778951125585401

theorem tailTrace_5546155 : CollatzResearch.WordTrace tailWord_5546155 prefixEnd_5546155 949281099778951125585401 := by
  unfold tailWord_5546155
  simp only [CollatzResearch.WordTrace]
  refine ⟨202284891222235117708039919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134856594148156745138693279 202284891222235117708039919)
  ·
    refine ⟨303427336833352676562059879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202284891222235117708039919 303427336833352676562059879)
    ·
      refine ⟨455141005250029014843089819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303427336833352676562059879 455141005250029014843089819)
      ·
        refine ⟨682711507875043522264634729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455141005250029014843089819 682711507875043522264634729)
        ·
          refine ⟨512033630906282641698476047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682711507875043522264634729 512033630906282641698476047)
          ·
            refine ⟨768050446359423962547714071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512033630906282641698476047 768050446359423962547714071)
            ·
              refine ⟨1152075669539135943821571107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768050446359423962547714071 1152075669539135943821571107)
              ·
                refine ⟨1728113504308703915732356661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152075669539135943821571107 1728113504308703915732356661)
                ·
                  refine ⟨162010641028940992099908437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728113504308703915732356661 162010641028940992099908437)
                  ·
                    refine ⟨949281099778951125585401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162010641028940992099908437 949281099778951125585401)
                    ·
                      rfl

theorem cell23_5546155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_5546155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546155 prefixEnd_5546155 := by exact prefixLift 5546155
  have htrace : WordTrace (prefixWord ++ tailWord_5546155) baseStart_5546155 baseEnd_5546155 := by
    simpa [prefixWord, tailWord_5546155, baseEnd_5546155] using wordTrace_append hprefix tailTrace_5546155
  have hstable : (prefixWord ++ tailWord_5546155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546155).length < 2 ^ (prefixWord ++ tailWord_5546155).sum := by decide
  have hdescent : baseEnd_5546155 < baseStart_5546155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546169 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5546169 : Nat := 118140960795 + 5546169 * 2 ^ 59
def prefixEnd_5546169 : Nat := 4983230072969 + 3 ^ 40 * 5546169 * 2
def baseEnd_5546169 : Nat := 2847850488066016321981139

theorem tailTrace_5546169 : CollatzResearch.WordTrace tailWord_5546169 prefixEnd_5546169 2847850488066016321981139 := by
  unfold tailWord_5546169
  simp only [CollatzResearch.WordTrace]
  refine ⟨202285401844184398099049561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134856934562789598732699707 202285401844184398099049561)
  ·
    refine ⟨151714051383138298574287171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202285401844184398099049561 151714051383138298574287171)
    ·
      refine ⟨227571077074707447861430757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151714051383138298574287171 227571077074707447861430757)
      ·
        refine ⟨42669576951507646474018267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227571077074707447861430757 42669576951507646474018267)
        ·
          refine ⟨64004365427261469711027401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42669576951507646474018267 64004365427261469711027401)
          ·
            refine ⟨48003274070446102283270551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64004365427261469711027401 48003274070446102283270551)
            ·
              refine ⟨72004911105669153424905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48003274070446102283270551 72004911105669153424905827)
              ·
                refine ⟨108007366658503730137358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72004911105669153424905827 108007366658503730137358741)
                ·
                  refine ⟨5062845312117362350188691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108007366658503730137358741 5062845312117362350188691)
                  ·
                    refine ⟨7594267968176043525283037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062845312117362350188691 7594267968176043525283037)
                    ·
                      refine ⟨2847850488066016321981139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594267968176043525283037 2847850488066016321981139)
                      ·
                        rfl

theorem cell23_5546169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5546169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546169 prefixEnd_5546169 := by exact prefixLift 5546169
  have htrace : WordTrace (prefixWord ++ tailWord_5546169) baseStart_5546169 baseEnd_5546169 := by
    simpa [prefixWord, tailWord_5546169, baseEnd_5546169] using wordTrace_append hprefix tailTrace_5546169
  have hstable : (prefixWord ++ tailWord_5546169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546169).length < 2 ^ (prefixWord ++ tailWord_5546169).sum := by decide
  have hdescent : baseEnd_5546169 < baseStart_5546169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546186 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_5546186 : Nat := 118140960795 + 5546186 * 2 ^ 59
def prefixEnd_5546186 : Nat := 4983230072969 + 3 ^ 40 * 5546186 * 2
def baseEnd_5546186 : Nat := 2847859217237142755468561

theorem tailTrace_5546186 : CollatzResearch.WordTrace tailWord_5546186 prefixEnd_5546186 2847859217237142755468561 := by
  unfold tailWord_5546186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50571505471280702500604603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134857347923415206668278941 50571505471280702500604603)
  ·
    refine ⟨75857258206921053750906905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50571505471280702500604603 75857258206921053750906905)
    ·
      refine ⟨56892943655190790313180179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75857258206921053750906905 56892943655190790313180179)
      ·
        refine ⟨85339415482786185469770269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56892943655190790313180179 85339415482786185469770269)
        ·
          refine ⟨32002280806044819551163851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85339415482786185469770269 32002280806044819551163851)
          ·
            refine ⟨48003421209067229326745777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32002280806044819551163851 48003421209067229326745777)
            ·
              refine ⟨36002565906800421995059333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48003421209067229326745777 36002565906800421995059333)
              ·
                refine ⟨6750481107525079124073625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36002565906800421995059333 6750481107525079124073625)
                ·
                  refine ⟨5062860830643809343055219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750481107525079124073625 5062860830643809343055219)
                  ·
                    refine ⟨7594291245965714014582829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062860830643809343055219 7594291245965714014582829)
                    ·
                      refine ⟨2847859217237142755468561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594291245965714014582829 2847859217237142755468561)
                      ·
                        rfl

theorem cell23_5546186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_5546186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546186 prefixEnd_5546186 := by exact prefixLift 5546186
  have htrace : WordTrace (prefixWord ++ tailWord_5546186) baseStart_5546186 baseEnd_5546186 := by
    simpa [prefixWord, tailWord_5546186, baseEnd_5546186] using wordTrace_append hprefix tailTrace_5546186
  have hstable : (prefixWord ++ tailWord_5546186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546186).length < 2 ^ (prefixWord ++ tailWord_5546186).sum := by decide
  have hdescent : baseEnd_5546186 < baseStart_5546186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546202 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_5546202 : Nat := 118140960795 + 5546202 * 2 ^ 59
def prefixEnd_5546202 : Nat := 4983230072969 + 3 ^ 40 * 5546202 * 2
def baseEnd_5546202 : Nat := 949289144309204897622829

theorem tailTrace_5546202 : CollatzResearch.WordTrace tailWord_5546202 prefixEnd_5546202 949289144309204897622829 := by
  unfold tailWord_5546202
  simp only [CollatzResearch.WordTrace]
  refine ⟨50571651363266211183750215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134857736968709896490000573 50571651363266211183750215)
  ·
    refine ⟨75857477044899316775625323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50571651363266211183750215 75857477044899316775625323)
    ·
      refine ⟨113786215567348975163437985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75857477044899316775625323 113786215567348975163437985)
      ·
        refine ⟨85339661675511731372578489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113786215567348975163437985 85339661675511731372578489)
        ·
          refine ⟨64004746256633798529433867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85339661675511731372578489 64004746256633798529433867)
          ·
            refine ⟨96007119384950697794150801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64004746256633798529433867 96007119384950697794150801)
            ·
              refine ⟨72005339538713023345613101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96007119384950697794150801 72005339538713023345613101)
              ·
                refine ⟨27002002327017383754604913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72005339538713023345613101 27002002327017383754604913)
                ·
                  refine ⟨20251501745263037815953685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27002002327017383754604913 20251501745263037815953685)
                  ·
                    refine ⟨949289144309204897622829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20251501745263037815953685 949289144309204897622829)
                    ·
                      rfl

theorem cell23_5546202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_5546202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546202 prefixEnd_5546202 := by exact prefixLift 5546202
  have htrace : WordTrace (prefixWord ++ tailWord_5546202) baseStart_5546202 baseEnd_5546202 := by
    simpa [prefixWord, tailWord_5546202, baseEnd_5546202] using wordTrace_append hprefix tailTrace_5546202
  have hstable : (prefixWord ++ tailWord_5546202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546202).length < 2 ^ (prefixWord ++ tailWord_5546202).sum := by decide
  have hdescent : baseEnd_5546202 < baseStart_5546202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546213 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5546213 : Nat := 118140960795 + 5546213 * 2 ^ 59
def prefixEnd_5546213 : Nat := 4983230072969 + 3 ^ 40 * 5546213 * 2
def baseEnd_5546213 : Nat := 2847873081214814149830937

theorem tailTrace_5546213 : CollatzResearch.WordTrace tailWord_5546213 prefixEnd_5546213 2847873081214814149830937 := by
  unfold tailWord_5546213
  simp only [CollatzResearch.WordTrace]
  refine ⟨202287006656024993613651293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134858004437349995742434195 202287006656024993613651293)
  ·
    refine ⟨75857627496009372605119235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202287006656024993613651293 75857627496009372605119235)
    ·
      refine ⟨113786441244014058907678853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75857627496009372605119235 113786441244014058907678853)
      ·
        refine ⟨21334957733252636045189785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113786441244014058907678853 21334957733252636045189785)
        ·
          refine ⟨16001218299939477033892339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21334957733252636045189785 16001218299939477033892339)
          ·
            refine ⟨24001827449909215550838509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16001218299939477033892339 24001827449909215550838509)
            ·
              refine ⟨9000685293715955831564441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24001827449909215550838509 9000685293715955831564441)
              ·
                refine ⟨6750513970286966873673331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9000685293715955831564441 6750513970286966873673331)
                ·
                  refine ⟨10125770955430450310509997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750513970286966873673331 10125770955430450310509997)
                  ·
                    refine ⟨3797164108286418866441249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10125770955430450310509997 3797164108286418866441249)
                    ·
                      refine ⟨2847873081214814149830937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797164108286418866441249 2847873081214814149830937)
                      ·
                        rfl

theorem cell23_5546213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5546213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546213 prefixEnd_5546213 := by exact prefixLift 5546213
  have htrace : WordTrace (prefixWord ++ tailWord_5546213) baseStart_5546213 baseEnd_5546213 := by
    simpa [prefixWord, tailWord_5546213, baseEnd_5546213] using wordTrace_append hprefix tailTrace_5546213
  have hstable : (prefixWord ++ tailWord_5546213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546213).length < 2 ^ (prefixWord ++ tailWord_5546213).sum := by decide
  have hdescent : baseEnd_5546213 < baseStart_5546213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546226 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_5546226 : Nat := 118140960795 + 5546226 * 2 ^ 59
def prefixEnd_5546226 : Nat := 4983230072969 + 3 ^ 40 * 5546226 * 2
def baseEnd_5546226 : Nat := 2847879756463322598968377

theorem tailTrace_5546226 : CollatzResearch.WordTrace tailWord_5546226 prefixEnd_5546226 2847879756463322598968377 := by
  unfold tailWord_5546226
  simp only [CollatzResearch.WordTrace]
  refine ⟨50571870201244474208468633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134858320536651931222583021 50571870201244474208468633)
  ·
    refine ⟨37928902650933355656351475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50571870201244474208468633 37928902650933355656351475)
    ·
      refine ⟨56893353976400033484527213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37928902650933355656351475 56893353976400033484527213)
      ·
        refine ⟨21335007741150012556697705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56893353976400033484527213 21335007741150012556697705)
        ·
          refine ⟨16001255805862509417523279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21335007741150012556697705 16001255805862509417523279)
          ·
            refine ⟨24001883708793764126284919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16001255805862509417523279 24001883708793764126284919)
            ·
              refine ⟨36002825563190646189427379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24001883708793764126284919 36002825563190646189427379)
              ·
                refine ⟨54004238344785969284141069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36002825563190646189427379 54004238344785969284141069)
                ·
                  refine ⟨20251589379294738481552901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54004238344785969284141069 20251589379294738481552901)
                  ·
                    refine ⟨3797173008617763465291169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20251589379294738481552901 3797173008617763465291169)
                    ·
                      refine ⟨2847879756463322598968377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797173008617763465291169 2847879756463322598968377)
                      ·
                        rfl

theorem cell23_5546226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_5546226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546226 prefixEnd_5546226 := by exact prefixLift 5546226
  have htrace : WordTrace (prefixWord ++ tailWord_5546226) baseStart_5546226 baseEnd_5546226 := by
    simpa [prefixWord, tailWord_5546226, baseEnd_5546226] using wordTrace_append hprefix tailTrace_5546226
  have hstable : (prefixWord ++ tailWord_5546226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546226).length < 2 ^ (prefixWord ++ tailWord_5546226).sum := by decide
  have hdescent : baseEnd_5546226 < baseStart_5546226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546243 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 2, 2, 2]
def baseStart_5546243 : Nat := 118140960795 + 5546243 * 2 ^ 59
def prefixEnd_5546243 : Nat := 4983230072969 + 3 ^ 40 * 5546243 * 2
def baseEnd_5546243 : Nat := 2847888485634449032455799

theorem tailTrace_5546243 : CollatzResearch.WordTrace tailWord_5546243 prefixEnd_5546243 2847888485634449032455799 := by
  unfold tailWord_5546243
  simp only [CollatzResearch.WordTrace]
  refine ⟨202288100845916308737243383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134858733897277539158162255 202288100845916308737243383)
  ·
    refine ⟨303432151268874463105865075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202288100845916308737243383 303432151268874463105865075)
    ·
      refine ⟨455148226903311694658797613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303432151268874463105865075 455148226903311694658797613)
      ·
        refine ⟨170680585088741885497049105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455148226903311694658797613 170680585088741885497049105)
        ·
          refine ⟨128010438816556414122786829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170680585088741885497049105 128010438816556414122786829)
          ·
            refine ⟨48003914556208655296045061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128010438816556414122786829 48003914556208655296045061)
            ·
              refine ⟨9000733979289122868008449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48003914556208655296045061 9000733979289122868008449)
              ·
                refine ⟨6750550484466842151006337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9000733979289122868008449 6750550484466842151006337)
                ·
                  refine ⟨5062912863350131613254753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750550484466842151006337 5062912863350131613254753)
                  ·
                    refine ⟨3797184647512598709941065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5062912863350131613254753 3797184647512598709941065)
                    ·
                      refine ⟨2847888485634449032455799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797184647512598709941065 2847888485634449032455799)
                      ·
                        rfl

theorem cell23_5546243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_5546243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546243 prefixEnd_5546243 := by exact prefixLift 5546243
  have htrace : WordTrace (prefixWord ++ tailWord_5546243) baseStart_5546243 baseEnd_5546243 := by
    simpa [prefixWord, tailWord_5546243, baseEnd_5546243] using wordTrace_append hprefix tailTrace_5546243
  have hstable : (prefixWord ++ tailWord_5546243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546243).length < 2 ^ (prefixWord ++ tailWord_5546243).sum := by decide
  have hdescent : baseEnd_5546243 < baseStart_5546243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546299 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 10, 2]
def baseStart_5546299 : Nat := 118140960795 + 5546299 * 2 ^ 59
def prefixEnd_5546299 : Nat := 4983230072969 + 3 ^ 40 * 5546299 * 2
def baseEnd_5546299 : Nat := 2847917240551100813355541

theorem tailTrace_5546299 : CollatzResearch.WordTrace tailWord_5546299 prefixEnd_5546299 2847917240551100813355541 := by
  unfold tailWord_5546299
  simp only [CollatzResearch.WordTrace]
  refine ⟨202290143333713430301281951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134860095555808953534187967 202290143333713430301281951)
  ·
    refine ⟨303435215000570145451922927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202290143333713430301281951 303435215000570145451922927)
    ·
      refine ⟨455152822500855218177884391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303435215000570145451922927 455152822500855218177884391)
      ·
        refine ⟨682729233751282827266826587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455152822500855218177884391 682729233751282827266826587)
        ·
          refine ⟨1024093850626924240900239881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682729233751282827266826587 1024093850626924240900239881)
          ·
            refine ⟨768070387970193180675179911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024093850626924240900239881 768070387970193180675179911)
            ·
              refine ⟨1152105581955289771012769867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768070387970193180675179911 1152105581955289771012769867)
              ·
                refine ⟨1728158372932934656519154801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152105581955289771012769867 1728158372932934656519154801)
                ·
                  refine ⟨1296118779699700992389366101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1728158372932934656519154801 1296118779699700992389366101)
                  ·
                    refine ⟨3797222987401467751140721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1296118779699700992389366101 3797222987401467751140721)
                    ·
                      refine ⟨2847917240551100813355541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797222987401467751140721 2847917240551100813355541)
                      ·
                        rfl

theorem cell23_5546299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10, 2].length) (baseStart_5546299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546299 prefixEnd_5546299 := by exact prefixLift 5546299
  have htrace : WordTrace (prefixWord ++ tailWord_5546299) baseStart_5546299 baseEnd_5546299 := by
    simpa [prefixWord, tailWord_5546299, baseEnd_5546299] using wordTrace_append hprefix tailTrace_5546299
  have hstable : (prefixWord ++ tailWord_5546299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546299).length < 2 ^ (prefixWord ++ tailWord_5546299).sum := by decide
  have hdescent : baseEnd_5546299 < baseStart_5546299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546316 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 2, 4, 2]
def baseStart_5546316 : Nat := 118140960795 + 5546316 * 2 ^ 59
def prefixEnd_5546316 : Nat := 4983230072969 + 3 ^ 40 * 5546316 * 2
def baseEnd_5546316 : Nat := 2847925969722227246842963

theorem tailTrace_5546316 : CollatzResearch.WordTrace tailWord_5546316 prefixEnd_5546316 2847925969722227246842963 := by
  unfold tailWord_5546316
  simp only [CollatzResearch.WordTrace]
  refine ⟨101145381687325921102325401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134860508916434561469767201 101145381687325921102325401)
  ·
    refine ⟨75859036265494440826744051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101145381687325921102325401 75859036265494440826744051)
    ·
      refine ⟨113788554398241661240116077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75859036265494440826744051 113788554398241661240116077)
      ·
        refine ⟨42670707899340622965043529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113788554398241661240116077 42670707899340622965043529)
        ·
          refine ⟨32003030924505467223782647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42670707899340622965043529 32003030924505467223782647)
          ·
            refine ⟨48004546386758200835673971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32003030924505467223782647 48004546386758200835673971)
            ·
              refine ⟨72006819580137301253510957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48004546386758200835673971 72006819580137301253510957)
              ·
                refine ⟨27002557342551487970066609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72006819580137301253510957 27002557342551487970066609)
                ·
                  refine ⟨20251918006913615977549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27002557342551487970066609 20251918006913615977549957)
                  ·
                    refine ⟨3797234626296302995790617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20251918006913615977549957 3797234626296302995790617)
                    ·
                      refine ⟨2847925969722227246842963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797234626296302995790617 2847925969722227246842963)
                      ·
                        rfl

theorem cell23_5546316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_5546316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546316 prefixEnd_5546316 := by exact prefixLift 5546316
  have htrace : WordTrace (prefixWord ++ tailWord_5546316) baseStart_5546316 baseEnd_5546316 := by
    simpa [prefixWord, tailWord_5546316, baseEnd_5546316] using wordTrace_append hprefix tailTrace_5546316
  have hstable : (prefixWord ++ tailWord_5546316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546316).length < 2 ^ (prefixWord ++ tailWord_5546316).sum := by decide
  have hdescent : baseEnd_5546316 < baseStart_5546316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546319 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_5546319 : Nat := 118140960795 + 5546319 * 2 ^ 59
def prefixEnd_5546319 : Nat := 4983230072969 + 3 ^ 40 * 5546319 * 2
def baseEnd_5546319 : Nat := 2847927510164190735105449

theorem tailTrace_5546319 : CollatzResearch.WordTrace tailWord_5546319 prefixEnd_5546319 2847927510164190735105449 := by
  unfold tailWord_5546319
  simp only [CollatzResearch.WordTrace]
  refine ⟨202290872793640973717010011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134860581862427315811340007 202290872793640973717010011)
  ·
    refine ⟨303436309190461460575515017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202290872793640973717010011 303436309190461460575515017)
    ·
      refine ⟨227577231892846095431636263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303436309190461460575515017 227577231892846095431636263)
      ·
        refine ⟨341365847839269143147454395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227577231892846095431636263 341365847839269143147454395)
        ·
          refine ⟨512048771758903714721181593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341365847839269143147454395 512048771758903714721181593)
          ·
            refine ⟨384036578819177786040886195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512048771758903714721181593 384036578819177786040886195)
            ·
              refine ⟨576054868228766679061329293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384036578819177786040886195 576054868228766679061329293)
              ·
                refine ⟨216020575585787504647998485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 576054868228766679061329293 216020575585787504647998485)
                ·
                  refine ⟨10125964480583789280374929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216020575585787504647998485 10125964480583789280374929)
                  ·
                    refine ⟨7594473360437841960281197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10125964480583789280374929 7594473360437841960281197)
                    ·
                      refine ⟨2847927510164190735105449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594473360437841960281197 2847927510164190735105449)
                      ·
                        rfl

theorem cell23_5546319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_5546319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546319 prefixEnd_5546319 := by exact prefixLift 5546319
  have htrace : WordTrace (prefixWord ++ tailWord_5546319) baseStart_5546319 baseEnd_5546319 := by
    simpa [prefixWord, tailWord_5546319, baseEnd_5546319] using wordTrace_append hprefix tailTrace_5546319
  have hstable : (prefixWord ++ tailWord_5546319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546319).length < 2 ^ (prefixWord ++ tailWord_5546319).sum := by decide
  have hdescent : baseEnd_5546319 < baseStart_5546319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546393 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 2, 3, 2]
def baseStart_5546393 : Nat := 118140960795 + 5546393 * 2 ^ 59
def prefixEnd_5546393 : Nat := 4983230072969 + 3 ^ 40 * 5546393 * 2
def baseEnd_5546393 : Nat := 2847965507732623445580109

theorem tailTrace_5546393 : CollatzResearch.WordTrace tailWord_5546393 prefixEnd_5546393 2847965507732623445580109 := by
  unfold tailWord_5546393
  simp only [CollatzResearch.WordTrace]
  refine ⟨202293571795372884355203833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134862381196915256236802555 202293571795372884355203833)
  ·
    refine ⟨151720178846529663266402875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202293571795372884355203833 151720178846529663266402875)
    ·
      refine ⟨227580268269794494899604313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151720178846529663266402875 227580268269794494899604313)
      ·
        refine ⟨170685201202345871174703235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227580268269794494899604313 170685201202345871174703235)
        ·
          refine ⟨256027801803518806762054853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170685201202345871174703235 256027801803518806762054853)
          ·
            refine ⟨48005212838159776267885285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256027801803518806762054853 48005212838159776267885285)
            ·
              refine ⟨9000977407154958050228491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48005212838159776267885285 9000977407154958050228491)
              ·
                refine ⟨13501466110732437075342737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9000977407154958050228491 13501466110732437075342737)
                ·
                  refine ⟨10126099583049327806507053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13501466110732437075342737 10126099583049327806507053)
                  ·
                    refine ⟨3797287343643497927440145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10126099583049327806507053 3797287343643497927440145)
                    ·
                      refine ⟨2847965507732623445580109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797287343643497927440145 2847965507732623445580109)
                      ·
                        rfl

theorem cell23_5546393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_5546393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546393 prefixEnd_5546393 := by exact prefixLift 5546393
  have htrace : WordTrace (prefixWord ++ tailWord_5546393) baseStart_5546393 baseEnd_5546393 := by
    simpa [prefixWord, tailWord_5546393, baseEnd_5546393] using wordTrace_append hprefix tailTrace_5546393
  have hstable : (prefixWord ++ tailWord_5546393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546393).length < 2 ^ (prefixWord ++ tailWord_5546393).sum := by decide
  have hdescent : baseEnd_5546393 < baseStart_5546393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546403 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 1, 5]
def baseStart_5546403 : Nat := 118140960795 + 5546403 * 2 ^ 59
def prefixEnd_5546403 : Nat := 4983230072969 + 3 ^ 40 * 5546403 * 2
def baseEnd_5546403 : Nat := 949323547513056135485021

theorem tailTrace_5546403 : CollatzResearch.WordTrace tailWord_5546403 prefixEnd_5546403 949323547513056135485021 := by
  unfold tailWord_5546403
  simp only [CollatzResearch.WordTrace]
  refine ⟨202293936525336656063067863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134862624350224437375378575 202293936525336656063067863)
  ·
    refine ⟨303440904788004984094601795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202293936525336656063067863 303440904788004984094601795)
    ·
      refine ⟨455161357182007476141902693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303440904788004984094601795 455161357182007476141902693)
      ·
        refine ⟨85342754471626401776606755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 455161357182007476141902693 85342754471626401776606755)
        ·
          refine ⟨128014131707439602664910133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85342754471626401776606755 128014131707439602664910133)
          ·
            refine ⟨12001324847572462749835325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128014131707439602664910133 12001324847572462749835325)
            ·
              refine ⟨4500496817839673531188247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12001324847572462749835325 4500496817839673531188247)
              ·
                refine ⟨6750745226759510296782371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500496817839673531188247 6750745226759510296782371)
                ·
                  refine ⟨10126117840139265445173557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750745226759510296782371 10126117840139265445173557)
                  ·
                    refine ⟨949323547513056135485021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10126117840139265445173557 949323547513056135485021)
                    ·
                      rfl

theorem cell23_5546403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 5].length) (baseStart_5546403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546403 prefixEnd_5546403 := by exact prefixLift 5546403
  have htrace : WordTrace (prefixWord ++ tailWord_5546403) baseStart_5546403 baseEnd_5546403 := by
    simpa [prefixWord, tailWord_5546403, baseEnd_5546403] using wordTrace_append hprefix tailTrace_5546403
  have hstable : (prefixWord ++ tailWord_5546403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546403).length < 2 ^ (prefixWord ++ tailWord_5546403).sum := by decide
  have hdescent : baseEnd_5546403 < baseStart_5546403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546417 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 1, 1, 3]
def baseStart_5546417 : Nat := 118140960795 + 5546417 * 2 ^ 59
def prefixEnd_5546417 : Nat := 4983230072969 + 3 ^ 40 * 5546417 * 2
def baseEnd_5546417 : Nat := 2847977831268331351679999

theorem tailTrace_5546417 : CollatzResearch.WordTrace tailWord_5546417 prefixEnd_5546417 2847977831268331351679999 := by
  unfold tailWord_5546417
  simp only [CollatzResearch.WordTrace]
  refine ⟨202294447147285936454077505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134862964764857290969385003 202294447147285936454077505)
  ·
    refine ⟨151720835360464452340558129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202294447147285936454077505 151720835360464452340558129)
    ·
      refine ⟨113790626520348339255418597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151720835360464452340558129 113790626520348339255418597)
      ·
        refine ⟨21335742472565313610390987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113790626520348339255418597 21335742472565313610390987)
        ·
          refine ⟨32003613708847970415586481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21335742472565313610390987 32003613708847970415586481)
          ·
            refine ⟨24002710281635977811689861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32003613708847970415586481 24002710281635977811689861)
            ·
              refine ⟨4500508177806745839691849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24002710281635977811689861 4500508177806745839691849)
              ·
                refine ⟨3375381133355059379768887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500508177806745839691849 3375381133355059379768887)
                ·
                  refine ⟨5063071700032589069653331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375381133355059379768887 5063071700032589069653331)
                  ·
                    refine ⟨7594607550048883604479997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5063071700032589069653331 7594607550048883604479997)
                    ·
                      refine ⟨2847977831268331351679999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594607550048883604479997 2847977831268331351679999)
                      ·
                        rfl

theorem cell23_5546417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_5546417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546417 prefixEnd_5546417 := by exact prefixLift 5546417
  have htrace : WordTrace (prefixWord ++ tailWord_5546417) baseStart_5546417 baseEnd_5546417 := by
    simpa [prefixWord, tailWord_5546417, baseEnd_5546417] using wordTrace_append hprefix tailTrace_5546417
  have hstable : (prefixWord ++ tailWord_5546417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546417).length < 2 ^ (prefixWord ++ tailWord_5546417).sum := by decide
  have hdescent : baseEnd_5546417 < baseStart_5546417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546440 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_5546440 : Nat := 118140960795 + 5546440 * 2 ^ 59
def prefixEnd_5546440 : Nat := 4983230072969 + 3 ^ 40 * 5546440 * 2
def baseEnd_5546440 : Nat := 2847989641323384761692393

theorem tailTrace_5546440 : CollatzResearch.WordTrace tailWord_5546440 prefixEnd_5546440 2847989641323384761692393 := by
  unfold tailWord_5546440
  simp only [CollatzResearch.WordTrace]
  refine ⟨101147643013101305691082387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134863524017468407588109849 101147643013101305691082387)
  ·
    refine ⟨151721464519651958536623581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101147643013101305691082387 151721464519651958536623581)
    ·
      refine ⟨56895549194869484451233843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151721464519651958536623581 56895549194869484451233843)
      ·
        refine ⟨85343323792304226676850765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56895549194869484451233843 85343323792304226676850765)
        ·
          refine ⟨32003746422114085003819037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85343323792304226676850765 32003746422114085003819037)
          ·
            refine ⟨12001404908292781876432139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32003746422114085003819037 12001404908292781876432139)
            ·
              refine ⟨18002107362439172814648209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12001404908292781876432139 18002107362439172814648209)
              ·
                refine ⟨13501580521829379610986157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18002107362439172814648209 13501580521829379610986157)
                ·
                  refine ⟨5063092695686017354119809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13501580521829379610986157 5063092695686017354119809)
                  ·
                    refine ⟨3797319521764513015589857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063092695686017354119809 3797319521764513015589857)
                    ·
                      refine ⟨2847989641323384761692393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797319521764513015589857 2847989641323384761692393)
                      ·
                        rfl

theorem cell23_5546440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_5546440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546440 prefixEnd_5546440 := by exact prefixLift 5546440
  have htrace : WordTrace (prefixWord ++ tailWord_5546440) baseStart_5546440 baseEnd_5546440 := by
    simpa [prefixWord, tailWord_5546440, baseEnd_5546440] using wordTrace_append hprefix tailTrace_5546440
  have hstable : (prefixWord ++ tailWord_5546440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546440).length < 2 ^ (prefixWord ++ tailWord_5546440).sum := by decide
  have hdescent : baseEnd_5546440 < baseStart_5546440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546457 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 1, 2, 2]
def baseStart_5546457 : Nat := 118140960795 + 5546457 * 2 ^ 59
def prefixEnd_5546457 : Nat := 4983230072969 + 3 ^ 40 * 5546457 * 2
def baseEnd_5546457 : Nat := 2847998370494511195179815

theorem tailTrace_5546457 : CollatzResearch.WordTrace tailWord_5546457 prefixEnd_5546457 2847998370494511195179815 := by
  unfold tailWord_5546457
  simp only [CollatzResearch.WordTrace]
  refine ⟨202295906067141023285533625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134863937378094015523689083 202295906067141023285533625)
  ·
    refine ⟨151721929550355767464150219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202295906067141023285533625 151721929550355767464150219)
    ·
      refine ⟨227582894325533651196225329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151721929550355767464150219 227582894325533651196225329)
      ·
        refine ⟨170687170744150238397168997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227582894325533651196225329 170687170744150238397168997)
        ·
          refine ⟨32003844514528169699469187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170687170744150238397168997 32003844514528169699469187)
          ·
            refine ⟨48005766771792254549203781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32003844514528169699469187 48005766771792254549203781)
            ·
              refine ⟨9001081269711047727975709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48005766771792254549203781 9001081269711047727975709)
              ·
                refine ⟨3375405476141642897990891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9001081269711047727975709 3375405476141642897990891)
                ·
                  refine ⟨5063108214212464346986337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375405476141642897990891 5063108214212464346986337)
                  ·
                    refine ⟨3797331160659348260239753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063108214212464346986337 3797331160659348260239753)
                    ·
                      refine ⟨2847998370494511195179815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797331160659348260239753 2847998370494511195179815)
                      ·
                        rfl

theorem cell23_5546457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_5546457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546457 prefixEnd_5546457 := by exact prefixLift 5546457
  have htrace : WordTrace (prefixWord ++ tailWord_5546457) baseStart_5546457 baseEnd_5546457 := by
    simpa [prefixWord, tailWord_5546457, baseEnd_5546457] using wordTrace_append hprefix tailTrace_5546457
  have hstable : (prefixWord ++ tailWord_5546457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546457).length < 2 ^ (prefixWord ++ tailWord_5546457).sum := by decide
  have hdescent : baseEnd_5546457 < baseStart_5546457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546467 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 2, 4]
def baseStart_5546467 : Nat := 118140960795 + 5546467 * 2 ^ 59
def prefixEnd_5546467 : Nat := 4983230072969 + 3 ^ 40 * 5546467 * 2
def baseEnd_5546467 : Nat := 949334501767018718684923

theorem tailTrace_5546467 : CollatzResearch.WordTrace tailWord_5546467 prefixEnd_5546467 949334501767018718684923 := by
  unfold tailWord_5546467
  simp only [CollatzResearch.WordTrace]
  refine ⟨202296270797104794993397655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134864180531403196662265103 202296270797104794993397655)
  ·
    refine ⟨303444406195657192490096483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202296270797104794993397655 303444406195657192490096483)
    ·
      refine ⟨455166609293485788735144725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303444406195657192490096483 455166609293485788735144725)
      ·
        refine ⟨21335934810632146346959909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 455166609293485788735144725 21335934810632146346959909)
        ·
          refine ⟨4000487776993527440054983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21335934810632146346959909 4000487776993527440054983)
          ·
            refine ⟨6000731665490291160082475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000487776993527440054983 6000731665490291160082475)
            ·
              refine ⟨9001097498235436740123713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000731665490291160082475 9001097498235436740123713)
              ·
                refine ⟨6750823123676577555092785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9001097498235436740123713 6750823123676577555092785)
                ·
                  refine ⟨5063117342757433166319589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750823123676577555092785 5063117342757433166319589)
                  ·
                    refine ⟨949334501767018718684923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5063117342757433166319589 949334501767018718684923)
                    ·
                      rfl

theorem cell23_5546467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 4].length) (baseStart_5546467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546467 prefixEnd_5546467 := by exact prefixLift 5546467
  have htrace : WordTrace (prefixWord ++ tailWord_5546467) baseStart_5546467 baseEnd_5546467 := by
    simpa [prefixWord, tailWord_5546467, baseEnd_5546467] using wordTrace_append hprefix tailTrace_5546467
  have hstable : (prefixWord ++ tailWord_5546467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546467).length < 2 ^ (prefixWord ++ tailWord_5546467).sum := by decide
  have hdescent : baseEnd_5546467 < baseStart_5546467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546473 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 3]
def baseStart_5546473 : Nat := 118140960795 + 5546473 * 2 ^ 59
def prefixEnd_5546473 : Nat := 4983230072969 + 3 ^ 40 * 5546473 * 2
def baseEnd_5546473 : Nat := 2848006586184983132579741

theorem tailTrace_5546473 : CollatzResearch.WordTrace tailWord_5546473 prefixEnd_5546473 2848006586184983132579741 := by
  unfold tailWord_5546473
  simp only [CollatzResearch.WordTrace]
  refine ⟨202296489635083058018116073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134864326423388705345410715 202296489635083058018116073)
  ·
    refine ⟨151722367226312293513587055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202296489635083058018116073 151722367226312293513587055)
    ·
      refine ⟨227583550839468440270380583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151722367226312293513587055 227583550839468440270380583)
      ·
        refine ⟨341375326259202660405570875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227583550839468440270380583 341375326259202660405570875)
        ·
          refine ⟨512062989388803990608356313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341375326259202660405570875 512062989388803990608356313)
          ·
            refine ⟨384047242041602992956267235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512062989388803990608356313 384047242041602992956267235)
            ·
              refine ⟨576070863062404489434400853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384047242041602992956267235 576070863062404489434400853)
              ·
                refine ⟨6750830426512552610559385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 576070863062404489434400853 6750830426512552610559385)
                ·
                  refine ⟨5063122819884414457919539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750830426512552610559385 5063122819884414457919539)
                  ·
                    refine ⟨7594684229826621686879309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5063122819884414457919539 7594684229826621686879309)
                    ·
                      refine ⟨2848006586184983132579741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594684229826621686879309 2848006586184983132579741)
                      ·
                        rfl

theorem cell23_5546473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_5546473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546473 prefixEnd_5546473 := by exact prefixLift 5546473
  have htrace : WordTrace (prefixWord ++ tailWord_5546473) baseStart_5546473 baseEnd_5546473 := by
    simpa [prefixWord, tailWord_5546473, baseEnd_5546473] using wordTrace_append hprefix tailTrace_5546473
  have hstable : (prefixWord ++ tailWord_5546473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546473).length < 2 ^ (prefixWord ++ tailWord_5546473).sum := by decide
  have hdescent : baseEnd_5546473 < baseStart_5546473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546541 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5546541 : Nat := 118140960795 + 5546541 * 2 ^ 59
def prefixEnd_5546541 : Nat := 4983230072969 + 3 ^ 40 * 5546541 * 2
def baseEnd_5546541 : Nat := 2848041502869488866529429

theorem tailTrace_5546541 : CollatzResearch.WordTrace tailWord_5546541 prefixEnd_5546541 2848041502869488866529429 := by
  unfold tailWord_5546541
  simp only [CollatzResearch.WordTrace]
  refine ⟨202298969798836705631591477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134865979865891137087727651 202298969798836705631591477)
  ·
    refine ⟨18965528418640941152961701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202298969798836705631591477 18965528418640941152961701)
    ·
      refine ⟨3556036578495176466180319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18965528418640941152961701 3556036578495176466180319)
      ·
        refine ⟨5334054867742764699270479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556036578495176466180319 5334054867742764699270479)
        ·
          refine ⟨8001082301614147048905719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334054867742764699270479 8001082301614147048905719)
          ·
            refine ⟨12001623452421220573358579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8001082301614147048905719 12001623452421220573358579)
            ·
              refine ⟨18002435178631830860037869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12001623452421220573358579 18002435178631830860037869)
              ·
                refine ⟨6750913191986936572514201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18002435178631830860037869 6750913191986936572514201)
                ·
                  refine ⟨5063184893990202429385651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750913191986936572514201 5063184893990202429385651)
                  ·
                    refine ⟨7594777340985303644078477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5063184893990202429385651 7594777340985303644078477)
                    ·
                      refine ⟨2848041502869488866529429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594777340985303644078477 2848041502869488866529429)
                      ·
                        rfl

theorem cell23_5546541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5546541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546541 prefixEnd_5546541 := by exact prefixLift 5546541
  have htrace : WordTrace (prefixWord ++ tailWord_5546541) baseStart_5546541 baseEnd_5546541 := by
    simpa [prefixWord, tailWord_5546541, baseEnd_5546541] using wordTrace_append hprefix tailTrace_5546541
  have hstable : (prefixWord ++ tailWord_5546541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546541).length < 2 ^ (prefixWord ++ tailWord_5546541).sum := by decide
  have hdescent : baseEnd_5546541 < baseStart_5546541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546586 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_5546586 : Nat := 118140960795 + 5546586 * 2 ^ 59
def prefixEnd_5546586 : Nat := 4983230072969 + 3 ^ 40 * 5546586 * 2
def baseEnd_5546586 : Nat := 2848064609498941190466721

theorem tailTrace_5546586 : CollatzResearch.WordTrace tailWord_5546586 prefixEnd_5546586 2848064609498941190466721 := by
  unfold tailWord_5546586
  simp only [CollatzResearch.WordTrace]
  refine ⟨50575152770918419579244903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134867074055782452211319741 50575152770918419579244903)
  ·
    refine ⟨75862729156377629368867355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50575152770918419579244903 75862729156377629368867355)
    ·
      refine ⟨113794093734566444053301033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75862729156377629368867355 113794093734566444053301033)
      ·
        refine ⟨85345570300924833039975775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113794093734566444053301033 85345570300924833039975775)
        ·
          refine ⟨128018355451387249559963663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85345570300924833039975775 128018355451387249559963663)
          ·
            refine ⟨192027533177080874339945495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128018355451387249559963663 192027533177080874339945495)
            ·
              refine ⟨288041299765621311509918243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192027533177080874339945495 288041299765621311509918243)
              ·
                refine ⟨432061949648431967264877365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288041299765621311509918243 432061949648431967264877365)
                ·
                  refine ⟨40505807779540496931082253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 432061949648431967264877365 40505807779540496931082253)
                  ·
                    refine ⟨15189677917327686349155845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40505807779540496931082253 15189677917327686349155845)
                    ·
                      refine ⟨2848064609498941190466721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15189677917327686349155845 2848064609498941190466721)
                      ·
                        rfl

theorem cell23_5546586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_5546586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546586 prefixEnd_5546586 := by exact prefixLift 5546586
  have htrace : WordTrace (prefixWord ++ tailWord_5546586) baseStart_5546586 baseEnd_5546586 := by
    simpa [prefixWord, tailWord_5546586, baseEnd_5546586] using wordTrace_append hprefix tailTrace_5546586
  have hstable : (prefixWord ++ tailWord_5546586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546586).length < 2 ^ (prefixWord ++ tailWord_5546586).sum := by decide
  have hdescent : baseEnd_5546586 < baseStart_5546586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546616 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_5546616 : Nat := 118140960795 + 5546616 * 2 ^ 59
def prefixEnd_5546616 : Nat := 4983230072969 + 3 ^ 40 * 5546616 * 2
def baseEnd_5546616 : Nat := 2848080013918576073091583

theorem tailTrace_5546616 : CollatzResearch.WordTrace tailWord_5546616 prefixEnd_5546616 2848080013918576073091583 := by
  unfold tailWord_5546616
  simp only [CollatzResearch.WordTrace]
  refine ⟨101150852636782496720285851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134867803515709995627047801 101150852636782496720285851)
  ·
    refine ⟨151726278955173745080428777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101150852636782496720285851 151726278955173745080428777)
    ·
      refine ⟨113794709216380308810321583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151726278955173745080428777 113794709216380308810321583)
      ·
        refine ⟨170692063824570463215482375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113794709216380308810321583 170692063824570463215482375)
        ·
          refine ⟨256038095736855694823223563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170692063824570463215482375 256038095736855694823223563)
          ·
            refine ⟨384057143605283542234835345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256038095736855694823223563 384057143605283542234835345)
            ·
              refine ⟨288042857703962656676126509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384057143605283542234835345 288042857703962656676126509)
              ·
                refine ⟨108016071638985996253547441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288042857703962656676126509 108016071638985996253547441)
                ·
                  refine ⟨81012053729239497190160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108016071638985996253547441 81012053729239497190160581)
                  ·
                    refine ⟨15189760074232405723155109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81012053729239497190160581 15189760074232405723155109)
                    ·
                      refine ⟨2848080013918576073091583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15189760074232405723155109 2848080013918576073091583)
                      ·
                        rfl

theorem cell23_5546616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_5546616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546616 prefixEnd_5546616 := by exact prefixLift 5546616
  have htrace : WordTrace (prefixWord ++ tailWord_5546616) baseStart_5546616 baseEnd_5546616 := by
    simpa [prefixWord, tailWord_5546616, baseEnd_5546616] using wordTrace_append hprefix tailTrace_5546616
  have hstable : (prefixWord ++ tailWord_5546616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546616).length < 2 ^ (prefixWord ++ tailWord_5546616).sum := by decide
  have hdescent : baseEnd_5546616 < baseStart_5546616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546623 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_5546623 : Nat := 118140960795 + 5546623 * 2 ^ 59
def prefixEnd_5546623 : Nat := 4983230072969 + 3 ^ 40 * 5546623 * 2
def baseEnd_5546623 : Nat := 2848083608283157545704051

theorem tailTrace_5546623 : CollatzResearch.WordTrace tailWord_5546623 prefixEnd_5546623 2848083608283157545704051 := by
  unfold tailWord_5546623
  simp only [CollatzResearch.WordTrace]
  refine ⟨202301960584539633636076523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134867973723026422424051015 202301960584539633636076523)
  ·
    refine ⟨303452940876809450454114785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202301960584539633636076523 303452940876809450454114785)
    ·
      refine ⟨227589705657607087840586089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303452940876809450454114785 227589705657607087840586089)
      ·
        refine ⟨170692279243205315880439567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227589705657607087840586089 170692279243205315880439567)
        ·
          refine ⟨256038418864807973820659351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170692279243205315880439567 256038418864807973820659351)
          ·
            refine ⟨384057628297211960730989027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256038418864807973820659351 384057628297211960730989027)
            ·
              refine ⟨576086442445817941096483541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384057628297211960730989027 576086442445817941096483541)
              ·
                refine ⟨13502025994823857994448833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 576086442445817941096483541 13502025994823857994448833)
                ·
                  refine ⟨10126519496117893495836625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13502025994823857994448833 10126519496117893495836625)
                  ·
                    refine ⟨7594889622088420121877469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10126519496117893495836625 7594889622088420121877469)
                    ·
                      refine ⟨2848083608283157545704051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7594889622088420121877469 2848083608283157545704051)
                      ·
                        rfl

theorem cell23_5546623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_5546623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546623 prefixEnd_5546623 := by exact prefixLift 5546623
  have htrace : WordTrace (prefixWord ++ tailWord_5546623) baseStart_5546623 baseEnd_5546623 := by
    simpa [prefixWord, tailWord_5546623, baseEnd_5546623] using wordTrace_append hprefix tailTrace_5546623
  have hstable : (prefixWord ++ tailWord_5546623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546623).length < 2 ^ (prefixWord ++ tailWord_5546623).sum := by decide
  have hdescent : baseEnd_5546623 < baseStart_5546623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546660 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 6]
def baseStart_5546660 : Nat := 118140960795 + 5546660 * 2 ^ 59
def prefixEnd_5546660 : Nat := 4983230072969 + 3 ^ 40 * 5546660 * 2
def baseEnd_5546660 : Nat := 316455845229708211215709

theorem tailTrace_5546660 : CollatzResearch.WordTrace tailWord_5546660 prefixEnd_5546660 316455845229708211215709 := by
  unfold tailWord_5546660
  simp only [CollatzResearch.WordTrace]
  refine ⟨101151655042702794477586717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134868873390270392636782289 101151655042702794477586717)
  ·
    refine ⟨37931870641013547929095019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101151655042702794477586717 37931870641013547929095019)
    ·
      refine ⟨56897805961520321893642529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37931870641013547929095019 56897805961520321893642529)
      ·
        refine ⟨42673354471140241420231897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56897805961520321893642529 42673354471140241420231897)
        ·
          refine ⟨32005015853355181065173923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42673354471140241420231897 32005015853355181065173923)
          ·
            refine ⟨48007523780032771597760885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32005015853355181065173923 48007523780032771597760885)
            ·
              refine ⟨4500705354378072337290083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48007523780032771597760885 4500705354378072337290083)
              ·
                refine ⟨6751058031567108505935125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500705354378072337290083 6751058031567108505935125)
                ·
                  refine ⟨316455845229708211215709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6751058031567108505935125 316455845229708211215709)
                  ·
                    rfl

theorem cell23_5546660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_5546660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546660 prefixEnd_5546660 := by exact prefixLift 5546660
  have htrace : WordTrace (prefixWord ++ tailWord_5546660) baseStart_5546660 baseEnd_5546660 := by
    simpa [prefixWord, tailWord_5546660, baseEnd_5546660] using wordTrace_append hprefix tailTrace_5546660
  have hstable : (prefixWord ++ tailWord_5546660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546660).length < 2 ^ (prefixWord ++ tailWord_5546660).sum := by decide
  have hdescent : baseEnd_5546660 < baseStart_5546660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546713 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_5546713 : Nat := 118140960795 + 5546713 * 2 ^ 59
def prefixEnd_5546713 : Nat := 4983230072969 + 3 ^ 40 * 5546713 * 2
def baseEnd_5546713 : Nat := 2848129821542062193578637

theorem tailTrace_5546713 : CollatzResearch.WordTrace tailWord_5546713 prefixEnd_5546713 2848129821542062193578637 := by
  unfold tailWord_5546713
  simp only [CollatzResearch.WordTrace]
  refine ⟨202305243154213579006852793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134870162102809052671235195 202305243154213579006852793)
  ·
    refine ⟨151728932365660184255139595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202305243154213579006852793 151728932365660184255139595)
    ·
      refine ⟨227593398548490276382709393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151728932365660184255139595 227593398548490276382709393)
      ·
        refine ⟨170695048911367707287032045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227593398548490276382709393 170695048911367707287032045)
        ·
          refine ⟨64010643341762890232637017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170695048911367707287032045 64010643341762890232637017)
          ·
            refine ⟨48007982506322167674477763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64010643341762890232637017 48007982506322167674477763)
            ·
              refine ⟨72011973759483251511716645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48007982506322167674477763 72011973759483251511716645)
              ·
                refine ⟨13502245079903109658446871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72011973759483251511716645 13502245079903109658446871)
                ·
                  refine ⟨20253367619854664487670307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13502245079903109658446871 20253367619854664487670307)
                  ·
                    refine ⟨30380051429781996731505461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20253367619854664487670307 30380051429781996731505461)
                    ·
                      refine ⟨2848129821542062193578637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30380051429781996731505461 2848129821542062193578637)
                      ·
                        rfl

theorem cell23_5546713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_5546713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546713 prefixEnd_5546713 := by exact prefixLift 5546713
  have htrace : WordTrace (prefixWord ++ tailWord_5546713) baseStart_5546713 baseEnd_5546713 := by
    simpa [prefixWord, tailWord_5546713, baseEnd_5546713] using wordTrace_append hprefix tailTrace_5546713
  have hstable : (prefixWord ++ tailWord_5546713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546713).length < 2 ^ (prefixWord ++ tailWord_5546713).sum := by decide
  have hdescent : baseEnd_5546713 < baseStart_5546713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546733 : List Nat := [1, 5, 1, 2, 1, 1, 1, 11]
def baseStart_5546733 : Nat := 118140960795 + 5546733 * 2 ^ 59
def prefixEnd_5546733 : Nat := 4983230072969 + 3 ^ 40 * 5546733 * 2
def baseEnd_5546733 : Nat := 105486670042783411678835

theorem tailTrace_5546733 : CollatzResearch.WordTrace tailWord_5546733 prefixEnd_5546733 105486670042783411678835 := by
  unfold tailWord_5546733
  simp only [CollatzResearch.WordTrace]
  refine ⟨202305972614141122422580853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134870648409427414948387235 202305972614141122422580853)
  ·
    refine ⟨18966184932575730227116955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202305972614141122422580853 18966184932575730227116955)
    ·
      refine ⟨28449277398863595340675433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18966184932575730227116955 28449277398863595340675433)
      ·
        refine ⟨21336958049147696505506575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28449277398863595340675433 21336958049147696505506575)
        ·
          refine ⟨32005437073721544758259863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21336958049147696505506575 32005437073721544758259863)
          ·
            refine ⟨48008155610582317137389795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32005437073721544758259863 48008155610582317137389795)
            ·
              refine ⟨72012233415873475706084693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48008155610582317137389795 72012233415873475706084693)
              ·
                refine ⟨105486670042783411678835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 72012233415873475706084693 105486670042783411678835)
                ·
                  rfl

theorem cell23_5546733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 11].length) (baseStart_5546733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546733 prefixEnd_5546733 := by exact prefixLift 5546733
  have htrace : WordTrace (prefixWord ++ tailWord_5546733) baseStart_5546733 baseEnd_5546733 := by
    simpa [prefixWord, tailWord_5546733, baseEnd_5546733] using wordTrace_append hprefix tailTrace_5546733
  have hstable : (prefixWord ++ tailWord_5546733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546733).length < 2 ^ (prefixWord ++ tailWord_5546733).sum := by decide
  have hdescent : baseEnd_5546733 < baseStart_5546733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546744 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 1, 2, 2]
def baseStart_5546744 : Nat := 118140960795 + 5546744 * 2 ^ 59
def prefixEnd_5546744 : Nat := 4983230072969 + 3 ^ 40 * 5546744 * 2
def baseEnd_5546744 : Nat := 2848145739442351572290995

theorem tailTrace_5546744 : CollatzResearch.WordTrace tailWord_5546744 prefixEnd_5546744 2848145739442351572290995 := by
  unfold tailWord_5546744
  simp only [CollatzResearch.WordTrace]
  refine ⟨101153186908550635650615643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134870915878067514200820857 101153186908550635650615643)
  ·
    refine ⟨151729780362825953475923465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101153186908550635650615643 151729780362825953475923465)
    ·
      refine ⟨113797335272119465106942599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151729780362825953475923465 113797335272119465106942599)
      ·
        refine ⟨170696002908179197660413899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113797335272119465106942599 170696002908179197660413899)
        ·
          refine ⟨256044004362268796490620849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170696002908179197660413899 256044004362268796490620849)
          ·
            refine ⟨192033003271701597367965637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256044004362268796490620849 192033003271701597367965637)
            ·
              refine ⟨36006188113444049506493557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192033003271701597367965637 36006188113444049506493557)
              ·
                refine ⟨3375580135635379641233771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36006188113444049506493557 3375580135635379641233771)
                ·
                  refine ⟨5063370203453069461850657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375580135635379641233771 5063370203453069461850657)
                  ·
                    refine ⟨3797527652589802096387993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063370203453069461850657 3797527652589802096387993)
                    ·
                      refine ⟨2848145739442351572290995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797527652589802096387993 2848145739442351572290995)
                      ·
                        rfl

theorem cell23_5546744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_5546744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546744 prefixEnd_5546744 := by exact prefixLift 5546744
  have htrace : WordTrace (prefixWord ++ tailWord_5546744) baseStart_5546744 baseEnd_5546744 := by
    simpa [prefixWord, tailWord_5546744, baseEnd_5546744] using wordTrace_append hprefix tailTrace_5546744
  have hstable : (prefixWord ++ tailWord_5546744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546744).length < 2 ^ (prefixWord ++ tailWord_5546744).sum := by decide
  have hdescent : baseEnd_5546744 < baseStart_5546744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546754 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_5546754 : Nat := 118140960795 + 5546754 * 2 ^ 59
def prefixEnd_5546754 : Nat := 4983230072969 + 3 ^ 40 * 5546754 * 2
def baseEnd_5546754 : Nat := 949383624749632177721983

theorem tailTrace_5546754 : CollatzResearch.WordTrace tailWord_5546754 prefixEnd_5546754 949383624749632177721983 := by
  unfold tailWord_5546754
  simp only [CollatzResearch.WordTrace]
  refine ⟨50576684636766260752273829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134871159031376695339396877 50576684636766260752273829)
  ·
    refine ⟨9483128369393673891051343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50576684636766260752273829 9483128369393673891051343)
    ·
      refine ⟨14224692554090510836577015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9483128369393673891051343 14224692554090510836577015)
      ·
        refine ⟨21337038831135766254865523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14224692554090510836577015 21337038831135766254865523)
        ·
          refine ⟨32005558246703649382298285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21337038831135766254865523 32005558246703649382298285)
          ·
            refine ⟨12002084342513868518361857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32005558246703649382298285 12002084342513868518361857)
            ·
              refine ⟨9001563256885401388771393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12002084342513868518361857 9001563256885401388771393)
              ·
                refine ⟨6751172442664051041578545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9001563256885401388771393 6751172442664051041578545)
                ·
                  refine ⟨5063379331998038281183909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6751172442664051041578545 5063379331998038281183909)
                  ·
                    refine ⟨949383624749632177721983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5063379331998038281183909 949383624749632177721983)
                    ·
                      rfl

theorem cell23_5546754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_5546754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546754 prefixEnd_5546754 := by exact prefixLift 5546754
  have htrace : WordTrace (prefixWord ++ tailWord_5546754) baseStart_5546754 baseEnd_5546754 := by
    simpa [prefixWord, tailWord_5546754, baseEnd_5546754] using wordTrace_append hprefix tailTrace_5546754
  have hstable : (prefixWord ++ tailWord_5546754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546754).length < 2 ^ (prefixWord ++ tailWord_5546754).sum := by decide
  have hdescent : baseEnd_5546754 < baseStart_5546754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546761 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 1, 2, 2]
def baseStart_5546761 : Nat := 118140960795 + 5546761 * 2 ^ 59
def prefixEnd_5546761 : Nat := 4983230072969 + 3 ^ 40 * 5546761 * 2
def baseEnd_5546761 : Nat := 2848154468613478005778417

theorem tailTrace_5546761 : CollatzResearch.WordTrace tailWord_5546761 prefixEnd_5546761 2848154468613478005778417 := by
  unfold tailWord_5546761
  simp only [CollatzResearch.WordTrace]
  refine ⟨202306993858039683204600137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134871329238693122136400091 202306993858039683204600137)
  ·
    refine ⟨151730245393529762403450103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202306993858039683204600137 151730245393529762403450103)
    ·
      refine ⟨227595368090294643605175155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151730245393529762403450103 227595368090294643605175155)
      ·
        refine ⟨341393052135441965407762733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227595368090294643605175155 341393052135441965407762733)
        ·
          refine ⟨128022394550790737027911025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341393052135441965407762733 128022394550790737027911025)
          ·
            refine ⟨96016795913093052770933269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128022394550790737027911025 96016795913093052770933269)
            ·
              refine ⟨4500787308426236848637497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96016795913093052770933269 4500787308426236848637497)
              ·
                refine ⟨3375590481319677636478123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500787308426236848637497 3375590481319677636478123)
                ·
                  refine ⟨5063385721979516454717185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375590481319677636478123 5063385721979516454717185)
                  ·
                    refine ⟨3797539291484637341037889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063385721979516454717185 3797539291484637341037889)
                    ·
                      refine ⟨2848154468613478005778417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797539291484637341037889 2848154468613478005778417)
                      ·
                        rfl

theorem cell23_5546761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 2, 2].length) (baseStart_5546761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546761 prefixEnd_5546761 := by exact prefixLift 5546761
  have htrace : WordTrace (prefixWord ++ tailWord_5546761) baseStart_5546761 baseEnd_5546761 := by
    simpa [prefixWord, tailWord_5546761, baseEnd_5546761] using wordTrace_append hprefix tailTrace_5546761
  have hstable : (prefixWord ++ tailWord_5546761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546761).length < 2 ^ (prefixWord ++ tailWord_5546761).sum := by decide
  have hdescent : baseEnd_5546761 < baseStart_5546761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546787 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 1, 3, 2]
def baseStart_5546787 : Nat := 118140960795 + 5546787 * 2 ^ 59
def prefixEnd_5546787 : Nat := 4983230072969 + 3 ^ 40 * 5546787 * 2
def baseEnd_5546787 : Nat := 2848167819110494904053297

theorem tailTrace_5546787 : CollatzResearch.WordTrace tailWord_5546787 prefixEnd_5546787 2848167819110494904053297 := by
  unfold tailWord_5546787
  simp only [CollatzResearch.WordTrace]
  refine ⟨202307942155945489645046615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134871961437296993096697743 202307942155945489645046615)
  ·
    refine ⟨303461913233918234467569923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202307942155945489645046615 303461913233918234467569923)
    ·
      refine ⟨455192869850877351701354885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303461913233918234467569923 455192869850877351701354885)
      ·
        refine ⟨85348663097039503444004041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 455192869850877351701354885 85348663097039503444004041)
        ·
          refine ⟨64011497322779627583003031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85348663097039503444004041 64011497322779627583003031)
          ·
            refine ⟨96017245984169441374504547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64011497322779627583003031 96017245984169441374504547)
            ·
              refine ⟨144025868976254162061756821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96017245984169441374504547 144025868976254162061756821)
              ·
                refine ⟨6751212608261913846644851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144025868976254162061756821 6751212608261913846644851)
                ·
                  refine ⟨10126818912392870769967277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6751212608261913846644851 10126818912392870769967277)
                  ·
                    refine ⟨3797557092147326538737729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10126818912392870769967277 3797557092147326538737729)
                    ·
                      refine ⟨2848167819110494904053297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797557092147326538737729 2848167819110494904053297)
                      ·
                        rfl

theorem cell23_5546787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_5546787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546787 prefixEnd_5546787 := by exact prefixLift 5546787
  have htrace : WordTrace (prefixWord ++ tailWord_5546787) baseStart_5546787 baseEnd_5546787 := by
    simpa [prefixWord, tailWord_5546787, baseEnd_5546787] using wordTrace_append hprefix tailTrace_5546787
  have hstable : (prefixWord ++ tailWord_5546787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546787).length < 2 ^ (prefixWord ++ tailWord_5546787).sum := by decide
  have hdescent : baseEnd_5546787 < baseStart_5546787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546863 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_5546863 : Nat := 118140960795 + 5546863 * 2 ^ 59
def prefixEnd_5546863 : Nat := 4983230072969 + 3 ^ 40 * 5546863 * 2
def baseEnd_5546863 : Nat := 2848206843640236606702947

theorem tailTrace_5546863 : CollatzResearch.WordTrace tailWord_5546863 prefixEnd_5546863 2848206843640236606702947 := by
  unfold tailWord_5546863
  simp only [CollatzResearch.WordTrace]
  refine ⟨202310714103670154624813243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134873809402446769749875495 202310714103670154624813243)
  ·
    refine ⟨303466071155505231937219865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202310714103670154624813243 303466071155505231937219865)
    ·
      refine ⟨227599553366628923952914899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303466071155505231937219865 227599553366628923952914899)
      ·
        refine ⟨341399330049943385929372349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227599553366628923952914899 341399330049943385929372349)
        ·
          refine ⟨128024748768728769723514631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341399330049943385929372349 128024748768728769723514631)
          ·
            refine ⟨192037123153093154585271947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128024748768728769723514631 192037123153093154585271947)
            ·
              refine ⟨288055684729639731877907921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192037123153093154585271947 288055684729639731877907921)
              ·
                refine ⟨216041763547229798908430941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288055684729639731877907921 216041763547229798908430941)
                ·
                  refine ⟨81015661330211174590661603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216041763547229798908430941 81015661330211174590661603)
                  ·
                    refine ⟨121523491995316761885992405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81015661330211174590661603 121523491995316761885992405)
                    ·
                      refine ⟨2848206843640236606702947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121523491995316761885992405 2848206843640236606702947)
                      ·
                        rfl

theorem cell23_5546863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_5546863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546863 prefixEnd_5546863 := by exact prefixLift 5546863
  have htrace : WordTrace (prefixWord ++ tailWord_5546863) baseStart_5546863 baseEnd_5546863 := by
    simpa [prefixWord, tailWord_5546863, baseEnd_5546863] using wordTrace_append hprefix tailTrace_5546863
  have hstable : (prefixWord ++ tailWord_5546863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546863).length < 2 ^ (prefixWord ++ tailWord_5546863).sum := by decide
  have hdescent : baseEnd_5546863 < baseStart_5546863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546925 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 5]
def baseStart_5546925 : Nat := 118140960795 + 5546925 * 2 ^ 59
def prefixEnd_5546925 : Nat := 4983230072969 + 3 ^ 40 * 5546925 * 2
def baseEnd_5546925 : Nat := 316470964382312818236407

theorem tailTrace_5546925 : CollatzResearch.WordTrace tailWord_5546925 prefixEnd_5546925 316470964382312818236407 := by
  unfold tailWord_5546925
  simp only [CollatzResearch.WordTrace]
  refine ⟨202312975429445539213570229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134875316952963692809046819 202312975429445539213570229)
  ·
    refine ⟨18966841446510519301272209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202312975429445539213570229 18966841446510519301272209)
    ·
      refine ⟨14225131084882889475954157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18966841446510519301272209 14225131084882889475954157)
      ·
        refine ⟨5334424156831083553482809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14225131084882889475954157 5334424156831083553482809)
        ·
          refine ⟨4000818117623312665112107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5334424156831083553482809 4000818117623312665112107)
          ·
            refine ⟨6001227176434968997668161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000818117623312665112107 6001227176434968997668161)
            ·
              refine ⟨4500920382326226748251121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001227176434968997668161 4500920382326226748251121)
              ·
                refine ⟨3375690286744670061188341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500920382326226748251121 3375690286744670061188341)
                ·
                  refine ⟨316470964382312818236407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375690286744670061188341 316470964382312818236407)
                  ·
                    rfl

theorem cell23_5546925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_5546925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546925 prefixEnd_5546925 := by exact prefixLift 5546925
  have htrace : WordTrace (prefixWord ++ tailWord_5546925) baseStart_5546925 baseEnd_5546925 := by
    simpa [prefixWord, tailWord_5546925, baseEnd_5546925] using wordTrace_append hprefix tailTrace_5546925
  have hstable : (prefixWord ++ tailWord_5546925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546925).length < 2 ^ (prefixWord ++ tailWord_5546925).sum := by decide
  have hdescent : baseEnd_5546925 < baseStart_5546925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546981 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 6]
def baseStart_5546981 : Nat := 118140960795 + 5546981 * 2 ^ 59
def prefixEnd_5546981 : Nat := 4983230072969 + 3 ^ 40 * 5546981 * 2
def baseEnd_5546981 : Nat := 316474159373051905003045

theorem tailTrace_5546981 : CollatzResearch.WordTrace tailWord_5546981 prefixEnd_5546981 316474159373051905003045 := by
  unfold tailWord_5546981
  simp only [CollatzResearch.WordTrace]
  refine ⟨202315017917242660777608797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134876678611495107185072531 202315017917242660777608797)
  ·
    refine ⟨75868131718965997791603299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202315017917242660777608797 75868131718965997791603299)
    ·
      refine ⟨113802197578448996687404949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75868131718965997791603299 113802197578448996687404949)
      ·
        refine ⟨5334478011489796719722107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113802197578448996687404949 5334478011489796719722107)
        ·
          refine ⟨8001717017234695079583161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334478011489796719722107 8001717017234695079583161)
          ·
            refine ⟨6001287762926021309687371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8001717017234695079583161 6001287762926021309687371)
            ·
              refine ⟨9001931644389031964531057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6001287762926021309687371 9001931644389031964531057)
              ·
                refine ⟨6751448733291773973398293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9001931644389031964531057 6751448733291773973398293)
                ·
                  refine ⟨316474159373051905003045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6751448733291773973398293 316474159373051905003045)
                  ·
                    rfl

theorem cell23_5546981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_5546981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546981 prefixEnd_5546981 := by exact prefixLift 5546981
  have htrace : WordTrace (prefixWord ++ tailWord_5546981) baseStart_5546981 baseEnd_5546981 := by
    simpa [prefixWord, tailWord_5546981, baseEnd_5546981] using wordTrace_append hprefix tailTrace_5546981
  have hstable : (prefixWord ++ tailWord_5546981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546981).length < 2 ^ (prefixWord ++ tailWord_5546981).sum := by decide
  have hdescent : baseEnd_5546981 < baseStart_5546981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546984 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_5546984 : Nat := 118140960795 + 5546984 * 2 ^ 59
def prefixEnd_5546984 : Nat := 4983230072969 + 3 ^ 40 * 5546984 * 2
def baseEnd_5546984 : Nat := 2848268974799430633289891

theorem tailTrace_5546984 : CollatzResearch.WordTrace tailWord_5546984 prefixEnd_5546984 2848268974799430633289891 := by
  unfold tailWord_5546984
  simp only [CollatzResearch.WordTrace]
  refine ⟨101157563668115896144984003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134876751557487861526645337 101157563668115896144984003)
  ·
    refine ⟨151736345502173844217476005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101157563668115896144984003 151736345502173844217476005)
    ·
      refine ⟨28450564781657595790776751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151736345502173844217476005 28450564781657595790776751)
      ·
        refine ⟨42675847172486393686165127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28450564781657595790776751 42675847172486393686165127)
        ·
          refine ⟨64013770758729590529247691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42675847172486393686165127 64013770758729590529247691)
          ·
            refine ⟨96020656138094385793871537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64013770758729590529247691 96020656138094385793871537)
            ·
              refine ⟨72015492103570789345403653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96020656138094385793871537 72015492103570789345403653)
              ·
                refine ⟨13502904769419523002263185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72015492103570789345403653 13502904769419523002263185)
                ·
                  refine ⟨10127178577064642251697389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13502904769419523002263185 10127178577064642251697389)
                  ·
                    refine ⟨3797691966399240844386521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10127178577064642251697389 3797691966399240844386521)
                    ·
                      refine ⟨2848268974799430633289891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797691966399240844386521 2848268974799430633289891)
                      ·
                        rfl

theorem cell23_5546984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_5546984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546984 prefixEnd_5546984 := by exact prefixLift 5546984
  have htrace : WordTrace (prefixWord ++ tailWord_5546984) baseStart_5546984 baseEnd_5546984 := by
    simpa [prefixWord, tailWord_5546984, baseEnd_5546984] using wordTrace_append hprefix tailTrace_5546984
  have hstable : (prefixWord ++ tailWord_5546984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546984).length < 2 ^ (prefixWord ++ tailWord_5546984).sum := by decide
  have hdescent : baseEnd_5546984 < baseStart_5546984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5546991 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 1, 1, 3]
def baseStart_5546991 : Nat := 118140960795 + 5546991 * 2 ^ 59
def prefixEnd_5546991 : Nat := 4983230072969 + 3 ^ 40 * 5546991 * 2
def baseEnd_5546991 : Nat := 2848272569164012105902359

theorem tailTrace_5546991 : CollatzResearch.WordTrace tailWord_5546991 prefixEnd_5546991 2848272569164012105902359 := by
  unfold tailWord_5546991
  simp only [CollatzResearch.WordTrace]
  refine ⟨202315382647206432485472827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134876921764804288323648551 202315382647206432485472827)
  ·
    refine ⟨303473073970809648728209241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202315382647206432485472827 303473073970809648728209241)
    ·
      refine ⟨227604805478107236546156931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303473073970809648728209241 227604805478107236546156931)
      ·
        refine ⟨341407208217160854819235397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227604805478107236546156931 341407208217160854819235397)
        ·
          refine ⟨64013851540717660278606637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 341407208217160854819235397 64013851540717660278606637)
          ·
            refine ⟨24005194327769122604477489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64013851540717660278606637 24005194327769122604477489)
            ·
              refine ⟨18003895745826841953358117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24005194327769122604477489 18003895745826841953358117)
              ·
                refine ⟨3375730452342532866254647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18003895745826841953358117 3375730452342532866254647)
                ·
                  refine ⟨5063595678513799299381971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375730452342532866254647 5063595678513799299381971)
                  ·
                    refine ⟨7595393517770698949072957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5063595678513799299381971 7595393517770698949072957)
                    ·
                      refine ⟨2848272569164012105902359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7595393517770698949072957 2848272569164012105902359)
                      ·
                        rfl

theorem cell23_5546991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 1, 3].length) (baseStart_5546991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5546991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5546991 prefixEnd_5546991 := by exact prefixLift 5546991
  have htrace : WordTrace (prefixWord ++ tailWord_5546991) baseStart_5546991 baseEnd_5546991 := by
    simpa [prefixWord, tailWord_5546991, baseEnd_5546991] using wordTrace_append hprefix tailTrace_5546991
  have hstable : (prefixWord ++ tailWord_5546991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5546991).length < 2 ^ (prefixWord ++ tailWord_5546991).sum := by decide
  have hdescent : baseEnd_5546991 < baseStart_5546991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5546991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547017 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_5547017 : Nat := 118140960795 + 5547017 * 2 ^ 59
def prefixEnd_5547017 : Nat := 4983230072969 + 3 ^ 40 * 5547017 * 2
def baseEnd_5547017 : Nat := 2848285919661029004177239

theorem tailTrace_5547017 : CollatzResearch.WordTrace tailWord_5547017 prefixEnd_5547017 2848285919661029004177239 := by
  unfold tailWord_5547017
  simp only [CollatzResearch.WordTrace]
  refine ⟨202316330945112238925919305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134877553963408159283946203 202316330945112238925919305)
  ·
    refine ⟨151737248208834179194439479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202316330945112238925919305 151737248208834179194439479)
    ·
      refine ⟨227605872313251268791659219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151737248208834179194439479 227605872313251268791659219)
      ·
        refine ⟨341408808469876903187488829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227605872313251268791659219 341408808469876903187488829)
        ·
          refine ⟨128028303176203838695308311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341408808469876903187488829 128028303176203838695308311)
          ·
            refine ⟨192042454764305758042962467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128028303176203838695308311 192042454764305758042962467)
            ·
              refine ⟨288063682146458637064443701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192042454764305758042962467 288063682146458637064443701)
              ·
                refine ⟨27005970201230497224791597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288063682146458637064443701 27005970201230497224791597)
                ·
                  refine ⟨10127238825461436459296849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27005970201230497224791597 10127238825461436459296849)
                  ·
                    refine ⟨7595429119096077344472637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10127238825461436459296849 7595429119096077344472637)
                    ·
                      refine ⟨2848285919661029004177239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7595429119096077344472637 2848285919661029004177239)
                      ·
                        rfl

theorem cell23_5547017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_5547017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547017 prefixEnd_5547017 := by exact prefixLift 5547017
  have htrace : WordTrace (prefixWord ++ tailWord_5547017) baseStart_5547017 baseEnd_5547017 := by
    simpa [prefixWord, tailWord_5547017, baseEnd_5547017] using wordTrace_append hprefix tailTrace_5547017
  have hstable : (prefixWord ++ tailWord_5547017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547017).length < 2 ^ (prefixWord ++ tailWord_5547017).sum := by decide
  have hdescent : baseEnd_5547017 < baseStart_5547017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547034 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_5547034 : Nat := 118140960795 + 5547034 * 2 ^ 59
def prefixEnd_5547034 : Nat := 4983230072969 + 3 ^ 40 * 5547034 * 2
def baseEnd_5547034 : Nat := 2848294648832155437664661

theorem tailTrace_5547034 : CollatzResearch.WordTrace tailWord_5547034 prefixEnd_5547034 2848294648832155437664661 := by
  unfold tailWord_5547034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50579237746512662707322039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134877967324033767219525437 50579237746512662707322039)
  ·
    refine ⟨75868856619768994060983059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50579237746512662707322039 75868856619768994060983059)
    ·
      refine ⟨113803284929653491091474589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75868856619768994060983059 113803284929653491091474589)
      ·
        refine ⟨42676231848620059159302971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113803284929653491091474589 42676231848620059159302971)
        ·
          refine ⟨64014347772930088738954457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42676231848620059159302971 64014347772930088738954457)
          ·
            refine ⟨48010760829697566554215843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64014347772930088738954457 48010760829697566554215843)
            ·
              refine ⟨72016141244546349831323765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48010760829697566554215843 72016141244546349831323765)
              ·
                refine ⟨6751513241676220296686603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72016141244546349831323765 6751513241676220296686603)
                ·
                  refine ⟨10127269862514330445029905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6751513241676220296686603 10127269862514330445029905)
                  ·
                    refine ⟨7595452396885747833772429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10127269862514330445029905 7595452396885747833772429)
                    ·
                      refine ⟨2848294648832155437664661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7595452396885747833772429 2848294648832155437664661)
                      ·
                        rfl

theorem cell23_5547034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_5547034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547034 prefixEnd_5547034 := by exact prefixLift 5547034
  have htrace : WordTrace (prefixWord ++ tailWord_5547034) baseStart_5547034 baseEnd_5547034 := by
    simpa [prefixWord, tailWord_5547034, baseEnd_5547034] using wordTrace_append hprefix tailTrace_5547034
  have hstable : (prefixWord ++ tailWord_5547034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547034).length < 2 ^ (prefixWord ++ tailWord_5547034).sum := by decide
  have hdescent : baseEnd_5547034 < baseStart_5547034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547104 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 3, 4, 2]
def baseStart_5547104 : Nat := 118140960795 + 5547104 * 2 ^ 59
def prefixEnd_5547104 : Nat := 4983230072969 + 3 ^ 40 * 5547104 * 2
def baseEnd_5547104 : Nat := 2848330592477970163789339

theorem tailTrace_5547104 : CollatzResearch.WordTrace tailWord_5547104 prefixEnd_5547104 2848330592477970163789339 := by
  unfold tailWord_5547104
  simp only [CollatzResearch.WordTrace]
  refine ⟨101159752047898526392168183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134879669397198035189557577 101159752047898526392168183)
  ·
    refine ⟨151739628071847789588252275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101159752047898526392168183 151739628071847789588252275)
    ·
      refine ⟨227609442107771684382378413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151739628071847789588252275 227609442107771684382378413)
      ·
        refine ⟨85353540790414381643391905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227609442107771684382378413 85353540790414381643391905)
        ·
          refine ⟨64015155592810786232543929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85353540790414381643391905 64015155592810786232543929)
          ·
            refine ⟨48011366694608089674407947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64015155592810786232543929 48011366694608089674407947)
            ·
              refine ⟨72017050041912134511611921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48011366694608089674407947 72017050041912134511611921)
              ·
                refine ⟨54012787531434100883708941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72017050041912134511611921 54012787531434100883708941)
                ·
                  refine ⟨20254795324287787831390853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54012787531434100883708941 20254795324287787831390853)
                  ·
                    refine ⟨3797774123303960218385785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20254795324287787831390853 3797774123303960218385785)
                    ·
                      refine ⟨2848330592477970163789339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797774123303960218385785 2848330592477970163789339)
                      ·
                        rfl

theorem cell23_5547104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_5547104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547104 prefixEnd_5547104 := by exact prefixLift 5547104
  have htrace : WordTrace (prefixWord ++ tailWord_5547104) baseStart_5547104 baseEnd_5547104 := by
    simpa [prefixWord, tailWord_5547104, baseEnd_5547104] using wordTrace_append hprefix tailTrace_5547104
  have hstable : (prefixWord ++ tailWord_5547104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547104).length < 2 ^ (prefixWord ++ tailWord_5547104).sum := by decide
  have hdescent : baseEnd_5547104 < baseStart_5547104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547114 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_5547114 : Nat := 118140960795 + 5547114 * 2 ^ 59
def prefixEnd_5547114 : Nat := 4983230072969 + 3 ^ 40 * 5547114 * 2
def baseEnd_5547114 : Nat := 949445242428171708221431

theorem tailTrace_5547114 : CollatzResearch.WordTrace tailWord_5547114 prefixEnd_5547114 949445242428171708221431 := by
  unfold tailWord_5547114
  simp only [CollatzResearch.WordTrace]
  refine ⟨50579967206440206123050099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134879912550507216328133597 50579967206440206123050099)
  ·
    refine ⟨75869950809660309184575149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50579967206440206123050099 75869950809660309184575149)
    ·
      refine ⟨28451231553622615944215681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75869950809660309184575149 28451231553622615944215681)
      ·
        refine ⟨21338423665216961958161761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28451231553622615944215681 21338423665216961958161761)
        ·
          refine ⟨16003817748912721468621321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21338423665216961958161761 16003817748912721468621321)
          ·
            refine ⟨12002863311684541101465991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16003817748912721468621321 12002863311684541101465991)
            ·
              refine ⟨18004294967526811652198987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12002863311684541101465991 18004294967526811652198987)
              ·
                refine ⟨27006442451290217478298481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18004294967526811652198987 27006442451290217478298481)
                ·
                  refine ⟨20254831838467663108723861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27006442451290217478298481 20254831838467663108723861)
                  ·
                    refine ⟨949445242428171708221431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20254831838467663108723861 949445242428171708221431)
                    ·
                      rfl

theorem cell23_5547114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_5547114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547114 prefixEnd_5547114 := by exact prefixLift 5547114
  have htrace : WordTrace (prefixWord ++ tailWord_5547114) baseStart_5547114 baseEnd_5547114 := by
    simpa [prefixWord, tailWord_5547114, baseEnd_5547114] using wordTrace_append hprefix tailTrace_5547114
  have hstable : (prefixWord ++ tailWord_5547114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547114).length < 2 ^ (prefixWord ++ tailWord_5547114).sum := by decide
  have hdescent : baseEnd_5547114 < baseStart_5547114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547127 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 7]
def baseStart_5547127 : Nat := 118140960795 + 5547127 * 2 ^ 59
def prefixEnd_5547127 : Nat := 4983230072969 + 3 ^ 40 * 5547127 * 2
def baseEnd_5547127 : Nat := 316482489170335952644637

theorem tailTrace_5547127 : CollatzResearch.WordTrace tailWord_5547127 prefixEnd_5547127 316482489170335952644637 := by
  unfold tailWord_5547127
  simp only [CollatzResearch.WordTrace]
  refine ⟨202320342974713727712423635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134880228649809151808282423 202320342974713727712423635)
  ·
    refine ⟨303480514462070591568635453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202320342974713727712423635 303480514462070591568635453)
    ·
      refine ⟨113805192923276471838238295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303480514462070591568635453 113805192923276471838238295)
      ·
        refine ⟨170707789384914707757357443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113805192923276471838238295 170707789384914707757357443)
        ·
          refine ⟨256061684077372061636036165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170707789384914707757357443 256061684077372061636036165)
          ·
            refine ⟨48011565764507261556756781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256061684077372061636036165 48011565764507261556756781)
            ·
              refine ⟨18004337161690223083783793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48011565764507261556756781 18004337161690223083783793)
              ·
                refine ⟨13503252871267667312837845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18004337161690223083783793 13503252871267667312837845)
                ·
                  refine ⟨316482489170335952644637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13503252871267667312837845 316482489170335952644637)
                  ·
                    rfl

theorem cell23_5547127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 7].length) (baseStart_5547127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547127 prefixEnd_5547127 := by exact prefixLift 5547127
  have htrace : WordTrace (prefixWord ++ tailWord_5547127) baseStart_5547127 baseEnd_5547127 := by
    simpa [prefixWord, tailWord_5547127, baseEnd_5547127] using wordTrace_append hprefix tailTrace_5547127
  have hstable : (prefixWord ++ tailWord_5547127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547127).length < 2 ^ (prefixWord ++ tailWord_5547127).sum := by decide
  have hdescent : baseEnd_5547127 < baseStart_5547127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547194 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_5547194 : Nat := 118140960795 + 5547194 * 2 ^ 59
def prefixEnd_5547194 : Nat := 4983230072969 + 3 ^ 40 * 5547194 * 2
def baseEnd_5547194 : Nat := 2848376805736874811663925

theorem tailTrace_5547194 : CollatzResearch.WordTrace tailWord_5547194 prefixEnd_5547194 2848376805736874811663925 := by
  unfold tailWord_5547194
  simp only [CollatzResearch.WordTrace]
  refine ⟨50580696666367749538778159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134881857776980665436741757 50580696666367749538778159)
  ·
    refine ⟨75871044999551624308167239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50580696666367749538778159 75871044999551624308167239)
    ·
      refine ⟨113806567499327436462250859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75871044999551624308167239 113806567499327436462250859)
      ·
        refine ⟨170709851248991154693376289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113806567499327436462250859 170709851248991154693376289)
        ·
          refine ⟨128032388436743366020032217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170709851248991154693376289 128032388436743366020032217)
          ·
            refine ⟨96024291327557524515024163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128032388436743366020032217 96024291327557524515024163)
            ·
              refine ⟨144036436991336286772536245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96024291327557524515024163 144036436991336286772536245)
              ·
                refine ⟨13503415967937776884925273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144036436991336286772536245 13503415967937776884925273)
                ·
                  refine ⟨10127561975953332663693955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13503415967937776884925273 10127561975953332663693955)
                  ·
                    refine ⟨15191342963929998995540933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10127561975953332663693955 15191342963929998995540933)
                    ·
                      refine ⟨2848376805736874811663925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15191342963929998995540933 2848376805736874811663925)
                      ·
                        rfl

theorem cell23_5547194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_5547194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547194 prefixEnd_5547194 := by exact prefixLift 5547194
  have htrace : WordTrace (prefixWord ++ tailWord_5547194) baseStart_5547194 baseEnd_5547194 := by
    simpa [prefixWord, tailWord_5547194, baseEnd_5547194] using wordTrace_append hprefix tailTrace_5547194
  have hstable : (prefixWord ++ tailWord_5547194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547194).length < 2 ^ (prefixWord ++ tailWord_5547194).sum := by decide
  have hdescent : baseEnd_5547194 < baseStart_5547194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547207 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5547207 : Nat := 118140960795 + 5547207 * 2 ^ 59
def prefixEnd_5547207 : Nat := 4983230072969 + 3 ^ 40 * 5547207 * 2
def baseEnd_5547207 : Nat := 2848383480985383260801365

theorem tailTrace_5547207 : CollatzResearch.WordTrace tailWord_5547207 prefixEnd_5547207 2848383480985383260801365 := by
  unfold tailWord_5547207
  simp only [CollatzResearch.WordTrace]
  refine ⟨202323260814423901375335875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134882173876282600916890583 202323260814423901375335875)
  ·
    refine ⟨303484891221635852063003813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202323260814423901375335875 303484891221635852063003813)
    ·
      refine ⟨56903417104056722261813215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303484891221635852063003813 56903417104056722261813215)
      ·
        refine ⟨85355125656085083392719823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56903417104056722261813215 85355125656085083392719823)
        ·
          refine ⟨128032688484127625089079735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85355125656085083392719823 128032688484127625089079735)
          ·
            refine ⟨192049032726191437633619603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128032688484127625089079735 192049032726191437633619603)
            ·
              refine ⟨288073549089287156450429405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192049032726191437633619603 288073549089287156450429405)
              ·
                refine ⟨108027580908482683668911027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288073549089287156450429405 108027580908482683668911027)
                ·
                  refine ⟨162041371362724025503366541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108027580908482683668911027 162041371362724025503366541)
                  ·
                    refine ⟨60765514261021509563762453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162041371362724025503366541 60765514261021509563762453)
                    ·
                      refine ⟨2848383480985383260801365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60765514261021509563762453 2848383480985383260801365)
                      ·
                        rfl

theorem cell23_5547207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5547207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547207 prefixEnd_5547207 := by exact prefixLift 5547207
  have htrace : WordTrace (prefixWord ++ tailWord_5547207) baseStart_5547207 baseEnd_5547207 := by
    simpa [prefixWord, tailWord_5547207, baseEnd_5547207] using wordTrace_append hprefix tailTrace_5547207
  have hstable : (prefixWord ++ tailWord_5547207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547207).length < 2 ^ (prefixWord ++ tailWord_5547207).sum := by decide
  have hdescent : baseEnd_5547207 < baseStart_5547207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547254 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5547254 : Nat := 118140960795 + 5547254 * 2 ^ 59
def prefixEnd_5547254 : Nat := 4983230072969 + 3 ^ 40 * 5547254 * 2
def baseEnd_5547254 : Nat := 2848407614576144576913649

theorem tailTrace_5547254 : CollatzResearch.WordTrace tailWord_5547254 prefixEnd_5547254 2848407614576144576913649 := by
  unfold tailWord_5547254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12645310940328351775143551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134883316696835752268197877 12645310940328351775143551)
  ·
    refine ⟨18967966410492527662715327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12645310940328351775143551 18967966410492527662715327)
    ·
      refine ⟨28451949615738791494072991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18967966410492527662715327 28451949615738791494072991)
      ·
        refine ⟨42677924423608187241109487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28451949615738791494072991 42677924423608187241109487)
        ·
          refine ⟨64016886635412280861664231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42677924423608187241109487 64016886635412280861664231)
          ·
            refine ⟨96025329953118421292496347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64016886635412280861664231 96025329953118421292496347)
            ·
              refine ⟨144037994929677631938744521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96025329953118421292496347 144037994929677631938744521)
              ·
                refine ⟨108028496197258223954058391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144037994929677631938744521 108028496197258223954058391)
                ·
                  refine ⟨162042744295887335931087587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108028496197258223954058391 162042744295887335931087587)
                  ·
                    refine ⟨243064116443831003896631381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162042744295887335931087587 243064116443831003896631381)
                    ·
                      refine ⟨2848407614576144576913649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 243064116443831003896631381 2848407614576144576913649)
                      ·
                        rfl

theorem cell23_5547254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5547254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547254 prefixEnd_5547254 := by exact prefixLift 5547254
  have htrace : WordTrace (prefixWord ++ tailWord_5547254) baseStart_5547254 baseEnd_5547254 := by
    simpa [prefixWord, tailWord_5547254, baseEnd_5547254] using wordTrace_append hprefix tailTrace_5547254
  have hstable : (prefixWord ++ tailWord_5547254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547254).length < 2 ^ (prefixWord ++ tailWord_5547254).sum := by decide
  have hdescent : baseEnd_5547254 < baseStart_5547254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547272 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 1, 4]
def baseStart_5547272 : Nat := 118140960795 + 5547272 * 2 ^ 59
def prefixEnd_5547272 : Nat := 4983230072969 + 3 ^ 40 * 5547272 * 2
def baseEnd_5547272 : Nat := 949472285742641835496189

theorem tailTrace_5547272 : CollatzResearch.WordTrace tailWord_5547272 prefixEnd_5547272 949472285742641835496189 := by
  unfold tailWord_5547272
  simp only [CollatzResearch.WordTrace]
  refine ⟨101162815779594208738226035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134883754372792278317634713 101162815779594208738226035)
  ·
    refine ⟨151744223669391313107339053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101162815779594208738226035 151744223669391313107339053)
    ·
      refine ⟨56904083876021742415252145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151744223669391313107339053 56904083876021742415252145)
      ·
        refine ⟨42678062907016306811439109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56904083876021742415252145 42678062907016306811439109)
        ·
          refine ⟨8002136795065557527144833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42678062907016306811439109 8002136795065557527144833)
          ·
            refine ⟨6001602596299168145358625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8002136795065557527144833 6001602596299168145358625)
            ·
              refine ⟨4501201947224376109018969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001602596299168145358625 4501201947224376109018969)
              ·
                refine ⟨3375901460418282081764227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501201947224376109018969 3375901460418282081764227)
                ·
                  refine ⟨5063852190627423122646341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375901460418282081764227 5063852190627423122646341)
                  ·
                    refine ⟨949472285742641835496189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5063852190627423122646341 949472285742641835496189)
                    ·
                      rfl

theorem cell23_5547272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_5547272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547272 prefixEnd_5547272 := by exact prefixLift 5547272
  have htrace : WordTrace (prefixWord ++ tailWord_5547272) baseStart_5547272 baseEnd_5547272 := by
    simpa [prefixWord, tailWord_5547272, baseEnd_5547272] using wordTrace_append hprefix tailTrace_5547272
  have hstable : (prefixWord ++ tailWord_5547272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547272).length < 2 ^ (prefixWord ++ tailWord_5547272).sum := by decide
  have hdescent : baseEnd_5547272 < baseStart_5547272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547301 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_5547301 : Nat := 118140960795 + 5547301 * 2 ^ 59
def prefixEnd_5547301 : Nat := 4983230072969 + 3 ^ 40 * 5547301 * 2
def baseEnd_5547301 : Nat := 2848431748166905893025933

theorem tailTrace_5547301 : CollatzResearch.WordTrace tailWord_5547301 prefixEnd_5547301 2848431748166905893025933 := by
  unfold tailWord_5547301
  simp only [CollatzResearch.WordTrace]
  refine ⟨202326689276083355429257757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134884459517388903619505171 202326689276083355429257757)
  ·
    refine ⟨75872508478531258285971659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202326689276083355429257757 75872508478531258285971659)
    ·
      refine ⟨113808762717796887428957489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75872508478531258285971659 113808762717796887428957489)
      ·
        refine ⟨85356572038347665571718117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113808762717796887428957489 85356572038347665571718117)
        ·
          refine ⟨16004357257190187294697147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85356572038347665571718117 16004357257190187294697147)
          ·
            refine ⟨24006535885785280942045721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16004357257190187294697147 24006535885785280942045721)
            ·
              refine ⟨18004901914338960706534291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24006535885785280942045721 18004901914338960706534291)
              ·
                refine ⟨27007352871508441059801437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18004901914338960706534291 27007352871508441059801437)
                ·
                  refine ⟨10127757326815665397425539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27007352871508441059801437 10127757326815665397425539)
                  ·
                    refine ⟨15191635990223498096138309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10127757326815665397425539 15191635990223498096138309)
                    ·
                      refine ⟨2848431748166905893025933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15191635990223498096138309 2848431748166905893025933)
                      ·
                        rfl

theorem cell23_5547301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_5547301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547301 prefixEnd_5547301 := by exact prefixLift 5547301
  have htrace : WordTrace (prefixWord ++ tailWord_5547301) baseStart_5547301 baseEnd_5547301 := by
    simpa [prefixWord, tailWord_5547301, baseEnd_5547301] using wordTrace_append hprefix tailTrace_5547301
  have hstable : (prefixWord ++ tailWord_5547301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547301).length < 2 ^ (prefixWord ++ tailWord_5547301).sum := by decide
  have hdescent : baseEnd_5547301 < baseStart_5547301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547324 : List Nat := [2, 2, 2, 2, 1, 4, 10]
def baseStart_5547324 : Nat := 118140960795 + 5547324 * 2 ^ 59
def prefixEnd_5547324 : Nat := 4983230072969 + 3 ^ 40 * 5547324 * 2
def baseEnd_5547324 : Nat := 35165969854592090160967

theorem tailTrace_5547324 : CollatzResearch.WordTrace tailWord_5547324 prefixEnd_5547324 35165969854592090160967 := by
  unfold tailWord_5547324
  simp only [CollatzResearch.WordTrace]
  refine ⟨101163764077500015178672513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134885018770000020238230017 101163764077500015178672513)
  ·
    refine ⟨75872823058125011384004385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101163764077500015178672513 75872823058125011384004385)
    ·
      refine ⟨56904617293593758538003289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75872823058125011384004385 56904617293593758538003289)
      ·
        refine ⟨42678462970195318903502467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56904617293593758538003289 42678462970195318903502467)
        ·
          refine ⟨64017694455292978355253701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42678462970195318903502467 64017694455292978355253701)
          ·
            refine ⟨12003317710367433441610069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64017694455292978355253701 12003317710367433441610069)
            ·
              refine ⟨35165969854592090160967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12003317710367433441610069 35165969854592090160967)
              ·
                rfl

theorem cell23_5547324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 10].length) (baseStart_5547324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547324 prefixEnd_5547324 := by exact prefixLift 5547324
  have htrace : WordTrace (prefixWord ++ tailWord_5547324) baseStart_5547324 baseEnd_5547324 := by
    simpa [prefixWord, tailWord_5547324, baseEnd_5547324] using wordTrace_append hprefix tailTrace_5547324
  have hstable : (prefixWord ++ tailWord_5547324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547324).length < 2 ^ (prefixWord ++ tailWord_5547324).sum := by decide
  have hdescent : baseEnd_5547324 < baseStart_5547324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547335 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_5547335 : Nat := 118140960795 + 5547335 * 2 ^ 59
def prefixEnd_5547335 : Nat := 4983230072969 + 3 ^ 40 * 5547335 * 2
def baseEnd_5547335 : Nat := 2848449206509158760000777

theorem tailTrace_5547335 : CollatzResearch.WordTrace tailWord_5547335 prefixEnd_5547335 2848449206509158760000777 := by
  unfold tailWord_5547335
  simp only [CollatzResearch.WordTrace]
  refine ⟨202327929357960179235995459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134885286238640119490663639 202327929357960179235995459)
  ·
    refine ⟨303491894036940268853993189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202327929357960179235995459 303491894036940268853993189)
    ·
      refine ⟨56904730131926300410123723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303491894036940268853993189 56904730131926300410123723)
      ·
        refine ⟨85357095197889450615185585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56904730131926300410123723 85357095197889450615185585)
        ·
          refine ⟨64017821398417087961389189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85357095197889450615185585 64017821398417087961389189)
          ·
            refine ⟨12003341512203203992760473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64017821398417087961389189 12003341512203203992760473)
            ·
              refine ⟨9002506134152402994570355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12003341512203203992760473 9002506134152402994570355)
              ·
                refine ⟨13503759201228604491855533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9002506134152402994570355 13503759201228604491855533)
                ·
                  refine ⟨5063909700460726684445825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13503759201228604491855533 5063909700460726684445825)
                  ·
                    refine ⟨3797932275345545013334369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063909700460726684445825 3797932275345545013334369)
                    ·
                      refine ⟨2848449206509158760000777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797932275345545013334369 2848449206509158760000777)
                      ·
                        rfl

theorem cell23_5547335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_5547335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547335 prefixEnd_5547335 := by exact prefixLift 5547335
  have htrace : WordTrace (prefixWord ++ tailWord_5547335) baseStart_5547335 baseEnd_5547335 := by
    simpa [prefixWord, tailWord_5547335, baseEnd_5547335] using wordTrace_append hprefix tailTrace_5547335
  have hstable : (prefixWord ++ tailWord_5547335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547335).length < 2 ^ (prefixWord ++ tailWord_5547335).sum := by decide
  have hdescent : baseEnd_5547335 < baseStart_5547335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547354 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_5547354 : Nat := 118140960795 + 5547354 * 2 ^ 59
def prefixEnd_5547354 : Nat := 4983230072969 + 3 ^ 40 * 5547354 * 2
def baseEnd_5547354 : Nat := 949486320880531395221063

theorem tailTrace_5547354 : CollatzResearch.WordTrace tailWord_5547354 prefixEnd_5547354 949486320880531395221063 := by
  unfold tailWord_5547354
  simp only [CollatzResearch.WordTrace]
  refine ⟨50582155586222836370234279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134885748229927563653958077 50582155586222836370234279)
  ·
    refine ⟨75873233379334254555351419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50582155586222836370234279 75873233379334254555351419)
    ·
      refine ⟨113809850069001381833027129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75873233379334254555351419 113809850069001381833027129)
      ·
        refine ⟨85357387551751036374770347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113809850069001381833027129 85357387551751036374770347)
        ·
          refine ⟨128036081327626554562155521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85357387551751036374770347 128036081327626554562155521)
          ·
            refine ⟨96027060995719915921616641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128036081327626554562155521 96027060995719915921616641)
            ·
              refine ⟨72020295746789936941212481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96027060995719915921616641 72020295746789936941212481)
              ·
                refine ⟨54015221810092452705909361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72020295746789936941212481 54015221810092452705909361)
                ·
                  refine ⟨40511416357569339529432021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54015221810092452705909361 40511416357569339529432021)
                  ·
                    refine ⟨949486320880531395221063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40511416357569339529432021 949486320880531395221063)
                    ·
                      rfl

theorem cell23_5547354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_5547354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547354 prefixEnd_5547354 := by exact prefixLift 5547354
  have htrace : WordTrace (prefixWord ++ tailWord_5547354) baseStart_5547354 baseEnd_5547354 := by
    simpa [prefixWord, tailWord_5547354, baseEnd_5547354] using wordTrace_append hprefix tailTrace_5547354
  have hstable : (prefixWord ++ tailWord_5547354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547354).length < 2 ^ (prefixWord ++ tailWord_5547354).sum := by decide
  have hdescent : baseEnd_5547354 < baseStart_5547354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547361 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_5547361 : Nat := 118140960795 + 5547361 * 2 ^ 59
def prefixEnd_5547361 : Nat := 4983230072969 + 3 ^ 40 * 5547361 * 2
def baseEnd_5547361 : Nat := 2848462557006175658275657

theorem tailTrace_5547361 : CollatzResearch.WordTrace tailWord_5547361 prefixEnd_5547361 2848462557006175658275657 := by
  unfold tailWord_5547361
  simp only [CollatzResearch.WordTrace]
  refine ⟨202328877655865985676441937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134885918437243990450961291 202328877655865985676441937)
  ·
    refine ⟨151746658241899489257331453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202328877655865985676441937 151746658241899489257331453)
    ·
      refine ⟨56904996840712308471499295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151746658241899489257331453 56904996840712308471499295)
      ·
        refine ⟨85357495261068462707248943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56904996840712308471499295 85357495261068462707248943)
        ·
          refine ⟨128036242891602694060873415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85357495261068462707248943 128036242891602694060873415)
          ·
            refine ⟨192054364337404041091310123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128036242891602694060873415 192054364337404041091310123)
            ·
              refine ⟨288081546506106061636965185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192054364337404041091310123 288081546506106061636965185)
              ·
                refine ⟨216061159879579546227723889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288081546506106061636965185 216061159879579546227723889)
                ·
                  refine ⟨162045869909684659670792917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216061159879579546227723889 162045869909684659670792917)
                  ·
                    refine ⟨3797950076008234211034209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162045869909684659670792917 3797950076008234211034209)
                    ·
                      refine ⟨2848462557006175658275657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797950076008234211034209 2848462557006175658275657)
                      ·
                        rfl

theorem cell23_5547361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_5547361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547361 prefixEnd_5547361 := by exact prefixLift 5547361
  have htrace : WordTrace (prefixWord ++ tailWord_5547361) baseStart_5547361 baseEnd_5547361 := by
    simpa [prefixWord, tailWord_5547361, baseEnd_5547361] using wordTrace_append hprefix tailTrace_5547361
  have hstable : (prefixWord ++ tailWord_5547361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547361).length < 2 ^ (prefixWord ++ tailWord_5547361).sum := by decide
  have hdescent : baseEnd_5547361 < baseStart_5547361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547391 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 8, 2]
def baseStart_5547391 : Nat := 118140960795 + 5547391 * 2 ^ 59
def prefixEnd_5547391 : Nat := 4983230072969 + 3 ^ 40 * 5547391 * 2
def baseEnd_5547391 : Nat := 2848477961425810540900519

theorem tailTrace_5547391 : CollatzResearch.WordTrace tailWord_5547391 prefixEnd_5547391 2848477961425810540900519 := by
  unfold tailWord_5547391
  simp only [CollatzResearch.WordTrace]
  refine ⟨202329971845757300800034027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134886647897171533866689351 202329971845757300800034027)
  ·
    refine ⟨303494957768635951200051041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202329971845757300800034027 303494957768635951200051041)
    ·
      refine ⟨227621218326476963400038281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303494957768635951200051041 227621218326476963400038281)
      ·
        refine ⟨170715913744857722550028711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227621218326476963400038281 170715913744857722550028711)
        ·
          refine ⟨256073870617286583825043067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170715913744857722550028711 256073870617286583825043067)
          ·
            refine ⟨384110805925929875737564601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256073870617286583825043067 384110805925929875737564601)
            ·
              refine ⟨288083104444447406803173451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384110805925929875737564601 288083104444447406803173451)
              ·
                refine ⟨432124656666671110204760177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288083104444447406803173451 432124656666671110204760177)
                ·
                  refine ⟨324093492500003332653570133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432124656666671110204760177 324093492500003332653570133)
                  ·
                    refine ⟨3797970615234414054534025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 324093492500003332653570133 3797970615234414054534025)
                    ·
                      refine ⟨2848477961425810540900519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797970615234414054534025 2848477961425810540900519)
                      ·
                        rfl

theorem cell23_5547391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_5547391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547391 prefixEnd_5547391 := by exact prefixLift 5547391
  have htrace : WordTrace (prefixWord ++ tailWord_5547391) baseStart_5547391 baseEnd_5547391 := by
    simpa [prefixWord, tailWord_5547391, baseEnd_5547391] using wordTrace_append hprefix tailTrace_5547391
  have hstable : (prefixWord ++ tailWord_5547391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547391).length < 2 ^ (prefixWord ++ tailWord_5547391).sum := by decide
  have hdescent : baseEnd_5547391 < baseStart_5547391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547412 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5547412 : Nat := 118140960795 + 5547412 * 2 ^ 59
def prefixEnd_5547412 : Nat := 4983230072969 + 3 ^ 40 * 5547412 * 2
def baseEnd_5547412 : Nat := 2848488744519554958737923

theorem tailTrace_5547412 : CollatzResearch.WordTrace tailWord_5547412 prefixEnd_5547412 2848488744519554958737923 := by
  unfold tailWord_5547412
  simp only [CollatzResearch.WordTrace]
  refine ⟨101165368889340610693274245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134887158519120814257698993 101165368889340610693274245)
  ·
    refine ⟨18968506666751364504988921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101165368889340610693274245 18968506666751364504988921)
    ·
      refine ⟨14226380000063523378741691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18968506666751364504988921 14226380000063523378741691)
      ·
        refine ⟨21339570000095285068112537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14226380000063523378741691 21339570000095285068112537)
        ·
          refine ⟨16004677500071463801084403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21339570000095285068112537 16004677500071463801084403)
          ·
            refine ⟨24007016250107195701626605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16004677500071463801084403 24007016250107195701626605)
            ·
              refine ⟨9002631093790198388109977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24007016250107195701626605 9002631093790198388109977)
              ·
                refine ⟨6751973320342648791082483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9002631093790198388109977 6751973320342648791082483)
                ·
                  refine ⟨10127959980513973186623725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6751973320342648791082483 10127959980513973186623725)
                  ·
                    refine ⟨3797984992692739944983897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10127959980513973186623725 3797984992692739944983897)
                    ·
                      refine ⟨2848488744519554958737923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3797984992692739944983897 2848488744519554958737923)
                      ·
                        rfl

theorem cell23_5547412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5547412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547412 prefixEnd_5547412 := by exact prefixLift 5547412
  have htrace : WordTrace (prefixWord ++ tailWord_5547412) baseStart_5547412 baseEnd_5547412 := by
    simpa [prefixWord, tailWord_5547412, baseEnd_5547412] using wordTrace_append hprefix tailTrace_5547412
  have hstable : (prefixWord ++ tailWord_5547412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547412).length < 2 ^ (prefixWord ++ tailWord_5547412).sum := by decide
  have hdescent : baseEnd_5547412 < baseStart_5547412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547602 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_5547602 : Nat := 118140960795 + 5547602 * 2 ^ 59
def prefixEnd_5547602 : Nat := 4983230072969 + 3 ^ 40 * 5547602 * 2
def baseEnd_5547602 : Nat := 949528768614636405120683

theorem tailTrace_5547602 : CollatzResearch.WordTrace tailWord_5547602 prefixEnd_5547602 949528768614636405120683 := by
  unfold tailWord_5547602
  simp only [CollatzResearch.WordTrace]
  refine ⟨50584416911998220958991265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134891778431995255890643373 50584416911998220958991265)
  ·
    refine ⟨37938312683998665719243449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50584416911998220958991265 37938312683998665719243449)
    ·
      refine ⟨28453734512998999289432587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37938312683998665719243449 28453734512998999289432587)
      ·
        refine ⟨42680601769498498934148881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28453734512998999289432587 42680601769498498934148881)
        ·
          refine ⟨32010451327123874200611661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42680601769498498934148881 32010451327123874200611661)
          ·
            refine ⟨12003919247671452825229373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32010451327123874200611661 12003919247671452825229373)
            ·
              refine ⟨4501469717876794809461015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12003919247671452825229373 4501469717876794809461015)
              ·
                refine ⟨6752204576815192214191523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501469717876794809461015 6752204576815192214191523)
                ·
                  refine ⟨10128306865222788321287285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6752204576815192214191523 10128306865222788321287285)
                  ·
                    refine ⟨949528768614636405120683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10128306865222788321287285 949528768614636405120683)
                    ·
                      rfl

theorem cell23_5547602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_5547602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547602 prefixEnd_5547602 := by exact prefixLift 5547602
  have htrace : WordTrace (prefixWord ++ tailWord_5547602) baseStart_5547602 baseEnd_5547602 := by
    simpa [prefixWord, tailWord_5547602, baseEnd_5547602] using wordTrace_append hprefix tailTrace_5547602
  have hstable : (prefixWord ++ tailWord_5547602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547602).length < 2 ^ (prefixWord ++ tailWord_5547602).sum := by decide
  have hdescent : baseEnd_5547602 < baseStart_5547602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547645 : List Nat := [1, 4, 1, 1, 4, 2, 3, 7]
def baseStart_5547645 : Nat := 118140960795 + 5547645 * 2 ^ 59
def prefixEnd_5547645 : Nat := 4983230072969 + 3 ^ 40 * 5547645 * 2
def baseEnd_5547645 : Nat := 105504014278224168412013

theorem tailTrace_5547645 : CollatzResearch.WordTrace tailWord_5547645 prefixEnd_5547645 105504014278224168412013 := by
  unfold tailWord_5547645
  simp only [CollatzResearch.WordTrace]
  refine ⟨202339235986837102179780389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134892823991224734786520259 202339235986837102179780389)
  ·
    refine ⟨37938606747531956658708823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202339235986837102179780389 37938606747531956658708823)
    ·
      refine ⟨56907910121297934988063235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37938606747531956658708823 56907910121297934988063235)
      ·
        refine ⟨85361865181946902482094853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56907910121297934988063235 85361865181946902482094853)
        ·
          refine ⟨16005349721615044215392785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85361865181946902482094853 16005349721615044215392785)
          ·
            refine ⟨12004012291211283161544589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16005349721615044215392785 12004012291211283161544589)
            ·
              refine ⟨4501504609204231185579221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12004012291211283161544589 4501504609204231185579221)
              ·
                refine ⟨105504014278224168412013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4501504609204231185579221 105504014278224168412013)
                ·
                  rfl

theorem cell23_5547645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 7].length) (baseStart_5547645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547645 prefixEnd_5547645 := by exact prefixLift 5547645
  have htrace : WordTrace (prefixWord ++ tailWord_5547645) baseStart_5547645 baseEnd_5547645 := by
    simpa [prefixWord, tailWord_5547645, baseEnd_5547645] using wordTrace_append hprefix tailTrace_5547645
  have hstable : (prefixWord ++ tailWord_5547645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547645).length < 2 ^ (prefixWord ++ tailWord_5547645).sum := by decide
  have hdescent : baseEnd_5547645 < baseStart_5547645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547655 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_5547655 : Nat := 118140960795 + 5547655 * 2 ^ 59
def prefixEnd_5547655 : Nat := 4983230072969 + 3 ^ 40 * 5547655 * 2
def baseEnd_5547655 : Nat := 2848613520318597507999305

theorem tailTrace_5547655 : CollatzResearch.WordTrace tailWord_5547655 prefixEnd_5547655 2848613520318597507999305 := by
  unfold tailWord_5547655
  simp only [CollatzResearch.WordTrace]
  refine ⟨202339600716800873887644419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134893067144533915925096279 202339600716800873887644419)
  ·
    refine ⟨303509401075201310831466629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202339600716800873887644419 303509401075201310831466629)
    ·
      refine ⟨56908012701600245780899993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303509401075201310831466629 56908012701600245780899993)
      ·
        refine ⟨42681009526200184335674995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56908012701600245780899993 42681009526200184335674995)
        ·
          refine ⟨64021514289300276503512493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42681009526200184335674995 64021514289300276503512493)
          ·
            refine ⟨24008067858487603688817185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64021514289300276503512493 24008067858487603688817185)
            ·
              refine ⟨18006050893865702766612889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24008067858487603688817185 18006050893865702766612889)
              ·
                refine ⟨13504538170399277074959667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18006050893865702766612889 13504538170399277074959667)
                ·
                  refine ⟨20256807255598915612439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13504538170399277074959667 20256807255598915612439501)
                  ·
                    refine ⟨7596302720849593354664813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20256807255598915612439501 7596302720849593354664813)
                    ·
                      refine ⟨2848613520318597507999305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7596302720849593354664813 2848613520318597507999305)
                      ·
                        rfl

theorem cell23_5547655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_5547655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547655 prefixEnd_5547655 := by exact prefixLift 5547655
  have htrace : WordTrace (prefixWord ++ tailWord_5547655) baseStart_5547655 baseEnd_5547655 := by
    simpa [prefixWord, tailWord_5547655, baseEnd_5547655] using wordTrace_append hprefix tailTrace_5547655
  have hstable : (prefixWord ++ tailWord_5547655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547655).length < 2 ^ (prefixWord ++ tailWord_5547655).sum := by decide
  have hdescent : baseEnd_5547655 < baseStart_5547655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547656 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5547656 : Nat := 118140960795 + 5547656 * 2 ^ 59
def prefixEnd_5547656 : Nat := 4983230072969 + 3 ^ 40 * 5547656 * 2
def baseEnd_5547656 : Nat := 2848614033799252004086801

theorem tailTrace_5547656 : CollatzResearch.WordTrace tailWord_5547656 prefixEnd_5547656 2848614033799252004086801 := by
  unfold tailWord_5547656
  simp only [CollatzResearch.WordTrace]
  refine ⟨101169818594898625529215411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134893091459864834038953881 101169818594898625529215411)
  ·
    refine ⟨151754727892347938293823117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101169818594898625529215411 151754727892347938293823117)
    ·
      refine ⟨56908022959630476860183669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151754727892347938293823117 56908022959630476860183669)
      ·
        refine ⟨5335127152465357205642219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56908022959630476860183669 5335127152465357205642219)
        ·
          refine ⟨8002690728698035808463329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335127152465357205642219 8002690728698035808463329)
          ·
            refine ⟨6002018046523526856347497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8002690728698035808463329 6002018046523526856347497)
            ·
              refine ⟨4501513534892645142260623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6002018046523526856347497 4501513534892645142260623)
              ·
                refine ⟨6752270302338967713390935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501513534892645142260623 6752270302338967713390935)
                ·
                  refine ⟨10128405453508451570086403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6752270302338967713390935 10128405453508451570086403)
                  ·
                    refine ⟨15192608180262677355129605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10128405453508451570086403 15192608180262677355129605)
                    ·
                      refine ⟨2848614033799252004086801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15192608180262677355129605 2848614033799252004086801)
                      ·
                        rfl

theorem cell23_5547656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5547656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547656 prefixEnd_5547656 := by exact prefixLift 5547656
  have htrace : WordTrace (prefixWord ++ tailWord_5547656) baseStart_5547656 baseEnd_5547656 := by
    simpa [prefixWord, tailWord_5547656, baseEnd_5547656] using wordTrace_append hprefix tailTrace_5547656
  have hstable : (prefixWord ++ tailWord_5547656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547656).length < 2 ^ (prefixWord ++ tailWord_5547656).sum := by decide
  have hdescent : baseEnd_5547656 < baseStart_5547656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547665 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 5, 3, 2]
def baseStart_5547665 : Nat := 118140960795 + 5547665 * 2 ^ 59
def prefixEnd_5547665 : Nat := 4983230072969 + 3 ^ 40 * 5547665 * 2
def baseEnd_5547665 : Nat := 2848618655125142468874259

theorem tailTrace_5547665 : CollatzResearch.WordTrace tailWord_5547665 prefixEnd_5547665 2848618655125142468874259 := by
  unfold tailWord_5547665
  simp only [CollatzResearch.WordTrace]
  refine ⟨202339965446764645595508449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134893310297843097063672299 202339965446764645595508449)
  ·
    refine ⟨151754974085073484196631337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202339965446764645595508449 151754974085073484196631337)
    ·
      refine ⟨113816230563805113147473503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151754974085073484196631337 113816230563805113147473503)
      ·
        refine ⟨170724345845707669721210255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113816230563805113147473503 170724345845707669721210255)
        ·
          refine ⟨256086518768561504581815383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170724345845707669721210255 256086518768561504581815383)
          ·
            refine ⟨384129778152842256872723075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256086518768561504581815383 384129778152842256872723075)
            ·
              refine ⟨576194667229263385309084613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384129778152842256872723075 576194667229263385309084613)
              ·
                refine ⟨108036500105486884745453365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576194667229263385309084613 108036500105486884745453365)
                ·
                  refine ⟨10128421884889395444886253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108036500105486884745453365 10128421884889395444886253)
                  ·
                    refine ⟨3798158206833523291832345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10128421884889395444886253 3798158206833523291832345)
                    ·
                      refine ⟨2848618655125142468874259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798158206833523291832345 2848618655125142468874259)
                      ·
                        rfl

theorem cell23_5547665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_5547665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547665 prefixEnd_5547665 := by exact prefixLift 5547665
  have htrace : WordTrace (prefixWord ++ tailWord_5547665) baseStart_5547665 baseEnd_5547665 := by
    simpa [prefixWord, tailWord_5547665, baseEnd_5547665] using wordTrace_append hprefix tailTrace_5547665
  have hstable : (prefixWord ++ tailWord_5547665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547665).length < 2 ^ (prefixWord ++ tailWord_5547665).sum := by decide
  have hdescent : baseEnd_5547665 < baseStart_5547665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547666 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_5547666 : Nat := 118140960795 + 5547666 * 2 ^ 59
def prefixEnd_5547666 : Nat := 4983230072969 + 3 ^ 40 * 5547666 * 2
def baseEnd_5547666 : Nat := 949539722868598988320585

theorem tailTrace_5547666 : CollatzResearch.WordTrace tailWord_5547666 prefixEnd_5547666 949539722868598988320585 := by
  unfold tailWord_5547666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50585000479940255691573713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134893334613174015177529901 50585000479940255691573713)
  ·
    refine ⟨37938750359955191768680285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50585000479940255691573713 37938750359955191768680285)
    ·
      refine ⟨14227031384983196913255107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37938750359955191768680285 14227031384983196913255107)
      ·
        refine ⟨21340547077474795369882661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14227031384983196913255107 21340547077474795369882661)
        ·
          refine ⟨4001352577026524131852999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21340547077474795369882661 4001352577026524131852999)
          ·
            refine ⟨6002028865539786197779499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4001352577026524131852999 6002028865539786197779499)
            ·
              refine ⟨9003043298309679296669249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6002028865539786197779499 9003043298309679296669249)
              ·
                refine ⟨6752282473732259472501937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9003043298309679296669249 6752282473732259472501937)
                ·
                  refine ⟨5064211855299194604376453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752282473732259472501937 5064211855299194604376453)
                  ·
                    refine ⟨949539722868598988320585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5064211855299194604376453 949539722868598988320585)
                    ·
                      rfl

theorem cell23_5547666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_5547666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547666 prefixEnd_5547666 := by exact prefixLift 5547666
  have htrace : WordTrace (prefixWord ++ tailWord_5547666) baseStart_5547666 baseEnd_5547666 := by
    simpa [prefixWord, tailWord_5547666, baseEnd_5547666] using wordTrace_append hprefix tailTrace_5547666
  have hstable : (prefixWord ++ tailWord_5547666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547666).length < 2 ^ (prefixWord ++ tailWord_5547666).sum := by decide
  have hdescent : baseEnd_5547666 < baseStart_5547666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547672 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_5547672 : Nat := 118140960795 + 5547672 * 2 ^ 59
def prefixEnd_5547672 : Nat := 4983230072969 + 3 ^ 40 * 5547672 * 2
def baseEnd_5547672 : Nat := 2848622249489723941486727

theorem tailTrace_5547672 : CollatzResearch.WordTrace tailWord_5547672 prefixEnd_5547672 2848622249489723941486727 := by
  unfold tailWord_5547672
  simp only [CollatzResearch.WordTrace]
  refine ⟨101170110378869642895506635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134893480505159523860675513 101170110378869642895506635)
  ·
    refine ⟨151755165568304464343259953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101170110378869642895506635 151755165568304464343259953)
    ·
      refine ⟨113816374176228348257444965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151755165568304464343259953 113816374176228348257444965)
      ·
        refine ⟨21340570158042815298270931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113816374176228348257444965 21340570158042815298270931)
        ·
          refine ⟨32010855237064222947406397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21340570158042815298270931 32010855237064222947406397)
          ·
            refine ⟨12004070713899083605277399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32010855237064222947406397 12004070713899083605277399)
            ·
              refine ⟨18006106070848625407916099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12004070713899083605277399 18006106070848625407916099)
              ·
                refine ⟨27009159106272938111874149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18006106070848625407916099 27009159106272938111874149)
                ·
                  refine ⟨5064217332426175895976403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27009159106272938111874149 5064217332426175895976403)
                  ·
                    refine ⟨7596325998639263843964605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5064217332426175895976403 7596325998639263843964605)
                    ·
                      refine ⟨2848622249489723941486727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7596325998639263843964605 2848622249489723941486727)
                      ·
                        rfl

theorem cell23_5547672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_5547672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547672 prefixEnd_5547672 := by exact prefixLift 5547672
  have htrace : WordTrace (prefixWord ++ tailWord_5547672) baseStart_5547672 baseEnd_5547672 := by
    simpa [prefixWord, tailWord_5547672, baseEnd_5547672] using wordTrace_append hprefix tailTrace_5547672
  have hstable : (prefixWord ++ tailWord_5547672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547672).length < 2 ^ (prefixWord ++ tailWord_5547672).sum := by decide
  have hdescent : baseEnd_5547672 < baseStart_5547672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547702 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5547702 : Nat := 118140960795 + 5547702 * 2 ^ 59
def prefixEnd_5547702 : Nat := 4983230072969 + 3 ^ 40 * 5547702 * 2
def baseEnd_5547702 : Nat := 2848637653909358824111589

theorem tailTrace_5547702 : CollatzResearch.WordTrace tailWord_5547702 prefixEnd_5547702 2848637653909358824111589 := by
  unfold tailWord_5547702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12646332184226912557162835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134894209965087067276403573 12646332184226912557162835)
  ·
    refine ⟨18969498276340368835744253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12646332184226912557162835 18969498276340368835744253)
    ·
      refine ⟨7113561853627638313404095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18969498276340368835744253 7113561853627638313404095)
      ·
        refine ⟨10670342780441457470106143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113561853627638313404095 10670342780441457470106143)
        ·
          refine ⟨16005514170662186205159215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670342780441457470106143 16005514170662186205159215)
          ·
            refine ⟨24008271255993279307738823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16005514170662186205159215 24008271255993279307738823)
            ·
              refine ⟨36012406883989918961608235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24008271255993279307738823 36012406883989918961608235)
              ·
                refine ⟨54018610325984878442412353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36012406883989918961608235 54018610325984878442412353)
                ·
                  refine ⟨40513957744488658831809265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54018610325984878442412353 40513957744488658831809265)
                  ·
                    refine ⟨30385468308366494123856949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40513957744488658831809265 30385468308366494123856949)
                    ·
                      refine ⟨2848637653909358824111589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30385468308366494123856949 2848637653909358824111589)
                      ·
                        rfl

theorem cell23_5547702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5547702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547702 prefixEnd_5547702 := by exact prefixLift 5547702
  have htrace : WordTrace (prefixWord ++ tailWord_5547702) baseStart_5547702 baseEnd_5547702 := by
    simpa [prefixWord, tailWord_5547702, baseEnd_5547702] using wordTrace_append hprefix tailTrace_5547702
  have hstable : (prefixWord ++ tailWord_5547702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547702).length < 2 ^ (prefixWord ++ tailWord_5547702).sum := by decide
  have hdescent : baseEnd_5547702 < baseStart_5547702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547712 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 6, 2, 2]
def baseStart_5547712 : Nat := 118140960795 + 5547712 * 2 ^ 59
def prefixEnd_5547712 : Nat := 4983230072969 + 3 ^ 40 * 5547712 * 2
def baseEnd_5547712 : Nat := 2848642788715903784986543

theorem tailTrace_5547712 : CollatzResearch.WordTrace tailWord_5547712 prefixEnd_5547712 2848642788715903784986543 := by
  unfold tailWord_5547712
  simp only [CollatzResearch.WordTrace]
  refine ⟨101170839838797186311234695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134894453118396248414979593 101170839838797186311234695)
  ·
    refine ⟨151756259758195779466852043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101170839838797186311234695 151756259758195779466852043)
    ·
      refine ⟨227634389637293669200278065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151756259758195779466852043 227634389637293669200278065)
      ·
        refine ⟨170725792227970251900208549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227634389637293669200278065 170725792227970251900208549)
        ·
          refine ⟨32011086042744422231289103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170725792227970251900208549 32011086042744422231289103)
          ·
            refine ⟨48016629064116633346933655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32011086042744422231289103 48016629064116633346933655)
            ·
              refine ⟨72024943596174950020400483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48016629064116633346933655 72024943596174950020400483)
              ·
                refine ⟨108037415394262425030600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72024943596174950020400483 108037415394262425030600725)
                ·
                  refine ⟨5064253846606051173309409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108037415394262425030600725 5064253846606051173309409)
                  ·
                    refine ⟨3798190384954538379982057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5064253846606051173309409 3798190384954538379982057)
                    ·
                      refine ⟨2848642788715903784986543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798190384954538379982057 2848642788715903784986543)
                      ·
                        rfl

theorem cell23_5547712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_5547712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547712 prefixEnd_5547712 := by exact prefixLift 5547712
  have htrace : WordTrace (prefixWord ++ tailWord_5547712) baseStart_5547712 baseEnd_5547712 := by
    simpa [prefixWord, tailWord_5547712, baseEnd_5547712] using wordTrace_append hprefix tailTrace_5547712
  have hstable : (prefixWord ++ tailWord_5547712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547712).length < 2 ^ (prefixWord ++ tailWord_5547712).sum := by decide
  have hdescent : baseEnd_5547712 < baseStart_5547712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547740 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5547740 : Nat := 118140960795 + 5547740 * 2 ^ 59
def prefixEnd_5547740 : Nat := 4983230072969 + 3 ^ 40 * 5547740 * 2
def baseEnd_5547740 : Nat := 2848657166174229675436415

theorem tailTrace_5547740 : CollatzResearch.WordTrace tailWord_5547740 prefixEnd_5547740 2848657166174229675436415 := by
  unfold tailWord_5547740
  simp only [CollatzResearch.WordTrace]
  refine ⟨101171350460746466702244337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134895133947661955602992449 101171350460746466702244337)
  ·
    refine ⟨75878512845559850026683253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101171350460746466702244337 75878512845559850026683253)
    ·
      refine ⟨7113610579271235940001555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75878512845559850026683253 7113610579271235940001555)
      ·
        refine ⟨10670415868906853910002333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113610579271235940001555 10670415868906853910002333)
        ·
          refine ⟨4001405950840070216250875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10670415868906853910002333 4001405950840070216250875)
          ·
            refine ⟨6002108926260105324376313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4001405950840070216250875 6002108926260105324376313)
            ·
              refine ⟨4501581694695078993282235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6002108926260105324376313 4501581694695078993282235)
              ·
                refine ⟨6752372542042618489923353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501581694695078993282235 6752372542042618489923353)
                ·
                  refine ⟨5064279406531963867442515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752372542042618489923353 5064279406531963867442515)
                  ·
                    refine ⟨7596419109797945801163773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5064279406531963867442515 7596419109797945801163773)
                    ·
                      refine ⟨2848657166174229675436415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7596419109797945801163773 2848657166174229675436415)
                      ·
                        rfl

theorem cell23_5547740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5547740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547740 prefixEnd_5547740 := by exact prefixLift 5547740
  have htrace : WordTrace (prefixWord ++ tailWord_5547740) baseStart_5547740 baseEnd_5547740 := by
    simpa [prefixWord, tailWord_5547740, baseEnd_5547740] using wordTrace_append hprefix tailTrace_5547740
  have hstable : (prefixWord ++ tailWord_5547740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547740).length < 2 ^ (prefixWord ++ tailWord_5547740).sum := by decide
  have hdescent : baseEnd_5547740 < baseStart_5547740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547802 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2]
def baseStart_5547802 : Nat := 118140960795 + 5547802 * 2 ^ 59
def prefixEnd_5547802 : Nat := 4983230072969 + 3 ^ 40 * 5547802 * 2
def baseEnd_5547802 : Nat := 2848689001974808432861129

theorem tailTrace_5547802 : CollatzResearch.WordTrace tailWord_5547802 prefixEnd_5547802 2848689001974808432861129 := by
  unfold tailWord_5547802
  simp only [CollatzResearch.WordTrace]
  refine ⟨50586240561817079498311415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134896641498178878662163773 50586240561817079498311415)
  ·
    refine ⟨75879360842725619247467123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50586240561817079498311415 75879360842725619247467123)
    ·
      refine ⟨113819041264088428871200685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75879360842725619247467123 113819041264088428871200685)
      ·
        refine ⟨42682140474033160826700257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113819041264088428871200685 42682140474033160826700257)
        ·
          refine ⟨32011605355524870620025193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42682140474033160826700257 32011605355524870620025193)
          ·
            refine ⟨24008704016643652965018895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32011605355524870620025193 24008704016643652965018895)
            ·
              refine ⟨36013056024965479447528343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24008704016643652965018895 36013056024965479447528343)
              ·
                refine ⟨54019584037448219171292515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36013056024965479447528343 54019584037448219171292515)
                ·
                  refine ⟨81029376056172328756938773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54019584037448219171292515 81029376056172328756938773)
                  ·
                    refine ⟨3798252002633077910481505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81029376056172328756938773 3798252002633077910481505)
                    ·
                      refine ⟨2848689001974808432861129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798252002633077910481505 2848689001974808432861129)
                      ·
                        rfl

theorem cell23_5547802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_5547802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547802 prefixEnd_5547802 := by exact prefixLift 5547802
  have htrace : WordTrace (prefixWord ++ tailWord_5547802) baseStart_5547802 baseEnd_5547802 := by
    simpa [prefixWord, tailWord_5547802, baseEnd_5547802] using wordTrace_append hprefix tailTrace_5547802
  have hstable : (prefixWord ++ tailWord_5547802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547802).length < 2 ^ (prefixWord ++ tailWord_5547802).sum := by decide
  have hdescent : baseEnd_5547802 < baseStart_5547802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547812 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_5547812 : Nat := 118140960795 + 5547812 * 2 ^ 59
def prefixEnd_5547812 : Nat := 4983230072969 + 3 ^ 40 * 5547812 * 2
def baseEnd_5547812 : Nat := 949564712260451131245361

theorem tailTrace_5547812 : CollatzResearch.WordTrace tailWord_5547812 prefixEnd_5547812 949564712260451131245361 := by
  unfold tailWord_5547812
  simp only [CollatzResearch.WordTrace]
  refine ⟨101172663488616044850554845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134896884651488059800739793 101172663488616044850554845)
  ·
    refine ⟨37939748808231016818958067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101172663488616044850554845 37939748808231016818958067)
    ·
      refine ⟨56909623212346525228437101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37939748808231016818958067 56909623212346525228437101)
      ·
        refine ⟨21341108704629946960663913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56909623212346525228437101 21341108704629946960663913)
        ·
          refine ⟨16005831528472460220497935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21341108704629946960663913 16005831528472460220497935)
          ·
            refine ⟨24008747292708690330746903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16005831528472460220497935 24008747292708690330746903)
            ·
              refine ⟨36013120939063035496120355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24008747292708690330746903 36013120939063035496120355)
              ·
                refine ⟨54019681408594553244180533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36013120939063035496120355 54019681408594553244180533)
                ·
                  refine ⟨5064345132055739366641925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54019681408594553244180533 5064345132055739366641925)
                  ·
                    refine ⟨949564712260451131245361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5064345132055739366641925 949564712260451131245361)
                    ·
                      rfl

theorem cell23_5547812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_5547812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547812 prefixEnd_5547812 := by exact prefixLift 5547812
  have htrace : WordTrace (prefixWord ++ tailWord_5547812) baseStart_5547812 baseEnd_5547812 := by
    simpa [prefixWord, tailWord_5547812, baseEnd_5547812] using wordTrace_append hprefix tailTrace_5547812
  have hstable : (prefixWord ++ tailWord_5547812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547812).length < 2 ^ (prefixWord ++ tailWord_5547812).sum := by decide
  have hdescent : baseEnd_5547812 < baseStart_5547812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547846 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_5547846 : Nat := 118140960795 + 5547846 * 2 ^ 59
def prefixEnd_5547846 : Nat := 4983230072969 + 3 ^ 40 * 5547846 * 2
def baseEnd_5547846 : Nat := 949570531707868753570309

theorem tailTrace_5547846 : CollatzResearch.WordTrace tailWord_5547846 prefixEnd_5547846 949570531707868753570309 := by
  unfold tailWord_5547846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323330220597153547120231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134897711372739275671898261 6323330220597153547120231)
  ·
    refine ⟨9484995330895730320680347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323330220597153547120231 9484995330895730320680347)
    ·
      refine ⟨14227492996343595481020521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9484995330895730320680347 14227492996343595481020521)
      ·
        refine ⟨10670619747257696610765391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14227492996343595481020521 10670619747257696610765391)
        ·
          refine ⟨16005929620886544916148087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670619747257696610765391 16005929620886544916148087)
          ·
            refine ⟨24008894431329817374222131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16005929620886544916148087 24008894431329817374222131)
            ·
              refine ⟨36013341646994726061333197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24008894431329817374222131 36013341646994726061333197)
              ·
                refine ⟨13505003117623022272999949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36013341646994726061333197 13505003117623022272999949)
                ·
                  refine ⟨5064376169108633352374981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13505003117623022272999949 5064376169108633352374981)
                  ·
                    refine ⟨949570531707868753570309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5064376169108633352374981 949570531707868753570309)
                    ·
                      rfl

theorem cell23_5547846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_5547846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547846 prefixEnd_5547846 := by exact prefixLift 5547846
  have htrace : WordTrace (prefixWord ++ tailWord_5547846) baseStart_5547846 baseEnd_5547846 := by
    simpa [prefixWord, tailWord_5547846, baseEnd_5547846] using wordTrace_append hprefix tailTrace_5547846
  have hstable : (prefixWord ++ tailWord_5547846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547846).length < 2 ^ (prefixWord ++ tailWord_5547846).sum := by decide
  have hdescent : baseEnd_5547846 < baseStart_5547846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547872 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 1, 5]
def baseStart_5547872 : Nat := 118140960795 + 5547872 * 2 ^ 59
def prefixEnd_5547872 : Nat := 4983230072969 + 3 ^ 40 * 5547872 * 2
def baseEnd_5547872 : Nat := 949574981873541052995269

theorem tailTrace_5547872 : CollatzResearch.WordTrace tailWord_5547872 prefixEnd_5547872 949574981873541052995269 := by
  unfold tailWord_5547872
  simp only [CollatzResearch.WordTrace]
  refine ⟨101173757678507359974146935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134898343571343146632195913 101173757678507359974146935)
  ·
    refine ⟨151760636517761039961220403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101173757678507359974146935 151760636517761039961220403)
    ·
      refine ⟨227640954776641559941830605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151760636517761039961220403 227640954776641559941830605)
      ·
        refine ⟨85365358041240584978186477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227640954776641559941830605 85365358041240584978186477)
        ·
          refine ⟨32012009265465219366819929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85365358041240584978186477 32012009265465219366819929)
          ·
            refine ⟨24009006949098914525114947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32012009265465219366819929 24009006949098914525114947)
            ·
              refine ⟨36013510423648371787672421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24009006949098914525114947 36013510423648371787672421)
              ·
                refine ⟨6752533204434069710188579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36013510423648371787672421 6752533204434069710188579)
                ·
                  refine ⟨10128799806651104565282869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6752533204434069710188579 10128799806651104565282869)
                  ·
                    refine ⟨949574981873541052995269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10128799806651104565282869 949574981873541052995269)
                    ·
                      rfl

theorem cell23_5547872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_5547872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547872 prefixEnd_5547872 := by exact prefixLift 5547872
  have htrace : WordTrace (prefixWord ++ tailWord_5547872) baseStart_5547872 baseEnd_5547872 := by
    simpa [prefixWord, tailWord_5547872, baseEnd_5547872] using wordTrace_append hprefix tailTrace_5547872
  have hstable : (prefixWord ++ tailWord_5547872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547872).length < 2 ^ (prefixWord ++ tailWord_5547872).sum := by decide
  have hdescent : baseEnd_5547872 < baseStart_5547872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547879 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_5547879 : Nat := 118140960795 + 5547879 * 2 ^ 59
def prefixEnd_5547879 : Nat := 4983230072969 + 3 ^ 40 * 5547879 * 2
def baseEnd_5547879 : Nat := 2848728539985204631598275

theorem tailTrace_5547879 : CollatzResearch.WordTrace tailWord_5547879 prefixEnd_5547879 2848728539985204631598275 := by
  unfold tailWord_5547879
  simp only [CollatzResearch.WordTrace]
  refine ⟨202347770667989360143798691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134898513778659573429199127 202347770667989360143798691)
  ·
    refine ⟨303521656001984040215698037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202347770667989360143798691 303521656001984040215698037)
    ·
      refine ⟨28455155250186003770221691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303521656001984040215698037 28455155250186003770221691)
      ·
        refine ⟨42682732875279005655332537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28455155250186003770221691 42682732875279005655332537)
        ·
          refine ⟨32012049656459254241499403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42682732875279005655332537 32012049656459254241499403)
          ·
            refine ⟨48018074484688881362249105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32012049656459254241499403 48018074484688881362249105)
            ·
              refine ⟨36013555863516661021686829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48018074484688881362249105 36013555863516661021686829)
              ·
                refine ⟨13505083448818747883132561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36013555863516661021686829 13505083448818747883132561)
                ·
                  refine ⟨10128812586614060912349421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13505083448818747883132561 10128812586614060912349421)
                  ·
                    refine ⟨3798304719980272842131033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10128812586614060912349421 3798304719980272842131033)
                    ·
                      refine ⟨2848728539985204631598275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798304719980272842131033 2848728539985204631598275)
                      ·
                        rfl

theorem cell23_5547879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_5547879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547879 prefixEnd_5547879 := by exact prefixLift 5547879
  have htrace : WordTrace (prefixWord ++ tailWord_5547879) baseStart_5547879 baseEnd_5547879 := by
    simpa [prefixWord, tailWord_5547879, baseEnd_5547879] using wordTrace_append hprefix tailTrace_5547879
  have hstable : (prefixWord ++ tailWord_5547879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547879).length < 2 ^ (prefixWord ++ tailWord_5547879).sum := by decide
  have hdescent : baseEnd_5547879 < baseStart_5547879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547929 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 3]
def baseStart_5547929 : Nat := 118140960795 + 5547929 * 2 ^ 59
def prefixEnd_5547929 : Nat := 4983230072969 + 3 ^ 40 * 5547929 * 2
def baseEnd_5547929 : Nat := 2848754214017929435973045

theorem tailTrace_5547929 : CollatzResearch.WordTrace tailWord_5547929 prefixEnd_5547929 2848754214017929435973045 := by
  unfold tailWord_5547929
  simp only [CollatzResearch.WordTrace]
  refine ⟨202349594317808218683118841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134899729545205479122079227 202349594317808218683118841)
  ·
    refine ⟨151762195738356164012339131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202349594317808218683118841 151762195738356164012339131)
    ·
      refine ⟨227643293607534246018508697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151762195738356164012339131 227643293607534246018508697)
      ·
        refine ⟨170732470205650684513881523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227643293607534246018508697 170732470205650684513881523)
        ·
          refine ⟨256098705308476026770822285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170732470205650684513881523 256098705308476026770822285)
          ·
            refine ⟨96037014490678510039058357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256098705308476026770822285 96037014490678510039058357)
            ·
              refine ⟨9003470108501110316161721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96037014490678510039058357 9003470108501110316161721)
              ·
                refine ⟨6752602581375832737121291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9003470108501110316161721 6752602581375832737121291)
                ·
                  refine ⟨10128903872063749105681937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6752602581375832737121291 10128903872063749105681937)
                  ·
                    refine ⟨7596677904047811829261453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10128903872063749105681937 7596677904047811829261453)
                    ·
                      refine ⟨2848754214017929435973045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7596677904047811829261453 2848754214017929435973045)
                      ·
                        rfl

theorem cell23_5547929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_5547929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547929 prefixEnd_5547929 := by exact prefixLift 5547929
  have htrace : WordTrace (prefixWord ++ tailWord_5547929) baseStart_5547929 baseEnd_5547929 := by
    simpa [prefixWord, tailWord_5547929, baseEnd_5547929] using wordTrace_append hprefix tailTrace_5547929
  have hstable : (prefixWord ++ tailWord_5547929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547929).length < 2 ^ (prefixWord ++ tailWord_5547929).sum := by decide
  have hdescent : baseEnd_5547929 < baseStart_5547929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547932 : List Nat := [2, 2, 3, 3, 1, 1, 2, 9]
def baseStart_5547932 : Nat := 118140960795 + 5547932 * 2 ^ 59
def prefixEnd_5547932 : Nat := 4983230072969 + 3 ^ 40 * 5547932 * 2
def baseEnd_5547932 : Nat := 105509472387403441638353

theorem tailTrace_5547932 : CollatzResearch.WordTrace tailWord_5547932 prefixEnd_5547932 105509472387403441638353 := by
  unfold tailWord_5547932
  simp only [CollatzResearch.WordTrace]
  refine ⟨101174851868398675097739025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134899802491198233463652033 101174851868398675097739025)
  ·
    refine ⟨75881138901299006323304269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101174851868398675097739025 75881138901299006323304269)
    ·
      refine ⟨28455427087987127371239101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75881138901299006323304269 28455427087987127371239101)
      ·
        refine ⟨10670785157995172764214663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28455427087987127371239101 10670785157995172764214663)
        ·
          refine ⟨16006177736992759146321995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670785157995172764214663 16006177736992759146321995)
          ·
            refine ⟨24009266605489138719482993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16006177736992759146321995 24009266605489138719482993)
            ·
              refine ⟨18006949954116854039612245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24009266605489138719482993 18006949954116854039612245)
              ·
                refine ⟨105509472387403441638353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18006949954116854039612245 105509472387403441638353)
                ·
                  rfl

theorem cell23_5547932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 9].length) (baseStart_5547932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547932 prefixEnd_5547932 := by exact prefixLift 5547932
  have htrace : WordTrace (prefixWord ++ tailWord_5547932) baseStart_5547932 baseEnd_5547932 := by
    simpa [prefixWord, tailWord_5547932, baseEnd_5547932] using wordTrace_append hprefix tailTrace_5547932
  have hstable : (prefixWord ++ tailWord_5547932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547932).length < 2 ^ (prefixWord ++ tailWord_5547932).sum := by decide
  have hdescent : baseEnd_5547932 < baseStart_5547932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547976 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_5547976 : Nat := 118140960795 + 5547976 * 2 ^ 59
def prefixEnd_5547976 : Nat := 4983230072969 + 3 ^ 40 * 5547976 * 2
def baseEnd_5547976 : Nat := 2848778347608690752085329

theorem tailTrace_5547976 : CollatzResearch.WordTrace tailWord_5547976 prefixEnd_5547976 2848778347608690752085329 := by
  unfold tailWord_5547976
  simp only [CollatzResearch.WordTrace]
  refine ⟨101175654274318972855039891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134900872365758630473386521 101175654274318972855039891)
  ·
    refine ⟨151763481411478459282559837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101175654274318972855039891 151763481411478459282559837)
    ·
      refine ⟨56911305529304422230959939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151763481411478459282559837 56911305529304422230959939)
      ·
        refine ⟨85366958293956633346439909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56911305529304422230959939 85366958293956633346439909)
        ·
          refine ⟨16006304680116868752457483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85366958293956633346439909 16006304680116868752457483)
          ·
            refine ⟨24009457020175303128686225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16006304680116868752457483 24009457020175303128686225)
            ·
              refine ⟨18007092765131477346514669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24009457020175303128686225 18007092765131477346514669)
              ·
                refine ⟨6752659786924304004943001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18007092765131477346514669 6752659786924304004943001)
                ·
                  refine ⟨5064494840193228003707251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752659786924304004943001 5064494840193228003707251)
                  ·
                    refine ⟨7596742260289842005560877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5064494840193228003707251 7596742260289842005560877)
                    ·
                      refine ⟨2848778347608690752085329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7596742260289842005560877 2848778347608690752085329)
                      ·
                        rfl

theorem cell23_5547976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_5547976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547976 prefixEnd_5547976 := by exact prefixLift 5547976
  have htrace : WordTrace (prefixWord ++ tailWord_5547976) baseStart_5547976 baseEnd_5547976 := by
    simpa [prefixWord, tailWord_5547976, baseEnd_5547976] using wordTrace_append hprefix tailTrace_5547976
  have hstable : (prefixWord ++ tailWord_5547976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547976).length < 2 ^ (prefixWord ++ tailWord_5547976).sum := by decide
  have hdescent : baseEnd_5547976 < baseStart_5547976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5547982 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_5547982 : Nat := 118140960795 + 5547982 * 2 ^ 59
def prefixEnd_5547982 : Nat := 4983230072969 + 3 ^ 40 * 5547982 * 2
def baseEnd_5547982 : Nat := 2848781428492617728610301

theorem tailTrace_5547982 : CollatzResearch.WordTrace tailWord_5547982 prefixEnd_5547982 2848781428492617728610301 := by
  unfold tailWord_5547982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25293940923327026091849775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134901018257744139156532133 25293940923327026091849775)
  ·
    refine ⟨37940911384990539137774663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25293940923327026091849775 37940911384990539137774663)
    ·
      refine ⟨56911367077485808706661995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37940911384990539137774663 56911367077485808706661995)
      ·
        refine ⟨85367050616228713059992993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56911367077485808706661995 85367050616228713059992993)
        ·
          refine ⟨64025287962171534794994745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85367050616228713059992993 64025287962171534794994745)
          ·
            refine ⟨48018965971628651096246059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64025287962171534794994745 48018965971628651096246059)
            ·
              refine ⟨72028448957442976644369089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48018965971628651096246059 72028448957442976644369089)
              ·
                refine ⟨54021336718082232483276817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72028448957442976644369089 54021336718082232483276817)
                ·
                  refine ⟨40516002538561674362457613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54021336718082232483276817 40516002538561674362457613)
                  ·
                    refine ⟨15193500951960627885921605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40516002538561674362457613 15193500951960627885921605)
                    ·
                      refine ⟨2848781428492617728610301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15193500951960627885921605 2848781428492617728610301)
                      ·
                        rfl

theorem cell23_5547982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_5547982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5547982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5547982 prefixEnd_5547982 := by exact prefixLift 5547982
  have htrace : WordTrace (prefixWord ++ tailWord_5547982) baseStart_5547982 baseEnd_5547982 := by
    simpa [prefixWord, tailWord_5547982, baseEnd_5547982] using wordTrace_append hprefix tailTrace_5547982
  have hstable : (prefixWord ++ tailWord_5547982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5547982).length < 2 ^ (prefixWord ++ tailWord_5547982).sum := by decide
  have hdescent : baseEnd_5547982 < baseStart_5547982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5547982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548003 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 1, 3, 2]
def baseStart_5548003 : Nat := 118140960795 + 5548003 * 2 ^ 59
def prefixEnd_5548003 : Nat := 4983230072969 + 3 ^ 40 * 5548003 * 2
def baseEnd_5548003 : Nat := 2848792211586362146447705

theorem tailTrace_5548003 : CollatzResearch.WordTrace tailWord_5548003 prefixEnd_5548003 2848792211586362146447705 := by
  unfold tailWord_5548003
  simp only [CollatzResearch.WordTrace]
  refine ⟨202352293319540129321312663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134901528879693419547541775 202352293319540129321312663)
  ·
    refine ⟨303528439979310193981968995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202352293319540129321312663 303528439979310193981968995)
    ·
      refine ⟨455292659968965290972953493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303528439979310193981968995 455292659968965290972953493)
      ·
        refine ⟨21341843436045248014357195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 455292659968965290972953493 21341843436045248014357195)
        ·
          refine ⟨32012765154067872021535793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21341843436045248014357195 32012765154067872021535793)
          ·
            refine ⟨24009573865550904016151845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32012765154067872021535793 24009573865550904016151845)
            ·
              refine ⟨4501795099790794503028471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24009573865550904016151845 4501795099790794503028471)
              ·
                refine ⟨6752692649686191754542707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501795099790794503028471 6752692649686191754542707)
                ·
                  refine ⟨10129038974529287631814061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6752692649686191754542707 10129038974529287631814061)
                  ·
                    refine ⟨3798389615448482861930273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10129038974529287631814061 3798389615448482861930273)
                    ·
                      refine ⟨2848792211586362146447705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798389615448482861930273 2848792211586362146447705)
                      ·
                        rfl

theorem cell23_5548003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_5548003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548003 prefixEnd_5548003 := by exact prefixLift 5548003
  have htrace : WordTrace (prefixWord ++ tailWord_5548003) baseStart_5548003 baseEnd_5548003 := by
    simpa [prefixWord, tailWord_5548003, baseEnd_5548003] using wordTrace_append hprefix tailTrace_5548003
  have hstable : (prefixWord ++ tailWord_5548003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548003).length < 2 ^ (prefixWord ++ tailWord_5548003).sum := by decide
  have hdescent : baseEnd_5548003 < baseStart_5548003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548032 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_5548032 : Nat := 118140960795 + 5548032 * 2 ^ 59
def prefixEnd_5548032 : Nat := 4983230072969 + 3 ^ 40 * 5548032 * 2
def baseEnd_5548032 : Nat := 2848807102525342532985071

theorem tailTrace_5548032 : CollatzResearch.WordTrace tailWord_5548032 prefixEnd_5548032 2848807102525342532985071 := by
  unfold tailWord_5548032
  simp only [CollatzResearch.WordTrace]
  refine ⟨101176675518217533637059175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134902234024290044849412233 101176675518217533637059175)
  ·
    refine ⟨151765013277326300455588763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101176675518217533637059175 151765013277326300455588763)
    ·
      refine ⟨227647519915989450683383145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151765013277326300455588763 227647519915989450683383145)
      ·
        refine ⟨170735639936992088012537359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227647519915989450683383145 170735639936992088012537359)
        ·
          refine ⟨256103459905488132018806039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170735639936992088012537359 256103459905488132018806039)
          ·
            refine ⟨384155189858232198028209059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256103459905488132018806039 384155189858232198028209059)
            ·
              refine ⟨576232784787348297042313589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384155189858232198028209059 576232784787348297042313589)
              ·
                refine ⟨54021823573813902847716899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 576232784787348297042313589 54021823573813902847716899)
                ·
                  refine ⟨81032735360720854271575349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54021823573813902847716899 81032735360720854271575349)
                  ·
                    refine ⟨7596818940067580087960189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81032735360720854271575349 7596818940067580087960189)
                    ·
                      refine ⟨2848807102525342532985071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7596818940067580087960189 2848807102525342532985071)
                      ·
                        rfl

theorem cell23_5548032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_5548032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548032 prefixEnd_5548032 := by exact prefixLift 5548032
  have htrace : WordTrace (prefixWord ++ tailWord_5548032) baseStart_5548032 baseEnd_5548032 := by
    simpa [prefixWord, tailWord_5548032, baseEnd_5548032] using wordTrace_append hprefix tailTrace_5548032
  have hstable : (prefixWord ++ tailWord_5548032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548032).length < 2 ^ (prefixWord ++ tailWord_5548032).sum := by decide
  have hdescent : baseEnd_5548032 < baseStart_5548032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548069 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_5548069 : Nat := 118140960795 + 5548069 * 2 ^ 59
def prefixEnd_5548069 : Nat := 4983230072969 + 3 ^ 40 * 5548069 * 2
def baseEnd_5548069 : Nat := 949608700436519629407467

theorem tailTrace_5548069 : CollatzResearch.WordTrace tailWord_5548069 prefixEnd_5548069 949608700436519629407467 := by
  unfold tailWord_5548069
  simp only [CollatzResearch.WordTrace]
  refine ⟨202354700537301022593215261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134903133691534015062143507 202354700537301022593215261)
  ·
    refine ⟨75883012701487883472455723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202354700537301022593215261 75883012701487883472455723)
    ·
      refine ⟨113824519052231825208683585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75883012701487883472455723 113824519052231825208683585)
      ·
        refine ⟨85368389289173868906512689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113824519052231825208683585 85368389289173868906512689)
        ·
          refine ⟨64026291966880401679884517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85368389289173868906512689 64026291966880401679884517)
          ·
            refine ⟨12004929743790075314978347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64026291966880401679884517 12004929743790075314978347)
            ·
              refine ⟨18007394615685112972467521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12004929743790075314978347 18007394615685112972467521)
              ·
                refine ⟨13505545961763834729350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18007394615685112972467521 13505545961763834729350641)
                ·
                  refine ⟨10129159471322876047012981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13505545961763834729350641 10129159471322876047012981)
                  ·
                    refine ⟨949608700436519629407467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10129159471322876047012981 949608700436519629407467)
                    ·
                      rfl

theorem cell23_5548069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_5548069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548069 prefixEnd_5548069 := by exact prefixLift 5548069
  have htrace : WordTrace (prefixWord ++ tailWord_5548069) baseStart_5548069 baseEnd_5548069 := by
    simpa [prefixWord, tailWord_5548069, baseEnd_5548069] using wordTrace_append hprefix tailTrace_5548069
  have hstable : (prefixWord ++ tailWord_5548069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548069).length < 2 ^ (prefixWord ++ tailWord_5548069).sum := by decide
  have hdescent : baseEnd_5548069 < baseStart_5548069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548084 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5548084 : Nat := 118140960795 + 5548084 * 2 ^ 59
def prefixEnd_5548084 : Nat := 4983230072969 + 3 ^ 40 * 5548084 * 2
def baseEnd_5548084 : Nat := 2848833803519376329534833

theorem tailTrace_5548084 : CollatzResearch.WordTrace tailWord_5548084 prefixEnd_5548084 2848833803519376329534833 := by
  unfold tailWord_5548084
  simp only [CollatzResearch.WordTrace]
  refine ⟨101177623816123340077505653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134903498421497786770007537 101177623816123340077505653)
  ·
    refine ⟨9485402232761563132266155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101177623816123340077505653 9485402232761563132266155)
    ·
      refine ⟨14228103349142344698399233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9485402232761563132266155 14228103349142344698399233)
      ·
        refine ⟨10671077511856758523799425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14228103349142344698399233 10671077511856758523799425)
        ·
          refine ⟨8003308133892568892849569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10671077511856758523799425 8003308133892568892849569)
          ·
            refine ⟨6002481100419426669637177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8003308133892568892849569 6002481100419426669637177)
            ·
              refine ⟨4501860825314570002227883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6002481100419426669637177 4501860825314570002227883)
              ·
                refine ⟨6752791237971855003341825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501860825314570002227883 6752791237971855003341825)
                ·
                  refine ⟨5064593428478891252506369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752791237971855003341825 5064593428478891252506369)
                  ·
                    refine ⟨3798445071359168439379777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5064593428478891252506369 3798445071359168439379777)
                    ·
                      refine ⟨2848833803519376329534833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798445071359168439379777 2848833803519376329534833)
                      ·
                        rfl

theorem cell23_5548084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5548084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548084 prefixEnd_5548084 := by exact prefixLift 5548084
  have htrace : WordTrace (prefixWord ++ tailWord_5548084) baseStart_5548084 baseEnd_5548084 := by
    simpa [prefixWord, tailWord_5548084, baseEnd_5548084] using wordTrace_append hprefix tailTrace_5548084
  have hstable : (prefixWord ++ tailWord_5548084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548084).length < 2 ^ (prefixWord ++ tailWord_5548084).sum := by decide
  have hdescent : baseEnd_5548084 < baseStart_5548084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548133 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_5548133 : Nat := 118140960795 + 5548133 * 2 ^ 59
def prefixEnd_5548133 : Nat := 4983230072969 + 3 ^ 40 * 5548133 * 2
def baseEnd_5548133 : Nat := 949619654690482212607369

theorem tailTrace_5548133 : CollatzResearch.WordTrace tailWord_5548133 prefixEnd_5548133 949619654690482212607369 := by
  unfold tailWord_5548133
  simp only [CollatzResearch.WordTrace]
  refine ⟨202357034809069161523545053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134904689872712774349030035 202357034809069161523545053)
  ·
    refine ⟨75883888053400935571329395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202357034809069161523545053 75883888053400935571329395)
    ·
      refine ⟨113825832080101403356994093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75883888053400935571329395 113825832080101403356994093)
      ·
        refine ⟨42684687030038026258872785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113825832080101403356994093 42684687030038026258872785)
        ·
          refine ⟨32013515272528519694154589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42684687030038026258872785 32013515272528519694154589)
          ·
            refine ⟨12005068227198194885307971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32013515272528519694154589 12005068227198194885307971)
            ·
              refine ⟨18007602340797292327961957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005068227198194885307971 18007602340797292327961957)
              ·
                refine ⟨3376425438899492311492867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18007602340797292327961957 3376425438899492311492867)
                ·
                  refine ⟨5064638158349238467239301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376425438899492311492867 5064638158349238467239301)
                  ·
                    refine ⟨949619654690482212607369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5064638158349238467239301 949619654690482212607369)
                    ·
                      rfl

theorem cell23_5548133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_5548133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548133 prefixEnd_5548133 := by exact prefixLift 5548133
  have htrace : WordTrace (prefixWord ++ tailWord_5548133) baseStart_5548133 baseEnd_5548133 := by
    simpa [prefixWord, tailWord_5548133, baseEnd_5548133] using wordTrace_append hprefix tailTrace_5548133
  have hstable : (prefixWord ++ tailWord_5548133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548133).length < 2 ^ (prefixWord ++ tailWord_5548133).sum := by decide
  have hdescent : baseEnd_5548133 < baseStart_5548133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548152 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_5548152 : Nat := 118140960795 + 5548152 * 2 ^ 59
def prefixEnd_5548152 : Nat := 4983230072969 + 3 ^ 40 * 5548152 * 2
def baseEnd_5548152 : Nat := 2848868720203882063484519

theorem tailTrace_5548152 : CollatzResearch.WordTrace tailWord_5548152 prefixEnd_5548152 2848868720203882063484519 := by
  unfold tailWord_5548152
  simp only [CollatzResearch.WordTrace]
  refine ⟨101178863898000163884243355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134905151864000218512324473 101178863898000163884243355)
  ·
    refine ⟨151768295847000245826365033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101178863898000163884243355 151768295847000245826365033)
    ·
      refine ⟨113826221885250184369773775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151768295847000245826365033 113826221885250184369773775)
      ·
        refine ⟨170739332827875276554660663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113826221885250184369773775 170739332827875276554660663)
        ·
          refine ⟨256108999241812914831990995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170739332827875276554660663 256108999241812914831990995)
          ·
            refine ⟨384163498862719372247986493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256108999241812914831990995 384163498862719372247986493)
            ·
              refine ⟨144061312073519764592994935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384163498862719372247986493 144061312073519764592994935)
              ·
                refine ⟨216091968110279646889492403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144061312073519764592994935 216091968110279646889492403)
                ·
                  refine ⟨324137952165419470334238605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216091968110279646889492403 324137952165419470334238605)
                  ·
                    refine ⟨121551732062032301375339477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324137952165419470334238605 121551732062032301375339477)
                    ·
                      refine ⟨2848868720203882063484519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121551732062032301375339477 2848868720203882063484519)
                      ·
                        rfl

theorem cell23_5548152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_5548152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548152 prefixEnd_5548152 := by exact prefixLift 5548152
  have htrace : WordTrace (prefixWord ++ tailWord_5548152) baseStart_5548152 baseEnd_5548152 := by
    simpa [prefixWord, tailWord_5548152, baseEnd_5548152] using wordTrace_append hprefix tailTrace_5548152
  have hstable : (prefixWord ++ tailWord_5548152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548152).length < 2 ^ (prefixWord ++ tailWord_5548152).sum := by decide
  have hdescent : baseEnd_5548152 < baseStart_5548152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548156 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_5548156 : Nat := 118140960795 + 5548156 * 2 ^ 59
def prefixEnd_5548156 : Nat := 4983230072969 + 3 ^ 40 * 5548156 * 2
def baseEnd_5548156 : Nat := 2848870774126500047834501

theorem tailTrace_5548156 : CollatzResearch.WordTrace tailWord_5548156 prefixEnd_5548156 2848870774126500047834501 := by
  unfold tailWord_5548156
  simp only [CollatzResearch.WordTrace]
  refine ⟨101178936843992918225816161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134905249125323890967754881 101178936843992918225816161)
  ·
    refine ⟨75884202632994688669362121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101178936843992918225816161 75884202632994688669362121)
    ·
      refine ⟨56913151974746016502021591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75884202632994688669362121 56913151974746016502021591)
      ·
        refine ⟨85369727962119024753032387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56913151974746016502021591 85369727962119024753032387)
        ·
          refine ⟨128054591943178537129548581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85369727962119024753032387 128054591943178537129548581)
          ·
            refine ⟨24010235989345975711790359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128054591943178537129548581 24010235989345975711790359)
            ·
              refine ⟨36015353984018963567685539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24010235989345975711790359 36015353984018963567685539)
              ·
                refine ⟨54023030976028445351528309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36015353984018963567685539 54023030976028445351528309)
                ·
                  refine ⟨5064659154002666751705779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54023030976028445351528309 5064659154002666751705779)
                  ·
                    refine ⟨7596988731004000127558669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5064659154002666751705779 7596988731004000127558669)
                    ·
                      refine ⟨2848870774126500047834501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7596988731004000127558669 2848870774126500047834501)
                      ·
                        rfl

theorem cell23_5548156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_5548156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548156 prefixEnd_5548156 := by exact prefixLift 5548156
  have htrace : WordTrace (prefixWord ++ tailWord_5548156) baseStart_5548156 baseEnd_5548156 := by
    simpa [prefixWord, tailWord_5548156, baseEnd_5548156] using wordTrace_append hprefix tailTrace_5548156
  have hstable : (prefixWord ++ tailWord_5548156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548156).length < 2 ^ (prefixWord ++ tailWord_5548156).sum := by decide
  have hdescent : baseEnd_5548156 < baseStart_5548156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548180 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 6]
def baseStart_5548180 : Nat := 118140960795 + 5548180 * 2 ^ 59
def prefixEnd_5548180 : Nat := 4983230072969 + 3 ^ 40 * 5548180 * 2
def baseEnd_5548180 : Nat := 316542566406911994881599

theorem tailTrace_5548180 : CollatzResearch.WordTrace tailWord_5548180 prefixEnd_5548180 316542566406911994881599 := by
  unfold tailWord_5548180
  simp only [CollatzResearch.WordTrace]
  refine ⟨101179374519949444275252997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134905832693265925700337329 101179374519949444275252997)
  ·
    refine ⟨18971132722490520801609937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101179374519949444275252997 18971132722490520801609937)
    ·
      refine ⟨14228349541867890601207453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18971132722490520801609937 14228349541867890601207453)
      ·
        refine ⟨5335631078200458975452795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14228349541867890601207453 5335631078200458975452795)
        ·
          refine ⟨8003446617300688463179193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335631078200458975452795 8003446617300688463179193)
          ·
            refine ⟨6002584962975516347384395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8003446617300688463179193 6002584962975516347384395)
            ·
              refine ⟨9003877444463274521076593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6002584962975516347384395 9003877444463274521076593)
              ·
                refine ⟨6752908083347455890807445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9003877444463274521076593 6752908083347455890807445)
                ·
                  refine ⟨316542566406911994881599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6752908083347455890807445 316542566406911994881599)
                  ·
                    rfl

theorem cell23_5548180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_5548180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548180 prefixEnd_5548180 := by exact prefixLift 5548180
  have htrace : WordTrace (prefixWord ++ tailWord_5548180) baseStart_5548180 baseEnd_5548180 := by
    simpa [prefixWord, tailWord_5548180, baseEnd_5548180] using wordTrace_append hprefix tailTrace_5548180
  have hstable : (prefixWord ++ tailWord_5548180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548180).length < 2 ^ (prefixWord ++ tailWord_5548180).sum := by decide
  have hdescent : baseEnd_5548180 < baseStart_5548180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548303 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 4, 2, 2]
def baseStart_5548303 : Nat := 118140960795 + 5548303 * 2 ^ 59
def prefixEnd_5548303 : Nat := 4983230072969 + 3 ^ 40 * 5548303 * 2
def baseEnd_5548303 : Nat := 2848946255782710972696325

theorem tailTrace_5548303 : CollatzResearch.WordTrace tailWord_5548303 prefixEnd_5548303 2848946255782710972696325 := by
  unfold tailWord_5548303
  simp only [CollatzResearch.WordTrace]
  refine ⟨202363235218453280557233563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134908823478968853704822375 202363235218453280557233563)
  ·
    refine ⟨303544852827679920835850345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202363235218453280557233563 303544852827679920835850345)
    ·
      refine ⟨227658639620759940626887759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303544852827679920835850345 227658639620759940626887759)
      ·
        refine ⟨341487959431139910940331639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227658639620759940626887759 341487959431139910940331639)
        ·
          refine ⟨512231939146709866410497459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341487959431139910940331639 512231939146709866410497459)
          ·
            refine ⟨768347908720064799615746189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512231939146709866410497459 768347908720064799615746189)
            ·
              refine ⟨288130465770024299855904821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768347908720064799615746189 288130465770024299855904821)
              ·
                refine ⟨27012231165939778111491077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288130465770024299855904821 27012231165939778111491077)
                ·
                  refine ⟨5064793343613708395904577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27012231165939778111491077 5064793343613708395904577)
                  ·
                    refine ⟨3798595007710281296928433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5064793343613708395904577 3798595007710281296928433)
                    ·
                      refine ⟨2848946255782710972696325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798595007710281296928433 2848946255782710972696325)
                      ·
                        rfl

theorem cell23_5548303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 2, 2].length) (baseStart_5548303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548303 prefixEnd_5548303 := by exact prefixLift 5548303
  have htrace : WordTrace (prefixWord ++ tailWord_5548303) baseStart_5548303 baseEnd_5548303 := by
    simpa [prefixWord, tailWord_5548303, baseEnd_5548303] using wordTrace_append hprefix tailTrace_5548303
  have hstable : (prefixWord ++ tailWord_5548303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548303).length < 2 ^ (prefixWord ++ tailWord_5548303).sum := by decide
  have hdescent : baseEnd_5548303 < baseStart_5548303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548320 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5548320 : Nat := 118140960795 + 5548320 * 2 ^ 59
def prefixEnd_5548320 : Nat := 4983230072969 + 3 ^ 40 * 5548320 * 2
def baseEnd_5548320 : Nat := 2848954984953837406183747

theorem tailTrace_5548320 : CollatzResearch.WordTrace tailWord_5548320 prefixEnd_5548320 2848954984953837406183747 := by
  unfold tailWord_5548320
  simp only [CollatzResearch.WordTrace]
  refine ⟨101181927629695846230301207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134909236839594461640401609 101181927629695846230301207)
  ·
    refine ⟨151772891444543769345451811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101181927629695846230301207 151772891444543769345451811)
    ·
      refine ⟨227659337166815654018177717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151772891444543769345451811 227659337166815654018177717)
      ·
        refine ⟨21343062859388967564204161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227659337166815654018177717 21343062859388967564204161)
        ·
          refine ⟨16007297144541725673153121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21343062859388967564204161 16007297144541725673153121)
          ·
            refine ⟨12005472858406294254864841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16007297144541725673153121 12005472858406294254864841)
            ·
              refine ⟨9004104643804720691148631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12005472858406294254864841 9004104643804720691148631)
              ·
                refine ⟨13506156965707081036722947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004104643804720691148631 13506156965707081036722947)
                ·
                  refine ⟨20259235448560621555084421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13506156965707081036722947 20259235448560621555084421)
                  ·
                    refine ⟨3798606646605116541578329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20259235448560621555084421 3798606646605116541578329)
                    ·
                      refine ⟨2848954984953837406183747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798606646605116541578329 2848954984953837406183747)
                      ·
                        rfl

theorem cell23_5548320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5548320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548320 prefixEnd_5548320 := by exact prefixLift 5548320
  have htrace : WordTrace (prefixWord ++ tailWord_5548320) baseStart_5548320 baseEnd_5548320 := by
    simpa [prefixWord, tailWord_5548320, baseEnd_5548320] using wordTrace_append hprefix tailTrace_5548320
  have hstable : (prefixWord ++ tailWord_5548320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548320).length < 2 ^ (prefixWord ++ tailWord_5548320).sum := by decide
  have hdescent : baseEnd_5548320 < baseStart_5548320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548376 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_5548376 : Nat := 118140960795 + 5548376 * 2 ^ 59
def prefixEnd_5548376 : Nat := 4983230072969 + 3 ^ 40 * 5548376 * 2
def baseEnd_5548376 : Nat := 2848983739870489187083489

theorem tailTrace_5548376 : CollatzResearch.WordTrace tailWord_5548376 prefixEnd_5548376 2848983739870489187083489 := by
  unfold tailWord_5548376
  simp only [CollatzResearch.WordTrace]
  refine ⟨101182948873594407012320491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134910598498125876016427321 101182948873594407012320491)
  ·
    refine ⟨151774423310391610518480737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101182948873594407012320491 151774423310391610518480737)
    ·
      refine ⟨113830817482793707888860553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151774423310391610518480737 113830817482793707888860553)
      ·
        refine ⟨85373113112095280916645415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113830817482793707888860553 85373113112095280916645415)
        ·
          refine ⟨128059669668142921374968123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85373113112095280916645415 128059669668142921374968123)
          ·
            refine ⟨192089504502214382062452185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128059669668142921374968123 192089504502214382062452185)
            ·
              refine ⟨144067128376660786546839139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192089504502214382062452185 144067128376660786546839139)
              ·
                refine ⟨216100692564991179820258709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144067128376660786546839139 216100692564991179820258709)
                ·
                  refine ⟨10129719963983961554074627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216100692564991179820258709 10129719963983961554074627)
                  ·
                    refine ⟨15194579945975942331111941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10129719963983961554074627 15194579945975942331111941)
                    ·
                      refine ⟨2848983739870489187083489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15194579945975942331111941 2848983739870489187083489)
                      ·
                        rfl

theorem cell23_5548376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_5548376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548376 prefixEnd_5548376 := by exact prefixLift 5548376
  have htrace : WordTrace (prefixWord ++ tailWord_5548376) baseStart_5548376 baseEnd_5548376 := by
    simpa [prefixWord, tailWord_5548376, baseEnd_5548376] using wordTrace_append hprefix tailTrace_5548376
  have hstable : (prefixWord ++ tailWord_5548376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548376).length < 2 ^ (prefixWord ++ tailWord_5548376).sum := by decide
  have hdescent : baseEnd_5548376 < baseStart_5548376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548413 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_5548413 : Nat := 118140960795 + 5548413 * 2 ^ 59
def prefixEnd_5548413 : Nat := 4983230072969 + 3 ^ 40 * 5548413 * 2
def baseEnd_5548413 : Nat := 2849002738654705542320819

theorem tailTrace_5548413 : CollatzResearch.WordTrace tailWord_5548413 prefixEnd_5548413 2849002738654705542320819 := by
  unfold tailWord_5548413
  simp only [CollatzResearch.WordTrace]
  refine ⟨202367247248054769343737893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134911498165369846229158595 202367247248054769343737893)
  ·
    refine ⟨37943858859010269251950855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202367247248054769343737893 37943858859010269251950855)
    ·
      refine ⟨56915788288515403877926283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37943858859010269251950855 56915788288515403877926283)
      ·
        refine ⟨85373682432773105816889425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56915788288515403877926283 85373682432773105816889425)
        ·
          refine ⟨64030261824579829362667069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85373682432773105816889425 64030261824579829362667069)
          ·
            refine ⟨24011348184217436011000151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64030261824579829362667069 24011348184217436011000151)
            ·
              refine ⟨36017022276326154016500227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24011348184217436011000151 36017022276326154016500227)
              ·
                refine ⟨54025533414489231024750341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36017022276326154016500227 54025533414489231024750341)
                ·
                  refine ⟨10129787515216730817140689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54025533414489231024750341 10129787515216730817140689)
                  ·
                    refine ⟨7597340636412548112855517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10129787515216730817140689 7597340636412548112855517)
                    ·
                      refine ⟨2849002738654705542320819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7597340636412548112855517 2849002738654705542320819)
                      ·
                        rfl

theorem cell23_5548413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_5548413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548413 prefixEnd_5548413 := by exact prefixLift 5548413
  have htrace : WordTrace (prefixWord ++ tailWord_5548413) baseStart_5548413 baseEnd_5548413 := by
    simpa [prefixWord, tailWord_5548413, baseEnd_5548413] using wordTrace_append hprefix tailTrace_5548413
  have hstable : (prefixWord ++ tailWord_5548413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548413).length < 2 ^ (prefixWord ++ tailWord_5548413).sum := by decide
  have hdescent : baseEnd_5548413 < baseStart_5548413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548483 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 6, 2]
def baseStart_5548483 : Nat := 118140960795 + 5548483 * 2 ^ 59
def prefixEnd_5548483 : Nat := 4983230072969 + 3 ^ 40 * 5548483 * 2
def baseEnd_5548483 : Nat := 2849038682300520268445497

theorem tailTrace_5548483 : CollatzResearch.WordTrace tailWord_5548483 prefixEnd_5548483 2849038682300520268445497 := by
  unfold tailWord_5548483
  simp only [CollatzResearch.WordTrace]
  refine ⟨202369800357801171298786103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134913200238534114199190735 202369800357801171298786103)
  ·
    refine ⟨303554700536701756948179155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202369800357801171298786103 303554700536701756948179155)
    ·
      refine ⟨455332050805052635422268733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303554700536701756948179155 455332050805052635422268733)
      ·
        refine ⟨170749519051894738283350775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455332050805052635422268733 170749519051894738283350775)
        ·
          refine ⟨256124278577842107425026163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170749519051894738283350775 256124278577842107425026163)
          ·
            refine ⟨384186417866763161137539245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256124278577842107425026163 384186417866763161137539245)
            ·
              refine ⟨144069906700036185426577217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384186417866763161137539245 144069906700036185426577217)
              ·
                refine ⟨108052430025027139069932913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144069906700036185426577217 108052430025027139069932913)
                ·
                  refine ⟨81039322518770354302449685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108052430025027139069932913 81039322518770354302449685)
                  ·
                    refine ⟨3798718243067360357927329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81039322518770354302449685 3798718243067360357927329)
                    ·
                      refine ⟨2849038682300520268445497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798718243067360357927329 2849038682300520268445497)
                      ·
                        rfl

theorem cell23_5548483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_5548483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548483 prefixEnd_5548483 := by exact prefixLift 5548483
  have htrace : WordTrace (prefixWord ++ tailWord_5548483) baseStart_5548483 baseEnd_5548483 := by
    simpa [prefixWord, tailWord_5548483, baseEnd_5548483] using wordTrace_append hprefix tailTrace_5548483
  have hstable : (prefixWord ++ tailWord_5548483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548483).length < 2 ^ (prefixWord ++ tailWord_5548483).sum := by decide
  have hdescent : baseEnd_5548483 < baseStart_5548483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548500 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5548500 : Nat := 118140960795 + 5548500 * 2 ^ 59
def prefixEnd_5548500 : Nat := 4983230072969 + 3 ^ 40 * 5548500 * 2
def baseEnd_5548500 : Nat := 2849047411471646701932919

theorem tailTrace_5548500 : CollatzResearch.WordTrace tailWord_5548500 prefixEnd_5548500 2849047411471646701932919 := by
  unfold tailWord_5548500
  simp only [CollatzResearch.WordTrace]
  refine ⟨101185210199369791601077477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134913613599159722134769969 101185210199369791601077477)
  ·
    refine ⟨18972226912381835925202027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101185210199369791601077477 18972226912381835925202027)
    ·
      refine ⟨28458340368572753887803041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18972226912381835925202027 28458340368572753887803041)
      ·
        refine ⟨21343755276429565415852281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28458340368572753887803041 21343755276429565415852281)
        ·
          refine ⟨16007816457322174061889211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21343755276429565415852281 16007816457322174061889211)
          ·
            refine ⟨24011724685983261092833817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16007816457322174061889211 24011724685983261092833817)
            ·
              refine ⟨18008793514487445819625363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24011724685983261092833817 18008793514487445819625363)
              ·
                refine ⟨27013190271731168729438045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18008793514487445819625363 27013190271731168729438045)
                ·
                  refine ⟨10129946351899188273539267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27013190271731168729438045 10129946351899188273539267)
                  ·
                    refine ⟨15194919527848782410308901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10129946351899188273539267 15194919527848782410308901)
                    ·
                      refine ⟨2849047411471646701932919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15194919527848782410308901 2849047411471646701932919)
                      ·
                        rfl

theorem cell23_5548500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5548500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548500 prefixEnd_5548500 := by exact prefixLift 5548500
  have htrace : WordTrace (prefixWord ++ tailWord_5548500) baseStart_5548500 baseEnd_5548500 := by
    simpa [prefixWord, tailWord_5548500, baseEnd_5548500] using wordTrace_append hprefix tailTrace_5548500
  have hstable : (prefixWord ++ tailWord_5548500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548500).length < 2 ^ (prefixWord ++ tailWord_5548500).sum := by decide
  have hdescent : baseEnd_5548500 < baseStart_5548500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548513 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_5548513 : Nat := 118140960795 + 5548513 * 2 ^ 59
def prefixEnd_5548513 : Nat := 4983230072969 + 3 ^ 40 * 5548513 * 2
def baseEnd_5548513 : Nat := 2849054086720155151070359

theorem tailTrace_5548513 : CollatzResearch.WordTrace tailWord_5548513 prefixEnd_5548513 2849054086720155151070359 := by
  unfold tailWord_5548513
  simp only [CollatzResearch.WordTrace]
  refine ⟨202370894547692486422378193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134913929698461657614918795 202370894547692486422378193)
  ·
    refine ⟨151778170910769364816783645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202370894547692486422378193 151778170910769364816783645)
    ·
      refine ⟨56916814091538511806293867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151778170910769364816783645 56916814091538511806293867)
      ·
        refine ⟨85375221137307767709440801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56916814091538511806293867 85375221137307767709440801)
        ·
          refine ⟨64031415852980825782080601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85375221137307767709440801 64031415852980825782080601)
          ·
            refine ⟨48023561889735619336560451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64031415852980825782080601 48023561889735619336560451)
            ·
              refine ⟨72035342834603429004840677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48023561889735619336560451 72035342834603429004840677)
              ·
                refine ⟨13506626781488142938407627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72035342834603429004840677 13506626781488142938407627)
                ·
                  refine ⟨20259940172232214407611441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13506626781488142938407627 20259940172232214407611441)
                  ·
                    refine ⟨15194955129174160805708581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20259940172232214407611441 15194955129174160805708581)
                    ·
                      refine ⟨2849054086720155151070359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15194955129174160805708581 2849054086720155151070359)
                      ·
                        rfl

theorem cell23_5548513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_5548513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548513 prefixEnd_5548513 := by exact prefixLift 5548513
  have htrace : WordTrace (prefixWord ++ tailWord_5548513) baseStart_5548513 baseEnd_5548513 := by
    simpa [prefixWord, tailWord_5548513, baseEnd_5548513] using wordTrace_append hprefix tailTrace_5548513
  have hstable : (prefixWord ++ tailWord_5548513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548513).length < 2 ^ (prefixWord ++ tailWord_5548513).sum := by decide
  have hdescent : baseEnd_5548513 < baseStart_5548513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548514 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5548514 : Nat := 118140960795 + 5548514 * 2 ^ 59
def prefixEnd_5548514 : Nat := 4983230072969 + 3 ^ 40 * 5548514 * 2
def baseEnd_5548514 : Nat := 949684866733603215719285

theorem tailTrace_5548514 : CollatzResearch.WordTrace tailWord_5548514 prefixEnd_5548514 949684866733603215719285 := by
  unfold tailWord_5548514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50592732755172215898291149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134913954013792575728776397 50592732755172215898291149)
  ·
    refine ⟨18972274783189580961859181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50592732755172215898291149 18972274783189580961859181)
    ·
      refine ⟨7114603043696092860697193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18972274783189580961859181 7114603043696092860697193)
      ·
        refine ⟨5335952282772069645522895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7114603043696092860697193 5335952282772069645522895)
        ·
          refine ⟨8003928424158104468284343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335952282772069645522895 8003928424158104468284343)
          ·
            refine ⟨12005892636237156702426515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003928424158104468284343 12005892636237156702426515)
            ·
              refine ⟨18008838954355735053639773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005892636237156702426515 18008838954355735053639773)
              ·
                refine ⟨6753314607883400645114915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18008838954355735053639773 6753314607883400645114915)
                ·
                  refine ⟨10129971911825100967672373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6753314607883400645114915 10129971911825100967672373)
                  ·
                    refine ⟨949684866733603215719285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10129971911825100967672373 949684866733603215719285)
                    ·
                      rfl

theorem cell23_5548514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5548514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548514 prefixEnd_5548514 := by exact prefixLift 5548514
  have htrace : WordTrace (prefixWord ++ tailWord_5548514) baseStart_5548514 baseEnd_5548514 := by
    simpa [prefixWord, tailWord_5548514, baseEnd_5548514] using wordTrace_append hprefix tailTrace_5548514
  have hstable : (prefixWord ++ tailWord_5548514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548514).length < 2 ^ (prefixWord ++ tailWord_5548514).sum := by decide
  have hdescent : baseEnd_5548514 < baseStart_5548514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548517 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5548517 : Nat := 118140960795 + 5548517 * 2 ^ 59
def prefixEnd_5548517 : Nat := 4983230072969 + 3 ^ 40 * 5548517 * 2
def baseEnd_5548517 : Nat := 2849056140642773135420341

theorem tailTrace_5548517 : CollatzResearch.WordTrace tailWord_5548517 prefixEnd_5548517 2849056140642773135420341 := by
  unfold tailWord_5548517
  simp only [CollatzResearch.WordTrace]
  refine ⟨202371040439677995105523805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134914026959785330070349203 202371040439677995105523805)
  ·
    refine ⟨75889140164879248164571427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202371040439677995105523805 75889140164879248164571427)
    ·
      refine ⟨113833710247318872246857141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75889140164879248164571427 113833710247318872246857141)
      ·
        refine ⟨10671910335686144273142857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113833710247318872246857141 10671910335686144273142857)
        ·
          refine ⟨8003932751764608204857143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10671910335686144273142857 8003932751764608204857143)
          ·
            refine ⟨12005899127646912307285715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003932751764608204857143 12005899127646912307285715)
            ·
              refine ⟨18008848691470368460928573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005899127646912307285715 18008848691470368460928573)
              ·
                refine ⟨6753318259301388172848215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18008848691470368460928573 6753318259301388172848215)
                ·
                  refine ⟨10129977388952082259272323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6753318259301388172848215 10129977388952082259272323)
                  ·
                    refine ⟨15194966083428123388908485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10129977388952082259272323 15194966083428123388908485)
                    ·
                      refine ⟨2849056140642773135420341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15194966083428123388908485 2849056140642773135420341)
                      ·
                        rfl

theorem cell23_5548517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5548517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548517 prefixEnd_5548517 := by exact prefixLift 5548517
  have htrace : WordTrace (prefixWord ++ tailWord_5548517) baseStart_5548517 baseEnd_5548517 := by
    simpa [prefixWord, tailWord_5548517, baseEnd_5548517] using wordTrace_append hprefix tailTrace_5548517
  have hstable : (prefixWord ++ tailWord_5548517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548517).length < 2 ^ (prefixWord ++ tailWord_5548517).sum := by decide
  have hdescent : baseEnd_5548517 < baseStart_5548517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548534 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5548534 : Nat := 118140960795 + 5548534 * 2 ^ 59
def prefixEnd_5548534 : Nat := 4983230072969 + 3 ^ 40 * 5548534 * 2
def baseEnd_5548534 : Nat := 2849064869813899568907763

theorem tailTrace_5548534 : CollatzResearch.WordTrace tailWord_5548534 prefixEnd_5548534 2849064869813899568907763 := by
  unfold tailWord_5548534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12648228780038525438055791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134914440320410938005928437 12648228780038525438055791)
  ·
    refine ⟨18972343170057788157083687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12648228780038525438055791 18972343170057788157083687)
    ·
      refine ⟨28458514755086682235625531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18972343170057788157083687 28458514755086682235625531)
      ·
        refine ⟨42687772132630023353438297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28458514755086682235625531 42687772132630023353438297)
        ·
          refine ⟨32015829099472517515078723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42687772132630023353438297 32015829099472517515078723)
          ·
            refine ⟨48023743649208776272618085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32015829099472517515078723 48023743649208776272618085)
            ·
              refine ⟨9004451934226645551115891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48023743649208776272618085 9004451934226645551115891)
              ·
                refine ⟨13506677901339968326673837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004451934226645551115891 13506677901339968326673837)
                ·
                  refine ⟨5065004213002488122502689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13506677901339968326673837 5065004213002488122502689)
                  ·
                    refine ⟨3798753159751866091877017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5065004213002488122502689 3798753159751866091877017)
                    ·
                      refine ⟨2849064869813899568907763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798753159751866091877017 2849064869813899568907763)
                      ·
                        rfl

theorem cell23_5548534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5548534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548534 prefixEnd_5548534 := by exact prefixLift 5548534
  have htrace : WordTrace (prefixWord ++ tailWord_5548534) baseStart_5548534 baseEnd_5548534 := by
    simpa [prefixWord, tailWord_5548534, baseEnd_5548534] using wordTrace_append hprefix tailTrace_5548534
  have hstable : (prefixWord ++ tailWord_5548534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548534).length < 2 ^ (prefixWord ++ tailWord_5548534).sum := by decide
  have hdescent : baseEnd_5548534 < baseStart_5548534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548557 : List Nat := [1, 7, 1, 1, 1, 2, 1, 9]
def baseStart_5548557 : Nat := 118140960795 + 5548557 * 2 ^ 59
def prefixEnd_5548557 : Nat := 4983230072969 + 3 ^ 40 * 5548557 * 2
def baseEnd_5548557 : Nat := 105521358513664925145191

theorem tailTrace_5548557 : CollatzResearch.WordTrace tailWord_5548557 prefixEnd_5548557 105521358513664925145191 := by
  unfold tailWord_5548557
  simp only [CollatzResearch.WordTrace]
  refine ⟨202372499359533081936979925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134914999573022054624653283 202372499359533081936979925)
  ·
    refine ⟨4743105453739056607897967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 202372499359533081936979925 4743105453739056607897967)
    ·
      refine ⟨7114658180608584911846951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743105453739056607897967 7114658180608584911846951)
      ·
        refine ⟨10671987270912877367770427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7114658180608584911846951 10671987270912877367770427)
        ·
          refine ⟨16007980906369316051655641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10671987270912877367770427 16007980906369316051655641)
          ·
            refine ⟨12005985679776987038741731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16007980906369316051655641 12005985679776987038741731)
            ·
              refine ⟨18008978519665480558112597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005985679776987038741731 18008978519665480558112597)
              ·
                refine ⟨105521358513664925145191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18008978519665480558112597 105521358513664925145191)
                ·
                  rfl

theorem cell23_5548557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 9].length) (baseStart_5548557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548557 prefixEnd_5548557 := by exact prefixLift 5548557
  have htrace : WordTrace (prefixWord ++ tailWord_5548557) baseStart_5548557 baseEnd_5548557 := by
    simpa [prefixWord, tailWord_5548557, baseEnd_5548557] using wordTrace_append hprefix tailTrace_5548557
  have hstable : (prefixWord ++ tailWord_5548557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548557).length < 2 ^ (prefixWord ++ tailWord_5548557).sum := by decide
  have hdescent : baseEnd_5548557 < baseStart_5548557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548577 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_5548577 : Nat := 118140960795 + 5548577 * 2 ^ 59
def prefixEnd_5548577 : Nat := 4983230072969 + 3 ^ 40 * 5548577 * 2
def baseEnd_5548577 : Nat := 2849086949482042900670065

theorem tailTrace_5548577 : CollatzResearch.WordTrace tailWord_5548577 prefixEnd_5548577 2849086949482042900670065 := by
  unfold tailWord_5548577
  simp only [CollatzResearch.WordTrace]
  refine ⟨202373228819460625352707985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134915485879640416901805323 202373228819460625352707985)
  ·
    refine ⟨151779921614595469014530989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202373228819460625352707985 151779921614595469014530989)
    ·
      refine ⟨56917470605473300880449121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151779921614595469014530989 56917470605473300880449121)
      ·
        refine ⟨42688102954104975660336841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56917470605473300880449121 42688102954104975660336841)
        ·
          refine ⟨32016077215578731745252631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42688102954104975660336841 32016077215578731745252631)
          ·
            refine ⟨48024115823368097617878947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32016077215578731745252631 48024115823368097617878947)
            ·
              refine ⟨72036173735052146426818421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48024115823368097617878947 72036173735052146426818421)
              ·
                refine ⟨6753391287661138727514227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72036173735052146426818421 6753391287661138727514227)
                ·
                  refine ⟨10130086931491708091271341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6753391287661138727514227 10130086931491708091271341)
                  ·
                    refine ⟨3798782599309390534226753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10130086931491708091271341 3798782599309390534226753)
                    ·
                      refine ⟨2849086949482042900670065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3798782599309390534226753 2849086949482042900670065)
                      ·
                        rfl

theorem cell23_5548577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_5548577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548577 prefixEnd_5548577 := by exact prefixLift 5548577
  have htrace : WordTrace (prefixWord ++ tailWord_5548577) baseStart_5548577 baseEnd_5548577 := by
    simpa [prefixWord, tailWord_5548577, baseEnd_5548577] using wordTrace_append hprefix tailTrace_5548577
  have hstable : (prefixWord ++ tailWord_5548577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548577).length < 2 ^ (prefixWord ++ tailWord_5548577).sum := by decide
  have hdescent : baseEnd_5548577 < baseStart_5548577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548677 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_5548677 : Nat := 118140960795 + 5548677 * 2 ^ 59
def prefixEnd_5548677 : Nat := 4983230072969 + 3 ^ 40 * 5548677 * 2
def baseEnd_5548677 : Nat := 949712765849164169806535

theorem tailTrace_5548677 : CollatzResearch.WordTrace tailWord_5548677 prefixEnd_5548677 949712765849164169806535 := by
  unfold tailWord_5548677
  simp only [CollatzResearch.WordTrace]
  refine ⟨202376876119098342431348285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134917917412732228287565523 202376876119098342431348285)
  ·
    refine ⟨75891328544661878411755607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202376876119098342431348285 75891328544661878411755607)
    ·
      refine ⟨113836992816992817617633411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75891328544661878411755607 113836992816992817617633411)
      ·
        refine ⟨170755489225489226426450117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113836992816992817617633411 170755489225489226426450117)
        ·
          refine ⟨32016654229779229954959397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170755489225489226426450117 32016654229779229954959397)
          ·
            refine ⟨6003122668083605616554887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32016654229779229954959397 6003122668083605616554887)
            ·
              refine ⟨9004684002125408424832331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003122668083605616554887 9004684002125408424832331)
              ·
                refine ⟨13507026003188112637248497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004684002125408424832331 13507026003188112637248497)
                ·
                  refine ⟨10130269502391084477936373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13507026003188112637248497 10130269502391084477936373)
                  ·
                    refine ⟨949712765849164169806535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10130269502391084477936373 949712765849164169806535)
                    ·
                      rfl

theorem cell23_5548677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_5548677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548677 prefixEnd_5548677 := by exact prefixLift 5548677
  have htrace : WordTrace (prefixWord ++ tailWord_5548677) baseStart_5548677 baseEnd_5548677 := by
    simpa [prefixWord, tailWord_5548677, baseEnd_5548677] using wordTrace_append hprefix tailTrace_5548677
  have hstable : (prefixWord ++ tailWord_5548677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548677).length < 2 ^ (prefixWord ++ tailWord_5548677).sum := by decide
  have hdescent : baseEnd_5548677 < baseStart_5548677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548683 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_5548683 : Nat := 118140960795 + 5548683 * 2 ^ 59
def prefixEnd_5548683 : Nat := 4983230072969 + 3 ^ 40 * 5548683 * 2
def baseEnd_5548683 : Nat := 2849141378431419485944577

theorem tailTrace_5548683 : CollatzResearch.WordTrace tailWord_5548683 prefixEnd_5548683 2849141378431419485944577 := by
  unfold tailWord_5548683
  simp only [CollatzResearch.WordTrace]
  refine ⟨202377094957076605456066703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134918063304717736970711135 202377094957076605456066703)
  ·
    refine ⟨303565642435614908184100055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202377094957076605456066703 303565642435614908184100055)
    ·
      refine ⟨455348463653422362276150083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303565642435614908184100055 455348463653422362276150083)
      ·
        refine ⟨683022695480133543414225125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455348463653422362276150083 683022695480133543414225125)
        ·
          refine ⟨128066755402525039390167211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 683022695480133543414225125 128066755402525039390167211)
          ·
            refine ⟨192100133103787559085250817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128066755402525039390167211 192100133103787559085250817)
            ·
              refine ⟨144075099827840669313938113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192100133103787559085250817 144075099827840669313938113)
              ·
                refine ⟨108056324870880501985453585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144075099827840669313938113 108056324870880501985453585)
                ·
                  refine ⟨81042243653160376489090189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108056324870880501985453585 81042243653160376489090189)
                  ·
                    refine ⟨30390841369935141183408821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81042243653160376489090189 30390841369935141183408821)
                    ·
                      refine ⟨2849141378431419485944577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30390841369935141183408821 2849141378431419485944577)
                      ·
                        rfl

theorem cell23_5548683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_5548683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548683 prefixEnd_5548683 := by exact prefixLift 5548683
  have htrace : WordTrace (prefixWord ++ tailWord_5548683) baseStart_5548683 baseEnd_5548683 := by
    simpa [prefixWord, tailWord_5548683, baseEnd_5548683] using wordTrace_append hprefix tailTrace_5548683
  have hstable : (prefixWord ++ tailWord_5548683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548683).length < 2 ^ (prefixWord ++ tailWord_5548683).sum := by decide
  have hdescent : baseEnd_5548683 < baseStart_5548683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548717 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_5548717 : Nat := 118140960795 + 5548717 * 2 ^ 59
def prefixEnd_5548717 : Nat := 4983230072969 + 3 ^ 40 * 5548717 * 2
def baseEnd_5548717 : Nat := 2849158836773672352919421

theorem tailTrace_5548717 : CollatzResearch.WordTrace tailWord_5548717 prefixEnd_5548717 2849158836773672352919421 := by
  unfold tailWord_5548717
  simp only [CollatzResearch.WordTrace]
  refine ⟨202378335038953429262804405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134918890025968952841869603 202378335038953429262804405)
  ·
    refine ⟨18972968909901883993387913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202378335038953429262804405 18972968909901883993387913)
    ·
      refine ⟨14229726682426412995040935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18972968909901883993387913 14229726682426412995040935)
      ·
        refine ⟨21344590023639619492561403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14229726682426412995040935 21344590023639619492561403)
        ·
          refine ⟨32016885035459429238842105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21344590023639619492561403 32016885035459429238842105)
          ·
            refine ⟨24012663776594571929131579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32016885035459429238842105 24012663776594571929131579)
            ·
              refine ⟨36018995664891857893697369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24012663776594571929131579 36018995664891857893697369)
              ·
                refine ⟨27014246748668893420273027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36018995664891857893697369 27014246748668893420273027)
                ·
                  refine ⟨40521370123003340130409541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27014246748668893420273027 40521370123003340130409541)
                  ·
                    refine ⟨7597756898063126274451789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40521370123003340130409541 7597756898063126274451789)
                    ·
                      refine ⟨2849158836773672352919421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7597756898063126274451789 2849158836773672352919421)
                      ·
                        rfl

theorem cell23_5548717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_5548717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548717 prefixEnd_5548717 := by exact prefixLift 5548717
  have htrace : WordTrace (prefixWord ++ tailWord_5548717) baseStart_5548717 baseEnd_5548717 := by
    simpa [prefixWord, tailWord_5548717, baseEnd_5548717] using wordTrace_append hprefix tailTrace_5548717
  have hstable : (prefixWord ++ tailWord_5548717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548717).length < 2 ^ (prefixWord ++ tailWord_5548717).sum := by decide
  have hdescent : baseEnd_5548717 < baseStart_5548717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548730 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_5548730 : Nat := 118140960795 + 5548730 * 2 ^ 59
def prefixEnd_5548730 : Nat := 4983230072969 + 3 ^ 40 * 5548730 * 2
def baseEnd_5548730 : Nat := 2849165512022180802056861

theorem tailTrace_5548730 : CollatzResearch.WordTrace tailWord_5548730 prefixEnd_5548730 2849165512022180802056861 := by
  unfold tailWord_5548730
  simp only [CollatzResearch.WordTrace]
  refine ⟨50594702296976583120756911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134919206125270888322018429 50594702296976583120756911)
  ·
    refine ⟨75892053445464874681135367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50594702296976583120756911 75892053445464874681135367)
    ·
      refine ⟨113838080168197312021703051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75892053445464874681135367 113838080168197312021703051)
      ·
        refine ⟨170757120252295968032554577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113838080168197312021703051 170757120252295968032554577)
        ·
          refine ⟨128067840189221976024415933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170757120252295968032554577 128067840189221976024415933)
          ·
            refine ⟨48025440070958241009155975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128067840189221976024415933 48025440070958241009155975)
            ·
              refine ⟨72038160106437361513733963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48025440070958241009155975 72038160106437361513733963)
              ·
                refine ⟨108057240159656042270600945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72038160106437361513733963 108057240159656042270600945)
                ·
                  refine ⟨81042930119742031702950709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108057240159656042270600945 81042930119742031702950709)
                  ·
                    refine ⟨7597774698725815472151629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81042930119742031702950709 7597774698725815472151629)
                    ·
                      refine ⟨2849165512022180802056861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7597774698725815472151629 2849165512022180802056861)
                      ·
                        rfl

theorem cell23_5548730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_5548730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548730 prefixEnd_5548730 := by exact prefixLift 5548730
  have htrace : WordTrace (prefixWord ++ tailWord_5548730) baseStart_5548730 baseEnd_5548730 := by
    simpa [prefixWord, tailWord_5548730, baseEnd_5548730] using wordTrace_append hprefix tailTrace_5548730
  have hstable : (prefixWord ++ tailWord_5548730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548730).length < 2 ^ (prefixWord ++ tailWord_5548730).sum := by decide
  have hdescent : baseEnd_5548730 < baseStart_5548730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548780 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_5548780 : Nat := 118140960795 + 5548780 * 2 ^ 59
def prefixEnd_5548780 : Nat := 4983230072969 + 3 ^ 40 * 5548780 * 2
def baseEnd_5548780 : Nat := 949730395351635202143877

theorem tailTrace_5548780 : CollatzResearch.WordTrace tailWord_5548780 prefixEnd_5548780 949730395351635202143877 := by
  unfold tailWord_5548780
  simp only [CollatzResearch.WordTrace]
  refine ⟨101190316418862595511173897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134920421891816794014898529 101190316418862595511173897)
  ·
    refine ⟨75892737314146946633380423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101190316418862595511173897 75892737314146946633380423)
    ·
      refine ⟨113839105971220419950070635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75892737314146946633380423 113839105971220419950070635)
      ·
        refine ⟨170758658956830629925105953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113839105971220419950070635 170758658956830629925105953)
        ·
          refine ⟨128068994217622972443829465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170758658956830629925105953 128068994217622972443829465)
          ·
            refine ⟨96051745663217229332872099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128068994217622972443829465 96051745663217229332872099)
            ·
              refine ⟨144077618494825843999308149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96051745663217229332872099 144077618494825843999308149)
              ·
                refine ⟨13507276733889922874935139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144077618494825843999308149 13507276733889922874935139)
                ·
                  refine ⟨20260915100834884312402709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13507276733889922874935139 20260915100834884312402709)
                  ·
                    refine ⟨949730395351635202143877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20260915100834884312402709 949730395351635202143877)
                    ·
                      rfl

theorem cell23_5548780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_5548780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548780 prefixEnd_5548780 := by exact prefixLift 5548780
  have htrace : WordTrace (prefixWord ++ tailWord_5548780) baseStart_5548780 baseEnd_5548780 := by
    simpa [prefixWord, tailWord_5548780, baseEnd_5548780] using wordTrace_append hprefix tailTrace_5548780
  have hstable : (prefixWord ++ tailWord_5548780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548780).length < 2 ^ (prefixWord ++ tailWord_5548780).sum := by decide
  have hdescent : baseEnd_5548780 < baseStart_5548780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548834 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_5548834 : Nat := 118140960795 + 5548834 * 2 ^ 59
def prefixEnd_5548834 : Nat := 4983230072969 + 3 ^ 40 * 5548834 * 2
def baseEnd_5548834 : Nat := 2849218914010248395156383

theorem tailTrace_5548834 : CollatzResearch.WordTrace tailWord_5548834 prefixEnd_5548834 2849218914010248395156383 := by
  unfold tailWord_5548834
  simp only [CollatzResearch.WordTrace]
  refine ⟨50595650594882389561203389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134921734919686372163209037 50595650594882389561203389)
  ·
    refine ⟨18973368973080896085451271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50595650594882389561203389 18973368973080896085451271)
    ·
      refine ⟨28460053459621344128176907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18973368973080896085451271 28460053459621344128176907)
      ·
        refine ⟨42690080189432016192265361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28460053459621344128176907 42690080189432016192265361)
        ·
          refine ⟨32017560142074012144199021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42690080189432016192265361 32017560142074012144199021)
          ·
            refine ⟨12006585053277754554074633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32017560142074012144199021 12006585053277754554074633)
            ·
              refine ⟨9004938789958315915555975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12006585053277754554074633 9004938789958315915555975)
              ·
                refine ⟨13507408184937473873333963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004938789958315915555975 13507408184937473873333963)
                ·
                  refine ⟨20261112277406210810000945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13507408184937473873333963 20261112277406210810000945)
                  ·
                    refine ⟨15195834208054658107500709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20261112277406210810000945 15195834208054658107500709)
                    ·
                      refine ⟨2849218914010248395156383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15195834208054658107500709 2849218914010248395156383)
                      ·
                        rfl

theorem cell23_5548834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_5548834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548834 prefixEnd_5548834 := by exact prefixLift 5548834
  have htrace : WordTrace (prefixWord ++ tailWord_5548834) baseStart_5548834 baseEnd_5548834 := by
    simpa [prefixWord, tailWord_5548834, baseEnd_5548834] using wordTrace_append hprefix tailTrace_5548834
  have hstable : (prefixWord ++ tailWord_5548834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548834).length < 2 ^ (prefixWord ++ tailWord_5548834).sum := by decide
  have hdescent : baseEnd_5548834 < baseStart_5548834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548858 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3]
def baseStart_5548858 : Nat := 118140960795 + 5548858 * 2 ^ 59
def prefixEnd_5548858 : Nat := 4983230072969 + 3 ^ 40 * 5548858 * 2
def baseEnd_5548858 : Nat := 2849231237545956301256273

theorem tailTrace_5548858 : CollatzResearch.WordTrace tailWord_5548858 prefixEnd_5548858 2849231237545956301256273 := by
  unfold tailWord_5548858
  simp only [CollatzResearch.WordTrace]
  refine ⟨50595869432860652585921807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134922318487628406895791485 50595869432860652585921807)
  ·
    refine ⟨75893804149290978878882711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50595869432860652585921807 75893804149290978878882711)
    ·
      refine ⟨113840706223936468318324067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75893804149290978878882711 113840706223936468318324067)
      ·
        refine ⟨170761059335904702477486101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113840706223936468318324067 170761059335904702477486101)
        ·
          refine ⟨8004424656370532928632161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 170761059335904702477486101 8004424656370532928632161)
          ·
            refine ⟨6003318492277899696474121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8004424656370532928632161 6003318492277899696474121)
            ·
              refine ⟨4502488869208424772355591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6003318492277899696474121 4502488869208424772355591)
              ·
                refine ⟨6753733303812637158533387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502488869208424772355591 6753733303812637158533387)
                ·
                  refine ⟨10130599955718955737800081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6753733303812637158533387 10130599955718955737800081)
                  ·
                    refine ⟨7597949966789216803350061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10130599955718955737800081 7597949966789216803350061)
                    ·
                      refine ⟨2849231237545956301256273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7597949966789216803350061 2849231237545956301256273)
                      ·
                        rfl

theorem cell23_5548858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_5548858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548858 prefixEnd_5548858 := by exact prefixLift 5548858
  have htrace : WordTrace (prefixWord ++ tailWord_5548858) baseStart_5548858 baseEnd_5548858 := by
    simpa [prefixWord, tailWord_5548858, baseEnd_5548858] using wordTrace_append hprefix tailTrace_5548858
  have hstable : (prefixWord ++ tailWord_5548858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548858).length < 2 ^ (prefixWord ++ tailWord_5548858).sum := by decide
  have hdescent : baseEnd_5548858 < baseStart_5548858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548865 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5548865 : Nat := 118140960795 + 5548865 * 2 ^ 59
def prefixEnd_5548865 : Nat := 4983230072969 + 3 ^ 40 * 5548865 * 2
def baseEnd_5548865 : Nat := 949744943970179257956247

theorem tailTrace_5548865 : CollatzResearch.WordTrace tailWord_5548865 prefixEnd_5548865 949744943970179257956247 := by
  unfold tailWord_5548865
  simp only [CollatzResearch.WordTrace]
  refine ⟨202383733042417250539192049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134922488694944833692794699 202383733042417250539192049)
  ·
    refine ⟨151787799781812937904394037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202383733042417250539192049 151787799781812937904394037)
    ·
      refine ⟨14230106229544962928536941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151787799781812937904394037 14230106229544962928536941)
      ·
        refine ⟨5336289836079361098201353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14230106229544962928536941 5336289836079361098201353)
        ·
          refine ⟨4002217377059520823651015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5336289836079361098201353 4002217377059520823651015)
          ·
            refine ⟨6003326065589281235476523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002217377059520823651015 6003326065589281235476523)
            ·
              refine ⟨9004989098383921853214785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003326065589281235476523 9004989098383921853214785)
              ·
                refine ⟨6753741823787941389911089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9004989098383921853214785 6753741823787941389911089)
                ·
                  refine ⟨5065306367840956042433317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6753741823787941389911089 5065306367840956042433317)
                  ·
                    refine ⟨949744943970179257956247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065306367840956042433317 949744943970179257956247)
                    ·
                      rfl

theorem cell23_5548865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5548865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548865 prefixEnd_5548865 := by exact prefixLift 5548865
  have htrace : WordTrace (prefixWord ++ tailWord_5548865) baseStart_5548865 baseEnd_5548865 := by
    simpa [prefixWord, tailWord_5548865, baseEnd_5548865] using wordTrace_append hprefix tailTrace_5548865
  have hstable : (prefixWord ++ tailWord_5548865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548865).length < 2 ^ (prefixWord ++ tailWord_5548865).sum := by decide
  have hdescent : baseEnd_5548865 < baseStart_5548865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548887 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 2, 6]
def baseStart_5548887 : Nat := 118140960795 + 5548887 * 2 ^ 59
def prefixEnd_5548887 : Nat := 4983230072969 + 3 ^ 40 * 5548887 * 2
def baseEnd_5548887 : Nat := 949748709494978895931213

theorem tailTrace_5548887 : CollatzResearch.WordTrace tailWord_5548887 prefixEnd_5548887 949748709494978895931213 := by
  unfold tailWord_5548887
  simp only [CollatzResearch.WordTrace]
  refine ⟨202384535448337548296492915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134923023632225032197661943 202384535448337548296492915)
  ·
    refine ⟨303576803172506322444739373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202384535448337548296492915 303576803172506322444739373)
    ·
      refine ⟨113841301189689870916777265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303576803172506322444739373 113841301189689870916777265)
      ·
        refine ⟨85380975892267403187582949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113841301189689870916777265 85380975892267403187582949)
        ·
          refine ⟨16008932979800138097671803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85380975892267403187582949 16008932979800138097671803)
          ·
            refine ⟨24013399469700207146507705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16008932979800138097671803 24013399469700207146507705)
            ·
              refine ⟨18010049602275155359880779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24013399469700207146507705 18010049602275155359880779)
              ·
                refine ⟨27015074403412733039821169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18010049602275155359880779 27015074403412733039821169)
                ·
                  refine ⟨20261305802559549779865877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27015074403412733039821169 20261305802559549779865877)
                  ·
                    refine ⟨949748709494978895931213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20261305802559549779865877 949748709494978895931213)
                    ·
                      rfl

theorem cell23_5548887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_5548887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548887 prefixEnd_5548887 := by exact prefixLift 5548887
  have htrace : WordTrace (prefixWord ++ tailWord_5548887) baseStart_5548887 baseEnd_5548887 := by
    simpa [prefixWord, tailWord_5548887, baseEnd_5548887] using wordTrace_append hprefix tailTrace_5548887
  have hstable : (prefixWord ++ tailWord_5548887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548887).length < 2 ^ (prefixWord ++ tailWord_5548887).sum := by decide
  have hdescent : baseEnd_5548887 < baseStart_5548887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548927 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_5548927 : Nat := 118140960795 + 5548927 * 2 ^ 59
def prefixEnd_5548927 : Nat := 4983230072969 + 3 ^ 40 * 5548927 * 2
def baseEnd_5548927 : Nat := 2849266667711116531293455

theorem tailTrace_5548927 : CollatzResearch.WordTrace tailWord_5548927 prefixEnd_5548927 2849266667711116531293455 := by
  unfold tailWord_5548927
  simp only [CollatzResearch.WordTrace]
  refine ⟨202385994368192635127949035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134923996245461756751966023 202385994368192635127949035)
  ·
    refine ⟨303578991552288952691923553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202385994368192635127949035 303578991552288952691923553)
    ·
      refine ⟨227684243664216714518942665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303578991552288952691923553 227684243664216714518942665)
      ·
        refine ⟨170763182748162535889206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227684243664216714518942665 170763182748162535889206999)
        ·
          refine ⟨256144774122243803833810499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170763182748162535889206999 256144774122243803833810499)
          ·
            refine ⟨384217161183365705750715749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256144774122243803833810499 384217161183365705750715749)
            ·
              refine ⟨72040717721881069828259203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 384217161183365705750715749 72040717721881069828259203)
              ·
                refine ⟨108061076582821604742388805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72040717721881069828259203 108061076582821604742388805)
                ·
                  refine ⟨20261451859279050889197901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108061076582821604742388805 20261451859279050889197901)
                  ·
                    refine ⟨7598044447229644083449213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20261451859279050889197901 7598044447229644083449213)
                    ·
                      refine ⟨2849266667711116531293455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598044447229644083449213 2849266667711116531293455)
                      ·
                        rfl

theorem cell23_5548927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_5548927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548927 prefixEnd_5548927 := by exact prefixLift 5548927
  have htrace : WordTrace (prefixWord ++ tailWord_5548927) baseStart_5548927 baseEnd_5548927 := by
    simpa [prefixWord, tailWord_5548927, baseEnd_5548927] using wordTrace_append hprefix tailTrace_5548927
  have hstable : (prefixWord ++ tailWord_5548927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548927).length < 2 ^ (prefixWord ++ tailWord_5548927).sum := by decide
  have hdescent : baseEnd_5548927 < baseStart_5548927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548957 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5548957 : Nat := 118140960795 + 5548957 * 2 ^ 59
def prefixEnd_5548957 : Nat := 4983230072969 + 3 ^ 40 * 5548957 * 2
def baseEnd_5548957 : Nat := 2849282072130751413918317

theorem tailTrace_5548957 : CollatzResearch.WordTrace tailWord_5548957 prefixEnd_5548957 2849282072130751413918317 := by
  unfold tailWord_5548957
  simp only [CollatzResearch.WordTrace]
  refine ⟨202387088558083950251541125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134924725705389300167694083 202387088558083950251541125)
  ·
    refine ⟨37947579104640740672163961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202387088558083950251541125 37947579104640740672163961)
    ·
      refine ⟨28460684328480555504122971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37947579104640740672163961 28460684328480555504122971)
      ·
        refine ⟨42691026492720833256184457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28460684328480555504122971 42691026492720833256184457)
        ·
          refine ⟨32018269869540624942138343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42691026492720833256184457 32018269869540624942138343)
          ·
            refine ⟨48027404804310937413207515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32018269869540624942138343 48027404804310937413207515)
            ·
              refine ⟨72041107206466406119811273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48027404804310937413207515 72041107206466406119811273)
              ·
                refine ⟨54030830404849804589858455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72041107206466406119811273 54030830404849804589858455)
                ·
                  refine ⟨81046245607274706884787683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54030830404849804589858455 81046245607274706884787683)
                  ·
                    refine ⟨121569368410912060327181525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81046245607274706884787683 121569368410912060327181525)
                    ·
                      refine ⟨2849282072130751413918317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121569368410912060327181525 2849282072130751413918317)
                      ·
                        rfl

theorem cell23_5548957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5548957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548957 prefixEnd_5548957 := by exact prefixLift 5548957
  have htrace : WordTrace (prefixWord ++ tailWord_5548957) baseStart_5548957 baseEnd_5548957 := by
    simpa [prefixWord, tailWord_5548957, baseEnd_5548957] using wordTrace_append hprefix tailTrace_5548957
  have hstable : (prefixWord ++ tailWord_5548957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548957).length < 2 ^ (prefixWord ++ tailWord_5548957).sum := by decide
  have hdescent : baseEnd_5548957 < baseStart_5548957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548964 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_5548964 : Nat := 118140960795 + 5548964 * 2 ^ 59
def prefixEnd_5548964 : Nat := 4983230072969 + 3 ^ 40 * 5548964 * 2
def baseEnd_5548964 : Nat := 949761888831777628843595

theorem tailTrace_5548964 : CollatzResearch.WordTrace tailWord_5548964 prefixEnd_5548964 949761888831777628843595 := by
  unfold tailWord_5548964
  simp only [CollatzResearch.WordTrace]
  refine ⟨101193671934529295223522973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134924895912705726964697297 101193671934529295223522973)
  ·
    refine ⟨37947626975448485708821115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101193671934529295223522973 37947626975448485708821115)
    ·
      refine ⟨56921440463172728563231673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37947626975448485708821115 56921440463172728563231673)
      ·
        refine ⟨42691080347379546422423755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56921440463172728563231673 42691080347379546422423755)
        ·
          refine ⟨64036620521069319633635633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42691080347379546422423755 64036620521069319633635633)
          ·
            refine ⟨48027465390801989725226725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64036620521069319633635633 48027465390801989725226725)
            ·
              refine ⟨9005149760775373073480011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48027465390801989725226725 9005149760775373073480011)
              ·
                refine ⟨13507724641163059610220017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9005149760775373073480011 13507724641163059610220017)
                ·
                  refine ⟨10130793480872294707665013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13507724641163059610220017 10130793480872294707665013)
                  ·
                    refine ⟨949761888831777628843595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10130793480872294707665013 949761888831777628843595)
                    ·
                      rfl

theorem cell23_5548964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_5548964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548964 prefixEnd_5548964 := by exact prefixLift 5548964
  have htrace : WordTrace (prefixWord ++ tailWord_5548964) baseStart_5548964 baseEnd_5548964 := by
    simpa [prefixWord, tailWord_5548964, baseEnd_5548964] using wordTrace_append hprefix tailTrace_5548964
  have hstable : (prefixWord ++ tailWord_5548964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548964).length < 2 ^ (prefixWord ++ tailWord_5548964).sum := by decide
  have hdescent : baseEnd_5548964 < baseStart_5548964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5548984 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_5548984 : Nat := 118140960795 + 5548984 * 2 ^ 59
def prefixEnd_5548984 : Nat := 4983230072969 + 3 ^ 40 * 5548984 * 2
def baseEnd_5548984 : Nat := 2849295936108422808280693

theorem tailTrace_5548984 : CollatzResearch.WordTrace tailWord_5548984 prefixEnd_5548984 2849295936108422808280693 := by
  unfold tailWord_5548984
  simp only [CollatzResearch.WordTrace]
  refine ⟨101194036664493066931387003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134925382219324089241849337 101194036664493066931387003)
  ·
    refine ⟨151791054996739600397080505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101194036664493066931387003 151791054996739600397080505)
    ·
      refine ⟨113843291247554700297810379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151791054996739600397080505 113843291247554700297810379)
      ·
        refine ⟨170764936871332050446715569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113843291247554700297810379 170764936871332050446715569)
        ·
          refine ⟨128073702653499037835036677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170764936871332050446715569 128073702653499037835036677)
          ·
            refine ⟨24013819247531069594069377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128073702653499037835036677 24013819247531069594069377)
            ·
              refine ⟨18010364435648302195552033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24013819247531069594069377 18010364435648302195552033)
              ·
                refine ⟨13507773326736226646664025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18010364435648302195552033 13507773326736226646664025)
                ·
                  refine ⟨10130829995052169984998019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13507773326736226646664025 10130829995052169984998019)
                  ·
                    refine ⟨15196244992578254977497029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10130829995052169984998019 15196244992578254977497029)
                    ·
                      refine ⟨2849295936108422808280693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15196244992578254977497029 2849295936108422808280693)
                      ·
                        rfl

theorem cell23_5548984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_5548984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5548984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5548984 prefixEnd_5548984 := by exact prefixLift 5548984
  have htrace : WordTrace (prefixWord ++ tailWord_5548984) baseStart_5548984 baseEnd_5548984 := by
    simpa [prefixWord, tailWord_5548984, baseEnd_5548984] using wordTrace_append hprefix tailTrace_5548984
  have hstable : (prefixWord ++ tailWord_5548984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5548984).length < 2 ^ (prefixWord ++ tailWord_5548984).sum := by decide
  have hdescent : baseEnd_5548984 < baseStart_5548984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5548984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549004 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5549004 : Nat := 118140960795 + 5549004 * 2 ^ 59
def prefixEnd_5549004 : Nat := 4983230072969 + 3 ^ 40 * 5549004 * 2
def baseEnd_5549004 : Nat := 2849306205721512730030601

theorem tailTrace_5549004 : CollatzResearch.WordTrace tailWord_5549004 prefixEnd_5549004 2849306205721512730030601 := by
  unfold tailWord_5549004
  simp only [CollatzResearch.WordTrace]
  refine ⟨101194401394456838639251033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134925868525942451519001377 101194401394456838639251033)
  ·
    refine ⟨75895801045842628979438275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101194401394456838639251033 75895801045842628979438275)
    ·
      refine ⟨113843701568763943469157413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75895801045842628979438275 113843701568763943469157413)
      ·
        refine ⟨21345694044143239400467015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113843701568763943469157413 21345694044143239400467015)
        ·
          refine ⟨32018541066214859100700523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21345694044143239400467015 32018541066214859100700523)
          ·
            refine ⟨48027811599322288651050785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32018541066214859100700523 48027811599322288651050785)
            ·
              refine ⟨36020858699491716488288089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48027811599322288651050785 36020858699491716488288089)
              ·
                refine ⟨27015644024618787366216067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36020858699491716488288089 27015644024618787366216067)
                ·
                  refine ⟨40523466036928181049324101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27015644024618787366216067 40523466036928181049324101)
                  ·
                    refine ⟨7598149881924033946748269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40523466036928181049324101 7598149881924033946748269)
                    ·
                      refine ⟨2849306205721512730030601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598149881924033946748269 2849306205721512730030601)
                      ·
                        rfl

theorem cell23_5549004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5549004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549004 prefixEnd_5549004 := by exact prefixLift 5549004
  have htrace : WordTrace (prefixWord ++ tailWord_5549004) baseStart_5549004 baseEnd_5549004 := by
    simpa [prefixWord, tailWord_5549004, baseEnd_5549004] using wordTrace_append hprefix tailTrace_5549004
  have hstable : (prefixWord ++ tailWord_5549004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549004).length < 2 ^ (prefixWord ++ tailWord_5549004).sum := by decide
  have hdescent : baseEnd_5549004 < baseStart_5549004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549021 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_5549021 : Nat := 118140960795 + 5549021 * 2 ^ 59
def prefixEnd_5549021 : Nat := 4983230072969 + 3 ^ 40 * 5549021 * 2
def baseEnd_5549021 : Nat := 2849314934892639163518023

theorem tailTrace_5549021 : CollatzResearch.WordTrace tailWord_5549021 prefixEnd_5549021 2849314934892639163518023 := by
  unfold tailWord_5549021
  simp only [CollatzResearch.WordTrace]
  refine ⟨202389422829852089181870917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134926281886568059454580611 202389422829852089181870917)
  ·
    refine ⟨37948016780597266721600797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202389422829852089181870917 37948016780597266721600797)
    ·
      refine ⟨14230506292723975020600299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37948016780597266721600797 14230506292723975020600299)
      ·
        refine ⟨21345759439085962530900449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14230506292723975020600299 21345759439085962530900449)
        ·
          refine ⟨16009319579314471898175337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21345759439085962530900449 16009319579314471898175337)
          ·
            refine ⟨12006989684485853923631503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16009319579314471898175337 12006989684485853923631503)
            ·
              refine ⟨18010484526728780885447255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12006989684485853923631503 18010484526728780885447255)
              ·
                refine ⟨27015726790093171328170883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18010484526728780885447255 27015726790093171328170883)
                ·
                  refine ⟨40523590185139756992256325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27015726790093171328170883 40523590185139756992256325)
                  ·
                    refine ⟨7598173159713704436048061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40523590185139756992256325 7598173159713704436048061)
                    ·
                      refine ⟨2849314934892639163518023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598173159713704436048061 2849314934892639163518023)
                      ·
                        rfl

theorem cell23_5549021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_5549021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549021 prefixEnd_5549021 := by exact prefixLift 5549021
  have htrace : WordTrace (prefixWord ++ tailWord_5549021) baseStart_5549021 baseEnd_5549021 := by
    simpa [prefixWord, tailWord_5549021, baseEnd_5549021] using wordTrace_append hprefix tailTrace_5549021
  have hstable : (prefixWord ++ tailWord_5549021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549021).length < 2 ^ (prefixWord ++ tailWord_5549021).sum := by decide
  have hdescent : baseEnd_5549021 < baseStart_5549021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549041 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 6]
def baseStart_5549041 : Nat := 118140960795 + 5549041 * 2 ^ 59
def prefixEnd_5549041 : Nat := 4983230072969 + 3 ^ 40 * 5549041 * 2
def baseEnd_5549041 : Nat := 316591689389525453918659

theorem tailTrace_5549041 : CollatzResearch.WordTrace tailWord_5549041 prefixEnd_5549041 316591689389525453918659 := by
  unfold tailWord_5549041
  simp only [CollatzResearch.WordTrace]
  refine ⟨202390152289779632597598977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134926768193186421731732651 202390152289779632597598977)
  ·
    refine ⟨151792614217334724448199233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202390152289779632597598977 151792614217334724448199233)
    ·
      refine ⟨113844460663001043336149425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151792614217334724448199233 113844460663001043336149425)
      ·
        refine ⟨85383345497250782502112069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113844460663001043336149425 85383345497250782502112069)
        ·
          refine ⟨16009377280734521719146013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85383345497250782502112069 16009377280734521719146013)
          ·
            refine ⟨6003516480275445644679755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16009377280734521719146013 6003516480275445644679755)
            ·
              refine ⟨9005274720413168467019633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003516480275445644679755 9005274720413168467019633)
              ·
                refine ⟨6753956040309876350264725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9005274720413168467019633 6753956040309876350264725)
                ·
                  refine ⟨316591689389525453918659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6753956040309876350264725 316591689389525453918659)
                  ·
                    rfl

theorem cell23_5549041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 6].length) (baseStart_5549041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549041 prefixEnd_5549041 := by exact prefixLift 5549041
  have htrace : WordTrace (prefixWord ++ tailWord_5549041) baseStart_5549041 baseEnd_5549041 := by
    simpa [prefixWord, tailWord_5549041, baseEnd_5549041] using wordTrace_append hprefix tailTrace_5549041
  have hstable : (prefixWord ++ tailWord_5549041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549041).length < 2 ^ (prefixWord ++ tailWord_5549041).sum := by decide
  have hdescent : baseEnd_5549041 < baseStart_5549041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549045 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5549045 : Nat := 118140960795 + 5549045 * 2 ^ 59
def prefixEnd_5549045 : Nat := 4983230072969 + 3 ^ 40 * 5549045 * 2
def baseEnd_5549045 : Nat := 949775752809449023205971

theorem tailTrace_5549045 : CollatzResearch.WordTrace tailWord_5549045 prefixEnd_5549045 949775752809449023205971 := by
  unfold tailWord_5549045
  simp only [CollatzResearch.WordTrace]
  refine ⟨202390298181765141280744589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134926865454510094187163059 202390298181765141280744589)
  ·
    refine ⟨75896361818161927980279221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202390298181765141280744589 75896361818161927980279221)
    ·
      refine ⟨7115283920452680748151177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75896361818161927980279221 7115283920452680748151177)
      ·
        refine ⟨5336462940339510561113383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7115283920452680748151177 5336462940339510561113383)
        ·
          refine ⟨8004694410509265841670075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336462940339510561113383 8004694410509265841670075)
          ·
            refine ⟨12007041615763898762505113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8004694410509265841670075 12007041615763898762505113)
            ·
              refine ⟨9005281211822924071878835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12007041615763898762505113 9005281211822924071878835)
              ·
                refine ⟨13507921817734386107818253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9005281211822924071878835 13507921817734386107818253)
                ·
                  refine ⟨5065470681650394790431845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13507921817734386107818253 5065470681650394790431845)
                  ·
                    refine ⟨949775752809449023205971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065470681650394790431845 949775752809449023205971)
                    ·
                      rfl

theorem cell23_5549045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5549045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549045 prefixEnd_5549045 := by exact prefixLift 5549045
  have htrace : WordTrace (prefixWord ++ tailWord_5549045) baseStart_5549045 baseEnd_5549045 := by
    simpa [prefixWord, tailWord_5549045, baseEnd_5549045] using wordTrace_append hprefix tailTrace_5549045
  have hstable : (prefixWord ++ tailWord_5549045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549045).length < 2 ^ (prefixWord ++ tailWord_5549045).sum := by decide
  have hdescent : baseEnd_5549045 < baseStart_5549045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549091 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 4]
def baseStart_5549091 : Nat := 118140960795 + 5549091 * 2 ^ 59
def prefixEnd_5549091 : Nat := 4983230072969 + 3 ^ 40 * 5549091 * 2
def baseEnd_5549091 : Nat := 2849350878538453889642701

theorem tailTrace_5549091 : CollatzResearch.WordTrace tailWord_5549091 prefixEnd_5549091 2849350878538453889642701 := by
  unfold tailWord_5549091
  simp only [CollatzResearch.WordTrace]
  refine ⟨202391975939598491136919127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134927983959732327424612751 202391975939598491136919127)
  ·
    refine ⟨303587963909397736705378691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202391975939598491136919127 303587963909397736705378691)
    ·
      refine ⟨455381945864096605058068037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303587963909397736705378691 455381945864096605058068037)
      ·
        refine ⟨85384114849518113448387757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 455381945864096605058068037 85384114849518113448387757)
        ·
          refine ⟨32019043068569292543145409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85384114849518113448387757 32019043068569292543145409)
          ·
            refine ⟨24014282301426969407359057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32019043068569292543145409 24014282301426969407359057)
            ·
              refine ⟨18010711726070227055519293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24014282301426969407359057 18010711726070227055519293)
              ·
                refine ⟨6754016897276335145819735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18010711726070227055519293 6754016897276335145819735)
                ·
                  refine ⟨10131025345914502718729603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754016897276335145819735 10131025345914502718729603)
                  ·
                    refine ⟨15196538018871754078094405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10131025345914502718729603 15196538018871754078094405)
                    ·
                      refine ⟨2849350878538453889642701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15196538018871754078094405 2849350878538453889642701)
                      ·
                        rfl

theorem cell23_5549091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_5549091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549091 prefixEnd_5549091 := by exact prefixLift 5549091
  have htrace : WordTrace (prefixWord ++ tailWord_5549091) baseStart_5549091 baseEnd_5549091 := by
    simpa [prefixWord, tailWord_5549091, baseEnd_5549091] using wordTrace_append hprefix tailTrace_5549091
  have hstable : (prefixWord ++ tailWord_5549091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549091).length < 2 ^ (prefixWord ++ tailWord_5549091).sum := by decide
  have hdescent : baseEnd_5549091 < baseStart_5549091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549095 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5549095 : Nat := 118140960795 + 5549095 * 2 ^ 59
def prefixEnd_5549095 : Nat := 4983230072969 + 3 ^ 40 * 5549095 * 2
def baseEnd_5549095 : Nat := 2849352932461071873992683

theorem tailTrace_5549095 : CollatzResearch.WordTrace tailWord_5549095 prefixEnd_5549095 2849352932461071873992683 := by
  unfold tailWord_5549095
  simp only [CollatzResearch.WordTrace]
  refine ⟨202392121831583999820064739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134928081221055999880043159 202392121831583999820064739)
  ·
    refine ⟨303588182747375999730097109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202392121831583999820064739 303588182747375999730097109)
    ·
      refine ⟨7115348033141624993674151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 303588182747375999730097109 7115348033141624993674151)
      ·
        refine ⟨10673022049712437490511227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7115348033141624993674151 10673022049712437490511227)
        ·
          refine ⟨16009533074568656235766841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10673022049712437490511227 16009533074568656235766841)
          ·
            refine ⟨12007149805926492176825131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16009533074568656235766841 12007149805926492176825131)
            ·
              refine ⟨18010724708889738265237697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12007149805926492176825131 18010724708889738265237697)
              ·
                refine ⟨13508043531667303698928273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18010724708889738265237697 13508043531667303698928273)
                ·
                  refine ⟨10131032648750477774196205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13508043531667303698928273 10131032648750477774196205)
                  ·
                    refine ⟨3799137243281429165323577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10131032648750477774196205 3799137243281429165323577)
                    ·
                      refine ⟨2849352932461071873992683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799137243281429165323577 2849352932461071873992683)
                      ·
                        rfl

theorem cell23_5549095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5549095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549095 prefixEnd_5549095 := by exact prefixLift 5549095
  have htrace : WordTrace (prefixWord ++ tailWord_5549095) baseStart_5549095 baseEnd_5549095 := by
    simpa [prefixWord, tailWord_5549095, baseEnd_5549095] using wordTrace_append hprefix tailTrace_5549095
  have hstable : (prefixWord ++ tailWord_5549095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549095).length < 2 ^ (prefixWord ++ tailWord_5549095).sum := by decide
  have hdescent : baseEnd_5549095 < baseStart_5549095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549102 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_5549102 : Nat := 118140960795 + 5549102 * 2 ^ 59
def prefixEnd_5549102 : Nat := 4983230072969 + 3 ^ 40 * 5549102 * 2
def baseEnd_5549102 : Nat := 2849356526825653346605151

theorem tailTrace_5549102 : CollatzResearch.WordTrace tailWord_5549102 prefixEnd_5549102 2849356526825653346605151 := by
  unfold tailWord_5549102
  simp only [CollatzResearch.WordTrace]
  refine ⟨25299047142819830001946195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134928251428372426677046373 25299047142819830001946195)
  ·
    refine ⟨37948570714229745002919293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25299047142819830001946195 37948570714229745002919293)
    ·
      refine ⟨14230714017836154376094735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37948570714229745002919293 14230714017836154376094735)
      ·
        refine ⟨21346071026754231564142103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14230714017836154376094735 21346071026754231564142103)
        ·
          refine ⟨32019106540131347346213155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21346071026754231564142103 32019106540131347346213155)
          ·
            refine ⟨48028659810197021019319733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32019106540131347346213155 48028659810197021019319733)
            ·
              refine ⟨4502686857205970720561225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48028659810197021019319733 4502686857205970720561225)
              ·
                refine ⟨3377015142904478040420919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502686857205970720561225 3377015142904478040420919)
                ·
                  refine ⟨5065522714356717060631379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377015142904478040420919 5065522714356717060631379)
                  ·
                    refine ⟨7598284071535075590947069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5065522714356717060631379 7598284071535075590947069)
                    ·
                      refine ⟨2849356526825653346605151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598284071535075590947069 2849356526825653346605151)
                      ·
                        rfl

theorem cell23_5549102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_5549102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549102 prefixEnd_5549102 := by exact prefixLift 5549102
  have htrace : WordTrace (prefixWord ++ tailWord_5549102) baseStart_5549102 baseEnd_5549102 := by
    simpa [prefixWord, tailWord_5549102, baseEnd_5549102] using wordTrace_append hprefix tailTrace_5549102
  have hstable : (prefixWord ++ tailWord_5549102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549102).length < 2 ^ (prefixWord ++ tailWord_5549102).sum := by decide
  have hdescent : baseEnd_5549102 < baseStart_5549102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549141 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_5549141 : Nat := 118140960795 + 5549141 * 2 ^ 59
def prefixEnd_5549141 : Nat := 4983230072969 + 3 ^ 40 * 5549141 * 2
def baseEnd_5549141 : Nat := 2849376552571178694017471

theorem tailTrace_5549141 : CollatzResearch.WordTrace tailWord_5549141 prefixEnd_5549141 2849376552571178694017471 := by
  unfold tailWord_5549141
  simp only [CollatzResearch.WordTrace]
  refine ⟨202393799589417349676239277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134929199726278233117492851 202393799589417349676239277)
  ·
    refine ⟨75897674846031506128589729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202393799589417349676239277 75897674846031506128589729)
    ·
      refine ⟨56923256134523629596442297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75897674846031506128589729 56923256134523629596442297)
      ·
        refine ⟨42692442100892722197331723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56923256134523629596442297 42692442100892722197331723)
        ·
          refine ⟨64038663151339083295997585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42692442100892722197331723 64038663151339083295997585)
          ·
            refine ⟨48028997363504312471998189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64038663151339083295997585 48028997363504312471998189)
            ·
              refine ⟨18010874011314117176999321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48028997363504312471998189 18010874011314117176999321)
              ·
                refine ⟨13508155508485587882749491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18010874011314117176999321 13508155508485587882749491)
                ·
                  refine ⟨20262233262728381824124237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13508155508485587882749491 20262233262728381824124237)
                  ·
                    refine ⟨7598337473523143184046589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20262233262728381824124237 7598337473523143184046589)
                    ·
                      refine ⟨2849376552571178694017471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598337473523143184046589 2849376552571178694017471)
                      ·
                        rfl

theorem cell23_5549141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_5549141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549141 prefixEnd_5549141 := by exact prefixLift 5549141
  have htrace : WordTrace (prefixWord ++ tailWord_5549141) baseStart_5549141 baseEnd_5549141 := by
    simpa [prefixWord, tailWord_5549141, baseEnd_5549141] using wordTrace_append hprefix tailTrace_5549141
  have hstable : (prefixWord ++ tailWord_5549141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549141).length < 2 ^ (prefixWord ++ tailWord_5549141).sum := by decide
  have hdescent : baseEnd_5549141 < baseStart_5549141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549159 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_5549159 : Nat := 118140960795 + 5549159 * 2 ^ 59
def prefixEnd_5549159 : Nat := 4983230072969 + 3 ^ 40 * 5549159 * 2
def baseEnd_5549159 : Nat := 2849385795222959623592389

theorem tailTrace_5549159 : CollatzResearch.WordTrace tailWord_5549159 prefixEnd_5549159 2849385795222959623592389 := by
  unfold tailWord_5549159
  simp only [CollatzResearch.WordTrace]
  refine ⟨202394456103352138750394531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134929637402234759166929687 202394456103352138750394531)
  ·
    refine ⟨303591684155028208125591797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202394456103352138750394531 303591684155028208125591797)
    ·
      refine ⟨28461720389533894511774231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303591684155028208125591797 28461720389533894511774231)
      ·
        refine ⟨42692580584300841767661347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28461720389533894511774231 42692580584300841767661347)
        ·
          refine ⟨64038870876451262651492021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42692580584300841767661347 64038870876451262651492021)
          ·
            refine ⟨6003644144667305873577377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64038870876451262651492021 6003644144667305873577377)
            ·
              refine ⟨4502733108500479405183033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6003644144667305873577377 4502733108500479405183033)
              ·
                refine ⟨3377049831375359553887275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502733108500479405183033 3377049831375359553887275)
                ·
                  refine ⟨5065574747063039330830913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377049831375359553887275 5065574747063039330830913)
                  ·
                    refine ⟨3799181060297279498123185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5065574747063039330830913 3799181060297279498123185)
                    ·
                      refine ⟨2849385795222959623592389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799181060297279498123185 2849385795222959623592389)
                      ·
                        rfl

theorem cell23_5549159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_5549159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549159 prefixEnd_5549159 := by exact prefixLift 5549159
  have htrace : WordTrace (prefixWord ++ tailWord_5549159) baseStart_5549159 baseEnd_5549159 := by
    simpa [prefixWord, tailWord_5549159, baseEnd_5549159] using wordTrace_append hprefix tailTrace_5549159
  have hstable : (prefixWord ++ tailWord_5549159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549159).length < 2 ^ (prefixWord ++ tailWord_5549159).sum := by decide
  have hdescent : baseEnd_5549159 < baseStart_5549159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549164 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_5549164 : Nat := 118140960795 + 5549164 * 2 ^ 59
def prefixEnd_5549164 : Nat := 4983230072969 + 3 ^ 40 * 5549164 * 2
def baseEnd_5549164 : Nat := 2849388362626232104029865

theorem tailTrace_5549164 : CollatzResearch.WordTrace tailWord_5549164 prefixEnd_5549164 2849388362626232104029865 := by
  unfold tailWord_5549164
  simp only [CollatzResearch.WordTrace]
  refine ⟨101197319234167012302163273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134929758978889349736217697 101197319234167012302163273)
  ·
    refine ⟨75897989425625259226622455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101197319234167012302163273 75897989425625259226622455)
    ·
      refine ⟨113846984138437888839933683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75897989425625259226622455 113846984138437888839933683)
      ·
        refine ⟨170770476207656833259900525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113846984138437888839933683 170770476207656833259900525)
        ·
          refine ⟨64038928577871312472462697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170770476207656833259900525 64038928577871312472462697)
          ·
            refine ⟨48029196433403484354347023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64038928577871312472462697 48029196433403484354347023)
            ·
              refine ⟨72043794650105226531520535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48029196433403484354347023 72043794650105226531520535)
              ·
                refine ⟨108065691975157839797280803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72043794650105226531520535 108065691975157839797280803)
                ·
                  refine ⟨162098537962736759695921205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108065691975157839797280803 162098537962736759695921205)
                  ·
                    refine ⟨15196737934006571221492613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162098537962736759695921205 15196737934006571221492613)
                    ·
                      refine ⟨2849388362626232104029865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15196737934006571221492613 2849388362626232104029865)
                      ·
                        rfl

theorem cell23_5549164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_5549164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549164 prefixEnd_5549164 := by exact prefixLift 5549164
  have htrace : WordTrace (prefixWord ++ tailWord_5549164) baseStart_5549164 baseEnd_5549164 := by
    simpa [prefixWord, tailWord_5549164, baseEnd_5549164] using wordTrace_append hprefix tailTrace_5549164
  have hstable : (prefixWord ++ tailWord_5549164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549164).length < 2 ^ (prefixWord ++ tailWord_5549164).sum := by decide
  have hdescent : baseEnd_5549164 < baseStart_5549164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549182 : List Nat := [4, 2, 4, 1, 1, 1, 3, 7]
def baseStart_5549182 : Nat := 118140960795 + 5549182 * 2 ^ 59
def prefixEnd_5549182 : Nat := 4983230072969 + 3 ^ 40 * 5549182 * 2
def baseEnd_5549182 : Nat := 105533244639926408652029

theorem tailTrace_5549182 : CollatzResearch.WordTrace tailWord_5549182 prefixEnd_5549182 105533244639926408652029 := by
  unfold tailWord_5549182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25299411872783601709810225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134930196654845875785654533 25299411872783601709810225)
  ·
    refine ⟨18974558904587701282357669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25299411872783601709810225 18974558904587701282357669)
    ·
      refine ⟨3557729794610193990442063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18974558904587701282357669 3557729794610193990442063)
      ·
        refine ⟨5336594691915290985663095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557729794610193990442063 5336594691915290985663095)
        ·
          refine ⟨8004892037872936478494643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336594691915290985663095 8004892037872936478494643)
          ·
            refine ⟨12007338056809404717741965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8004892037872936478494643 12007338056809404717741965)
            ·
              refine ⟨4502751771303526769153237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12007338056809404717741965 4502751771303526769153237)
              ·
                refine ⟨105533244639926408652029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4502751771303526769153237 105533244639926408652029)
                ·
                  rfl

theorem cell23_5549182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_5549182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549182 prefixEnd_5549182 := by exact prefixLift 5549182
  have htrace : WordTrace (prefixWord ++ tailWord_5549182) baseStart_5549182 baseEnd_5549182 := by
    simpa [prefixWord, tailWord_5549182, baseEnd_5549182] using wordTrace_append hprefix tailTrace_5549182
  have hstable : (prefixWord ++ tailWord_5549182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549182).length < 2 ^ (prefixWord ++ tailWord_5549182).sum := by decide
  have hdescent : baseEnd_5549182 < baseStart_5549182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549184 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_5549184 : Nat := 118140960795 + 5549184 * 2 ^ 59
def prefixEnd_5549184 : Nat := 4983230072969 + 3 ^ 40 * 5549184 * 2
def baseEnd_5549184 : Nat := 2849398632239322025779773

theorem tailTrace_5549184 : CollatzResearch.WordTrace tailWord_5549184 prefixEnd_5549184 2849398632239322025779773 := by
  unfold tailWord_5549184
  simp only [CollatzResearch.WordTrace]
  refine ⟨101197683964130784010027303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134930245285507712013369737 101197683964130784010027303)
  ·
    refine ⟨151796525946196176015040955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101197683964130784010027303 151796525946196176015040955)
    ·
      refine ⟨227694788919294264022561433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151796525946196176015040955 227694788919294264022561433)
      ·
        refine ⟨170771091689470698016921075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227694788919294264022561433 170771091689470698016921075)
        ·
          refine ⟨256156637534206047025381613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170771091689470698016921075 256156637534206047025381613)
          ·
            refine ⟨96058739075327267634518105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256156637534206047025381613 96058739075327267634518105)
            ·
              refine ⟨72044054306495450725888579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96058739075327267634518105 72044054306495450725888579)
              ·
                refine ⟨108066081459743176088832869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72044054306495450725888579 108066081459743176088832869)
                ·
                  refine ⟨20262390273701845516656163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108066081459743176088832869 20262390273701845516656163)
                  ·
                    refine ⟨30393585410552768274984245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20262390273701845516656163 30393585410552768274984245)
                    ·
                      refine ⟨2849398632239322025779773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30393585410552768274984245 2849398632239322025779773)
                      ·
                        rfl

theorem cell23_5549184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_5549184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549184 prefixEnd_5549184 := by exact prefixLift 5549184
  have htrace : WordTrace (prefixWord ++ tailWord_5549184) baseStart_5549184 baseEnd_5549184 := by
    simpa [prefixWord, tailWord_5549184, baseEnd_5549184] using wordTrace_append hprefix tailTrace_5549184
  have hstable : (prefixWord ++ tailWord_5549184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549184).length < 2 ^ (prefixWord ++ tailWord_5549184).sum := by decide
  have hdescent : baseEnd_5549184 < baseStart_5549184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549202 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_5549202 : Nat := 118140960795 + 5549202 * 2 ^ 59
def prefixEnd_5549202 : Nat := 4983230072969 + 3 ^ 40 * 5549202 * 2
def baseEnd_5549202 : Nat := 2849407874891102955354691

theorem tailTrace_5549202 : CollatzResearch.WordTrace tailWord_5549202 prefixEnd_5549202 2849407874891102955354691 := by
  unfold tailWord_5549202
  simp only [CollatzResearch.WordTrace]
  refine ⟨50599006110549089273552465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134930682961464238062806573 50599006110549089273552465)
  ·
    refine ⟨37949254582911816955164349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50599006110549089273552465 37949254582911816955164349)
    ·
      refine ⟨14230970468591931358186631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37949254582911816955164349 14230970468591931358186631)
      ·
        refine ⟨21346455702887897037279947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14230970468591931358186631 21346455702887897037279947)
        ·
          refine ⟨32019683554331845555919921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21346455702887897037279947 32019683554331845555919921)
          ·
            refine ⟨24014762665748884166939941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32019683554331845555919921 24014762665748884166939941)
            ·
              refine ⟨4502767999827915781301239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24014762665748884166939941 4502767999827915781301239)
              ·
                refine ⟨6754151999741873671951859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502767999827915781301239 6754151999741873671951859)
                ·
                  refine ⟨10131227999612810507927789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754151999741873671951859 10131227999612810507927789)
                  ·
                    refine ⟨3799210499854803940472921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10131227999612810507927789 3799210499854803940472921)
                    ·
                      refine ⟨2849407874891102955354691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799210499854803940472921 2849407874891102955354691)
                      ·
                        rfl

theorem cell23_5549202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_5549202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549202 prefixEnd_5549202 := by exact prefixLift 5549202
  have htrace : WordTrace (prefixWord ++ tailWord_5549202) baseStart_5549202 baseEnd_5549202 := by
    simpa [prefixWord, tailWord_5549202, baseEnd_5549202] using wordTrace_append hprefix tailTrace_5549202
  have hstable : (prefixWord ++ tailWord_5549202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549202).length < 2 ^ (prefixWord ++ tailWord_5549202).sum := by decide
  have hdescent : baseEnd_5549202 < baseStart_5549202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549221 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 7]
def baseStart_5549221 : Nat := 118140960795 + 5549221 * 2 ^ 59
def prefixEnd_5549221 : Nat := 4983230072969 + 3 ^ 40 * 5549221 * 2
def baseEnd_5549221 : Nat := 316601959002615375668567

theorem tailTrace_5549221 : CollatzResearch.WordTrace tailWord_5549221 prefixEnd_5549221 316601959002615375668567 := by
  unfold tailWord_5549221
  simp only [CollatzResearch.WordTrace]
  refine ⟨202396717429127523339151517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134931144952751682226101011 202396717429127523339151517)
  ·
    refine ⟨75898769035922821252181819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202396717429127523339151517 75898769035922821252181819)
    ·
      refine ⟨113848153553884231878272729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75898769035922821252181819 113848153553884231878272729)
      ·
        refine ⟨85386115165413173908704547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113848153553884231878272729 85386115165413173908704547)
        ·
          refine ⟨128079172748119760863056821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85386115165413173908704547 128079172748119760863056821)
          ·
            refine ⟨12007422445136227580911577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128079172748119760863056821 12007422445136227580911577)
            ·
              refine ⟨9005566833852170685683683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12007422445136227580911577 9005566833852170685683683)
              ·
                refine ⟨13508350250778256028525525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9005566833852170685683683 13508350250778256028525525)
                ·
                  refine ⟨316601959002615375668567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13508350250778256028525525 316601959002615375668567)
                  ·
                    rfl

theorem cell23_5549221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_5549221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549221 prefixEnd_5549221 := by exact prefixLift 5549221
  have htrace : WordTrace (prefixWord ++ tailWord_5549221) baseStart_5549221 baseEnd_5549221 := by
    simpa [prefixWord, tailWord_5549221, baseEnd_5549221] using wordTrace_append hprefix tailTrace_5549221
  have hstable : (prefixWord ++ tailWord_5549221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549221).length < 2 ^ (prefixWord ++ tailWord_5549221).sum := by decide
  have hdescent : baseEnd_5549221 < baseStart_5549221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549231 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_5549231 : Nat := 118140960795 + 5549231 * 2 ^ 59
def prefixEnd_5549231 : Nat := 4983230072969 + 3 ^ 40 * 5549231 * 2
def baseEnd_5549231 : Nat := 2849422765830083341892057

theorem tailTrace_5549231 : CollatzResearch.WordTrace tailWord_5549231 prefixEnd_5549231 2849422765830083341892057 := by
  unfold tailWord_5549231
  simp only [CollatzResearch.WordTrace]
  refine ⟨202397082159091295047015547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134931388106060863364677031 202397082159091295047015547)
  ·
    refine ⟨303595623238636942570523321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202397082159091295047015547 303595623238636942570523321)
    ·
      refine ⟨227696717428977706927892491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303595623238636942570523321 227696717428977706927892491)
      ·
        refine ⟨341545076143466560391838737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227696717428977706927892491 341545076143466560391838737)
        ·
          refine ⟨256158807107599920293879053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341545076143466560391838737 256158807107599920293879053)
          ·
            refine ⟨96059552665349970110204645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256158807107599920293879053 96059552665349970110204645)
            ·
              refine ⟨18011166124753119395663371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96059552665349970110204645 18011166124753119395663371)
              ·
                refine ⟨27016749187129679093495057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18011166124753119395663371 27016749187129679093495057)
                ·
                  refine ⟨20262561890347259320121293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27016749187129679093495057 20262561890347259320121293)
                  ·
                    refine ⟨7598460708880222245045485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20262561890347259320121293 7598460708880222245045485)
                    ·
                      refine ⟨2849422765830083341892057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598460708880222245045485 2849422765830083341892057)
                      ·
                        rfl

theorem cell23_5549231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_5549231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549231 prefixEnd_5549231 := by exact prefixLift 5549231
  have htrace : WordTrace (prefixWord ++ tailWord_5549231) baseStart_5549231 baseEnd_5549231 := by
    simpa [prefixWord, tailWord_5549231, baseEnd_5549231] using wordTrace_append hprefix tailTrace_5549231
  have hstable : (prefixWord ++ tailWord_5549231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549231).length < 2 ^ (prefixWord ++ tailWord_5549231).sum := by decide
  have hdescent : baseEnd_5549231 < baseStart_5549231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549271 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_5549271 : Nat := 118140960795 + 5549271 * 2 ^ 59
def prefixEnd_5549271 : Nat := 4983230072969 + 3 ^ 40 * 5549271 * 2
def baseEnd_5549271 : Nat := 2849443305056263185391873

theorem tailTrace_5549271 : CollatzResearch.WordTrace tailWord_5549271 prefixEnd_5549271 2849443305056263185391873 := by
  unfold tailWord_5549271
  simp only [CollatzResearch.WordTrace]
  refine ⟨202398541078946381878471667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134932360719297587918981111 202398541078946381878471667)
  ·
    refine ⟨303597811618419572817707501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202398541078946381878471667 303597811618419572817707501)
    ·
      refine ⟨113849179356907339806640313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303597811618419572817707501 113849179356907339806640313)
      ·
        refine ⟨85386884517680504854980235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113849179356907339806640313 85386884517680504854980235)
        ·
          refine ⟨128080326776520757282470353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85386884517680504854980235 128080326776520757282470353)
          ·
            refine ⟨96060245082390567961852765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128080326776520757282470353 96060245082390567961852765)
            ·
              refine ⟨36022591905896462985694787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96060245082390567961852765 36022591905896462985694787)
              ·
                refine ⟨54033887858844694478542181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36022591905896462985694787 54033887858844694478542181)
                ·
                  refine ⟨10131353973533380214726659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54033887858844694478542181 10131353973533380214726659)
                  ·
                    refine ⟨15197030960300070322089989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10131353973533380214726659 15197030960300070322089989)
                    ·
                      refine ⟨2849443305056263185391873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15197030960300070322089989 2849443305056263185391873)
                      ·
                        rfl

theorem cell23_5549271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_5549271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549271 prefixEnd_5549271 := by exact prefixLift 5549271
  have htrace : WordTrace (prefixWord ++ tailWord_5549271) baseStart_5549271 baseEnd_5549271 := by
    simpa [prefixWord, tailWord_5549271, baseEnd_5549271] using wordTrace_append hprefix tailTrace_5549271
  have hstable : (prefixWord ++ tailWord_5549271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549271).length < 2 ^ (prefixWord ++ tailWord_5549271).sum := by decide
  have hdescent : baseEnd_5549271 < baseStart_5549271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549288 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_5549288 : Nat := 118140960795 + 5549288 * 2 ^ 59
def prefixEnd_5549288 : Nat := 4983230072969 + 3 ^ 40 * 5549288 * 2
def baseEnd_5549288 : Nat := 2849452034227389618879295

theorem tailTrace_5549288 : CollatzResearch.WordTrace tailWord_5549288 prefixEnd_5549288 2849452034227389618879295 := by
  unfold tailWord_5549288
  simp only [CollatzResearch.WordTrace]
  refine ⟨101199580559942396890920259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134932774079923195854560345 101199580559942396890920259)
  ·
    refine ⟨151799370839913595336380389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101199580559942396890920259 151799370839913595336380389)
    ·
      refine ⟨28462382032483799125571323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151799370839913595336380389 28462382032483799125571323)
      ·
        refine ⟨42693573048725698688356985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28462382032483799125571323 42693573048725698688356985)
        ·
          refine ⟨32020179786544274016267739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42693573048725698688356985 32020179786544274016267739)
          ·
            refine ⟨48030269679816411024401609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32020179786544274016267739 48030269679816411024401609)
            ·
              refine ⟨36022702259862308268301207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48030269679816411024401609 36022702259862308268301207)
              ·
                refine ⟨54034053389793462402451811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36022702259862308268301207 54034053389793462402451811)
                ·
                  refine ⟨81051080084690193603677717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54034053389793462402451811 81051080084690193603677717)
                  ·
                    refine ⟨3799269378969852825172393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81051080084690193603677717 3799269378969852825172393)
                    ·
                      refine ⟨2849452034227389618879295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799269378969852825172393 2849452034227389618879295)
                      ·
                        rfl

theorem cell23_5549288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_5549288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549288 prefixEnd_5549288 := by exact prefixLift 5549288
  have htrace : WordTrace (prefixWord ++ tailWord_5549288) baseStart_5549288 baseEnd_5549288 := by
    simpa [prefixWord, tailWord_5549288, baseEnd_5549288] using wordTrace_append hprefix tailTrace_5549288
  have hstable : (prefixWord ++ tailWord_5549288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549288).length < 2 ^ (prefixWord ++ tailWord_5549288).sum := by decide
  have hdescent : baseEnd_5549288 < baseStart_5549288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549365 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_5549365 : Nat := 118140960795 + 5549365 * 2 ^ 59
def prefixEnd_5549365 : Nat := 4983230072969 + 3 ^ 40 * 5549365 * 2
def baseEnd_5549365 : Nat := 2849491572237785817616441

theorem tailTrace_5549365 : CollatzResearch.WordTrace tailWord_5549365 prefixEnd_5549365 2849491572237785817616441 := by
  unfold tailWord_5549365
  simp only [CollatzResearch.WordTrace]
  refine ⟨202401969540605835932393549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134934646360403890621595699 202401969540605835932393549)
  ·
    refine ⟨75900738577727188474647581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202401969540605835932393549 75900738577727188474647581)
    ·
      refine ⟨28462776966647695677992843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75900738577727188474647581 28462776966647695677992843)
      ·
        refine ⟨42694165449971543516989265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28462776966647695677992843 42694165449971543516989265)
        ·
          refine ⟨32020624087478657637741949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42694165449971543516989265 32020624087478657637741949)
          ·
            refine ⟨12007734032804496614153231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32020624087478657637741949 12007734032804496614153231)
            ·
              refine ⟨18011601049206744921229847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12007734032804496614153231 18011601049206744921229847)
              ·
                refine ⟨27017401573810117381844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18011601049206744921229847 27017401573810117381844771)
                ·
                  refine ⟨40526102360715176072767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27017401573810117381844771 40526102360715176072767157)
                  ·
                    refine ⟨3799322096317047756821921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40526102360715176072767157 3799322096317047756821921)
                    ·
                      refine ⟨2849491572237785817616441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799322096317047756821921 2849491572237785817616441)
                      ·
                        rfl

theorem cell23_5549365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_5549365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549365 prefixEnd_5549365 := by exact prefixLift 5549365
  have htrace : WordTrace (prefixWord ++ tailWord_5549365) baseStart_5549365 baseEnd_5549365 := by
    simpa [prefixWord, tailWord_5549365, baseEnd_5549365] using wordTrace_append hprefix tailTrace_5549365
  have hstable : (prefixWord ++ tailWord_5549365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549365).length < 2 ^ (prefixWord ++ tailWord_5549365).sum := by decide
  have hdescent : baseEnd_5549365 < baseStart_5549365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549366 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5549366 : Nat := 118140960795 + 5549366 * 2 ^ 59
def prefixEnd_5549366 : Nat := 4983230072969 + 3 ^ 40 * 5549366 * 2
def baseEnd_5549366 : Nat := 949830695239480104567979

theorem tailTrace_5549366 : CollatzResearch.WordTrace tailWord_5549366 prefixEnd_5549366 949830695239480104567979 := by
  unfold tailWord_5549366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12650125375850138318948747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134934670675734808735453301 12650125375850138318948747)
  ·
    refine ⟨18975188063775207478423121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12650125375850138318948747 18975188063775207478423121)
    ·
      refine ⟨14231391047831405608817341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18975188063775207478423121 14231391047831405608817341)
      ·
        refine ⟨5336771642936777103306503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14231391047831405608817341 5336771642936777103306503)
        ·
          refine ⟨8005157464405165654959755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336771642936777103306503 8005157464405165654959755)
          ·
            refine ⟨12007736196607748482439633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8005157464405165654959755 12007736196607748482439633)
            ·
              refine ⟨9005802147455811361829725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12007736196607748482439633 9005802147455811361829725)
              ·
                refine ⟨3377175805295929260686147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9005802147455811361829725 3377175805295929260686147)
                ·
                  refine ⟨5065763707943893891029221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377175805295929260686147 5065763707943893891029221)
                  ·
                    refine ⟨949830695239480104567979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065763707943893891029221 949830695239480104567979)
                    ·
                      rfl

theorem cell23_5549366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5549366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549366 prefixEnd_5549366 := by exact prefixLift 5549366
  have htrace : WordTrace (prefixWord ++ tailWord_5549366) baseStart_5549366 baseEnd_5549366 := by
    simpa [prefixWord, tailWord_5549366, baseEnd_5549366] using wordTrace_append hprefix tailTrace_5549366
  have hstable : (prefixWord ++ tailWord_5549366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549366).length < 2 ^ (prefixWord ++ tailWord_5549366).sum := by decide
  have hdescent : baseEnd_5549366 < baseStart_5549366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549372 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_5549372 : Nat := 118140960795 + 5549372 * 2 ^ 59
def prefixEnd_5549372 : Nat := 4983230072969 + 3 ^ 40 * 5549372 * 2
def baseEnd_5549372 : Nat := 2849495166602367290228909

theorem tailTrace_5549372 : CollatzResearch.WordTrace tailWord_5549372 prefixEnd_5549372 2849495166602367290228909 := by
  unfold tailWord_5549372
  simp only [CollatzResearch.WordTrace]
  refine ⟨101201112425790238063949185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134934816567720317418598913 101201112425790238063949185)
  ·
    refine ⟨75900834319342678547961889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101201112425790238063949185 75900834319342678547961889)
    ·
      refine ⟨56925625739507008910971417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75900834319342678547961889 56925625739507008910971417)
      ·
        refine ⟨42694219304630256683228563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56925625739507008910971417 42694219304630256683228563)
        ·
          refine ⟨64041328956945385024842845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42694219304630256683228563 64041328956945385024842845)
          ·
            refine ⟨24015498358854519384316067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64041328956945385024842845 24015498358854519384316067)
            ·
              refine ⟨36023247538281779076474101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24015498358854519384316067 36023247538281779076474101)
              ·
                refine ⟨3377179456713916788419447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36023247538281779076474101 3377179456713916788419447)
                ·
                  refine ⟨5065769185070875182629171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377179456713916788419447 5065769185070875182629171)
                  ·
                    refine ⟨7598653777606312773943757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5065769185070875182629171 7598653777606312773943757)
                    ·
                      refine ⟨2849495166602367290228909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598653777606312773943757 2849495166602367290228909)
                      ·
                        rfl

theorem cell23_5549372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_5549372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549372 prefixEnd_5549372 := by exact prefixLift 5549372
  have htrace : WordTrace (prefixWord ++ tailWord_5549372) baseStart_5549372 baseEnd_5549372 := by
    simpa [prefixWord, tailWord_5549372, baseEnd_5549372] using wordTrace_append hprefix tailTrace_5549372
  have hstable : (prefixWord ++ tailWord_5549372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549372).length < 2 ^ (prefixWord ++ tailWord_5549372).sum := by decide
  have hdescent : baseEnd_5549372 < baseStart_5549372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549375 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 1, 5]
def baseStart_5549375 : Nat := 118140960795 + 5549375 * 2 ^ 59
def prefixEnd_5549375 : Nat := 4983230072969 + 3 ^ 40 * 5549375 * 2
def baseEnd_5549375 : Nat := 949832235681443592830465

theorem tailTrace_5549375 : CollatzResearch.WordTrace tailWord_5549375 prefixEnd_5549375 949832235681443592830465 := by
  unfold tailWord_5549375
  simp only [CollatzResearch.WordTrace]
  refine ⟨202402334270569607640257579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134934889513713071760171719 202402334270569607640257579)
  ·
    refine ⟨303603501405854411460386369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202402334270569607640257579 303603501405854411460386369)
    ·
      refine ⟨227702626054390808595289777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303603501405854411460386369 227702626054390808595289777)
      ·
        refine ⟨170776969540793106446467333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227702626054390808595289777 170776969540793106446467333)
        ·
          refine ⟨32020681788898707458712625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170776969540793106446467333 32020681788898707458712625)
          ·
            refine ⟨24015511341674030594034469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32020681788898707458712625 24015511341674030594034469)
            ·
              refine ⟨4502908376563880736381463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24015511341674030594034469 4502908376563880736381463)
              ·
                refine ⟨6754362564845821104572195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502908376563880736381463 6754362564845821104572195)
                ·
                  refine ⟨10131543847268731656858293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754362564845821104572195 10131543847268731656858293)
                  ·
                    refine ⟨949832235681443592830465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10131543847268731656858293 949832235681443592830465)
                    ·
                      rfl

theorem cell23_5549375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 5].length) (baseStart_5549375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549375 prefixEnd_5549375 := by exact prefixLift 5549375
  have htrace : WordTrace (prefixWord ++ tailWord_5549375) baseStart_5549375 baseEnd_5549375 := by
    simpa [prefixWord, tailWord_5549375, baseEnd_5549375] using wordTrace_append hprefix tailTrace_5549375
  have hstable : (prefixWord ++ tailWord_5549375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549375).length < 2 ^ (prefixWord ++ tailWord_5549375).sum := by decide
  have hdescent : baseEnd_5549375 < baseStart_5549375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549381 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_5549381 : Nat := 118140960795 + 5549381 * 2 ^ 59
def prefixEnd_5549381 : Nat := 4983230072969 + 3 ^ 40 * 5549381 * 2
def baseEnd_5549381 : Nat := 2849499787928257755016367

theorem tailTrace_5549381 : CollatzResearch.WordTrace tailWord_5549381 prefixEnd_5549381 2849499787928257755016367 := by
  unfold tailWord_5549381
  simp only [CollatzResearch.WordTrace]
  refine ⟨202402553108547870664975997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134935035405698580443317331 202402553108547870664975997)
  ·
    refine ⟨75900957415705451499365999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202402553108547870664975997 75900957415705451499365999)
    ·
      refine ⟨113851436123558177249048999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75900957415705451499365999 113851436123558177249048999)
      ·
        refine ⟨170777154185337265873573499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113851436123558177249048999 170777154185337265873573499)
        ·
          refine ⟨256165731278005898810360249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170777154185337265873573499 256165731278005898810360249)
          ·
            refine ⟨192124298458504424107770187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256165731278005898810360249 192124298458504424107770187)
            ·
              refine ⟨288186447687756636161655281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192124298458504424107770187 288186447687756636161655281)
              ·
                refine ⟨216139835765817477121241461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288186447687756636161655281 216139835765817477121241461)
                ·
                  refine ⟨20263109603045388480116387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216139835765817477121241461 20263109603045388480116387)
                  ·
                    refine ⟨30394664404568082720174581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20263109603045388480116387 30394664404568082720174581)
                    ·
                      refine ⟨2849499787928257755016367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30394664404568082720174581 2849499787928257755016367)
                      ·
                        rfl

theorem cell23_5549381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_5549381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549381 prefixEnd_5549381 := by exact prefixLift 5549381
  have htrace : WordTrace (prefixWord ++ tailWord_5549381) baseStart_5549381 baseEnd_5549381 := by
    simpa [prefixWord, tailWord_5549381, baseEnd_5549381] using wordTrace_append hprefix tailTrace_5549381
  have hstable : (prefixWord ++ tailWord_5549381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549381).length < 2 ^ (prefixWord ++ tailWord_5549381).sum := by decide
  have hdescent : baseEnd_5549381 < baseStart_5549381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549408 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_5549408 : Nat := 118140960795 + 5549408 * 2 ^ 59
def prefixEnd_5549408 : Nat := 4983230072969 + 3 ^ 40 * 5549408 * 2
def baseEnd_5549408 : Nat := 2849513651905929149378743

theorem tailTrace_5549408 : CollatzResearch.WordTrace tailWord_5549408 prefixEnd_5549408 2849513651905929149378743 := by
  unfold tailWord_5549408
  simp only [CollatzResearch.WordTrace]
  refine ⟨101201768939725027138104439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134935691919633369517472585 101201768939725027138104439)
  ·
    refine ⟨151802653409587540707156659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101201768939725027138104439 151802653409587540707156659)
    ·
      refine ⟨227703980114381311060734989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151802653409587540707156659 227703980114381311060734989)
      ·
        refine ⟨85388992542892991647775621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227703980114381311060734989 85388992542892991647775621)
        ·
          refine ⟨16010436101792435933957929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85388992542892991647775621 16010436101792435933957929)
          ·
            refine ⟨12007827076344326950468447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16010436101792435933957929 12007827076344326950468447)
            ·
              refine ⟨18011740614516490425702671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12007827076344326950468447 18011740614516490425702671)
              ·
                refine ⟨27017610921774735638554007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18011740614516490425702671 27017610921774735638554007)
                ·
                  refine ⟨40526416382662103457831011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27017610921774735638554007 40526416382662103457831011)
                  ·
                    refine ⟨60789624573993155186746517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40526416382662103457831011 60789624573993155186746517)
                    ·
                      refine ⟨2849513651905929149378743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60789624573993155186746517 2849513651905929149378743)
                      ·
                        rfl

theorem cell23_5549408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_5549408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549408 prefixEnd_5549408 := by exact prefixLift 5549408
  have htrace : WordTrace (prefixWord ++ tailWord_5549408) baseStart_5549408 baseEnd_5549408 := by
    simpa [prefixWord, tailWord_5549408, baseEnd_5549408] using wordTrace_append hprefix tailTrace_5549408
  have hstable : (prefixWord ++ tailWord_5549408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549408).length < 2 ^ (prefixWord ++ tailWord_5549408).sum := by decide
  have hdescent : baseEnd_5549408 < baseStart_5549408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549412 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_5549412 : Nat := 118140960795 + 5549412 * 2 ^ 59
def prefixEnd_5549412 : Nat := 4983230072969 + 3 ^ 40 * 5549412 * 2
def baseEnd_5549412 : Nat := 2849515705828547133728725

theorem tailTrace_5549412 : CollatzResearch.WordTrace tailWord_5549412 prefixEnd_5549412 2849515705828547133728725 := by
  unfold tailWord_5549412
  simp only [CollatzResearch.WordTrace]
  refine ⟨101201841885717781479677245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134935789180957041972902993 101201841885717781479677245)
  ·
    refine ⟨37950690707144168054878967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101201841885717781479677245 37950690707144168054878967)
    ·
      refine ⟨56926036060716252082318451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37950690707144168054878967 56926036060716252082318451)
      ·
        refine ⟨85389054091074378123477677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56926036060716252082318451 85389054091074378123477677)
        ·
          refine ⟨32020895284152891796304129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85389054091074378123477677 32020895284152891796304129)
          ·
            refine ⟨24015671463114668847228097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32020895284152891796304129 24015671463114668847228097)
            ·
              refine ⟨18011753597336001635421073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24015671463114668847228097 18011753597336001635421073)
              ·
                refine ⟨13508815198002001226565805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18011753597336001635421073 13508815198002001226565805)
                ·
                  refine ⟨5065805699250750459962177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13508815198002001226565805 5065805699250750459962177)
                  ·
                    refine ⟨3799354274438062844971633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5065805699250750459962177 3799354274438062844971633)
                    ·
                      refine ⟨2849515705828547133728725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799354274438062844971633 2849515705828547133728725)
                      ·
                        rfl

theorem cell23_5549412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_5549412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549412 prefixEnd_5549412 := by exact prefixLift 5549412
  have htrace : WordTrace (prefixWord ++ tailWord_5549412) baseStart_5549412 baseEnd_5549412 := by
    simpa [prefixWord, tailWord_5549412, baseEnd_5549412] using wordTrace_append hprefix tailTrace_5549412
  have hstable : (prefixWord ++ tailWord_5549412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549412).length < 2 ^ (prefixWord ++ tailWord_5549412).sum := by decide
  have hdescent : baseEnd_5549412 < baseStart_5549412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549445 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_5549445 : Nat := 118140960795 + 5549445 * 2 ^ 59
def prefixEnd_5549445 : Nat := 4983230072969 + 3 ^ 40 * 5549445 * 2
def baseEnd_5549445 : Nat := 2849532650690145504616073

theorem tailTrace_5549445 : CollatzResearch.WordTrace tailWord_5549445 prefixEnd_5549445 2849532650690145504616073 := by
  unfold tailWord_5549445
  simp only [CollatzResearch.WordTrace]
  refine ⟨202404887380316009595305789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134936591586877339730203859 202404887380316009595305789)
  ·
    refine ⟨75901832767618503598239671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202404887380316009595305789 75901832767618503598239671)
    ·
      refine ⟨113852749151427755397359507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75901832767618503598239671 113852749151427755397359507)
      ·
        refine ⟨170779123727141633096039261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113852749151427755397359507 170779123727141633096039261)
        ·
          refine ⟨64042171397678112411014723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170779123727141633096039261 64042171397678112411014723)
          ·
            refine ⟨96063257096517168616522085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64042171397678112411014723 96063257096517168616522085)
            ·
              refine ⟨18011860705596969115597891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96063257096517168616522085 18011860705596969115597891)
              ·
                refine ⟨27017791058395453673396837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18011860705596969115597891 27017791058395453673396837)
                ·
                  refine ⟨5065835823449147563761907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27017791058395453673396837 5065835823449147563761907)
                  ·
                    refine ⟨7598753735173721345642861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5065835823449147563761907 7598753735173721345642861)
                    ·
                      refine ⟨2849532650690145504616073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7598753735173721345642861 2849532650690145504616073)
                      ·
                        rfl

theorem cell23_5549445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_5549445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549445 prefixEnd_5549445 := by exact prefixLift 5549445
  have htrace : WordTrace (prefixWord ++ tailWord_5549445) baseStart_5549445 baseEnd_5549445 := by
    simpa [prefixWord, tailWord_5549445, baseEnd_5549445] using wordTrace_append hprefix tailTrace_5549445
  have hstable : (prefixWord ++ tailWord_5549445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549445).length < 2 ^ (prefixWord ++ tailWord_5549445).sum := by decide
  have hdescent : baseEnd_5549445 < baseStart_5549445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549489 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 1, 3, 2]
def baseStart_5549489 : Nat := 118140960795 + 5549489 * 2 ^ 59
def prefixEnd_5549489 : Nat := 4983230072969 + 3 ^ 40 * 5549489 * 2
def baseEnd_5549489 : Nat := 2849555243838943332465871

theorem tailTrace_5549489 : CollatzResearch.WordTrace tailWord_5549489 prefixEnd_5549489 2849555243838943332465871 := by
  unfold tailWord_5549489
  simp only [CollatzResearch.WordTrace]
  refine ⟨202406492192156605109907521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134937661461437736739938347 202406492192156605109907521)
  ·
    refine ⟨151804869144117453832430641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202406492192156605109907521 151804869144117453832430641)
    ·
      refine ⟨113853651858088090374322981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151804869144117453832430641 113853651858088090374322981)
      ·
        refine ⟨21347559723391516945185559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113853651858088090374322981 21347559723391516945185559)
        ·
          refine ⟨32021339585087275417778339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21347559723391516945185559 32021339585087275417778339)
          ·
            refine ⟨48032009377630913126667509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32021339585087275417778339 48032009377630913126667509)
            ·
              refine ⟨4503000879152898105625079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48032009377630913126667509 4503000879152898105625079)
              ·
                refine ⟨6754501318729347158437619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503000879152898105625079 6754501318729347158437619)
                ·
                  refine ⟨10131751978094020737656429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754501318729347158437619 10131751978094020737656429)
                  ·
                    refine ⟨3799406991785257776621161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10131751978094020737656429 3799406991785257776621161)
                    ·
                      refine ⟨2849555243838943332465871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799406991785257776621161 2849555243838943332465871)
                      ·
                        rfl

theorem cell23_5549489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_5549489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549489 prefixEnd_5549489 := by exact prefixLift 5549489
  have htrace : WordTrace (prefixWord ++ tailWord_5549489) baseStart_5549489 baseEnd_5549489 := by
    simpa [prefixWord, tailWord_5549489, baseEnd_5549489] using wordTrace_append hprefix tailTrace_5549489
  have hstable : (prefixWord ++ tailWord_5549489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549489).length < 2 ^ (prefixWord ++ tailWord_5549489).sum := by decide
  have hdescent : baseEnd_5549489 < baseStart_5549489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549548 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_5549548 : Nat := 118140960795 + 5549548 * 2 ^ 59
def prefixEnd_5549548 : Nat := 4983230072969 + 3 ^ 40 * 5549548 * 2
def baseEnd_5549548 : Nat := 2849585539197558601628099

theorem tailTrace_5549548 : CollatzResearch.WordTrace tailWord_5549548 prefixEnd_5549548 2849585539197558601628099 := by
  unfold tailWord_5549548
  simp only [CollatzResearch.WordTrace]
  refine ⟨101204322049471429093152649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134939096065961905457536865 101204322049471429093152649)
  ·
    refine ⟨75903241537103571819864487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101204322049471429093152649 75903241537103571819864487)
    ·
      refine ⟨113854862305655357729796731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75903241537103571819864487 113854862305655357729796731)
      ·
        refine ⟨170782293458483036594695097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113854862305655357729796731 170782293458483036594695097)
        ·
          refine ⟨128086720093862277446021323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170782293458483036594695097 128086720093862277446021323)
          ·
            refine ⟨192130080140793416169031985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128086720093862277446021323 192130080140793416169031985)
            ·
              refine ⟨144097560105595062126773989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192130080140793416169031985 144097560105595062126773989)
              ·
                refine ⟨27018292519799074148770123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144097560105595062126773989 27018292519799074148770123)
                ·
                  refine ⟨40527438779698611223155185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27018292519799074148770123 40527438779698611223155185)
                  ·
                    refine ⟨30395579084773958417366389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40527438779698611223155185 30395579084773958417366389)
                    ·
                      refine ⟨2849585539197558601628099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30395579084773958417366389 2849585539197558601628099)
                      ·
                        rfl

theorem cell23_5549548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_5549548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549548 prefixEnd_5549548 := by exact prefixLift 5549548
  have htrace : WordTrace (prefixWord ++ tailWord_5549548) baseStart_5549548 baseEnd_5549548 := by
    simpa [prefixWord, tailWord_5549548, baseEnd_5549548] using wordTrace_append hprefix tailTrace_5549548
  have hstable : (prefixWord ++ tailWord_5549548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549548).length < 2 ^ (prefixWord ++ tailWord_5549548).sum := by decide
  have hdescent : baseEnd_5549548 < baseStart_5549548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549575 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5549575 : Nat := 118140960795 + 5549575 * 2 ^ 59
def prefixEnd_5549575 : Nat := 4983230072969 + 3 ^ 40 * 5549575 * 2
def baseEnd_5549575 : Nat := 2849599403175229995990475

theorem tailTrace_5549575 : CollatzResearch.WordTrace tailWord_5549575 prefixEnd_5549575 2849599403175229995990475 := by
  unfold tailWord_5549575
  simp only [CollatzResearch.WordTrace]
  refine ⟨202409628869845041797538179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134939752579896694531692119 202409628869845041797538179)
  ·
    refine ⟨303614443304767562696307269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202409628869845041797538179 303614443304767562696307269)
    ·
      refine ⟨56927708119643918005557613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303614443304767562696307269 56927708119643918005557613)
      ·
        refine ⟨21347890544866469252084105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56927708119643918005557613 21347890544866469252084105)
        ·
          refine ⟨16010917908649851939063079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21347890544866469252084105 16010917908649851939063079)
          ·
            refine ⟨24016376862974777908594619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16010917908649851939063079 24016376862974777908594619)
            ·
              refine ⟨36024565294462166862891929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24016376862974777908594619 36024565294462166862891929)
              ·
                refine ⟨27018423970846625147168947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36024565294462166862891929 27018423970846625147168947)
                ·
                  refine ⟨40527635956269937720753421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27018423970846625147168947 40527635956269937720753421)
                  ·
                    refine ⟨15197863483601226645282533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40527635956269937720753421 15197863483601226645282533)
                    ·
                      refine ⟨2849599403175229995990475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15197863483601226645282533 2849599403175229995990475)
                      ·
                        rfl

theorem cell23_5549575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5549575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549575 prefixEnd_5549575 := by exact prefixLift 5549575
  have htrace : WordTrace (prefixWord ++ tailWord_5549575) baseStart_5549575 baseEnd_5549575 := by
    simpa [prefixWord, tailWord_5549575, baseEnd_5549575] using wordTrace_append hprefix tailTrace_5549575
  have hstable : (prefixWord ++ tailWord_5549575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549575).length < 2 ^ (prefixWord ++ tailWord_5549575).sum := by decide
  have hdescent : baseEnd_5549575 < baseStart_5549575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549585 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 3, 4]
def baseStart_5549585 : Nat := 118140960795 + 5549585 * 2 ^ 59
def prefixEnd_5549585 : Nat := 4983230072969 + 3 ^ 40 * 5549585 * 2
def baseEnd_5549585 : Nat := 949868179327258318955143

theorem tailTrace_5549585 : CollatzResearch.WordTrace tailWord_5549585 prefixEnd_5549585 949868179327258318955143 := by
  unfold tailWord_5549585
  simp only [CollatzResearch.WordTrace]
  refine ⟨202409993599808813505402209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134939995733205875670268139 202409993599808813505402209)
  ·
    refine ⟨151807495199856610129051657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202409993599808813505402209 151807495199856610129051657)
    ·
      refine ⟨113855621399892457596788743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151807495199856610129051657 113855621399892457596788743)
      ·
        refine ⟨170783432099838686395183115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113855621399892457596788743 170783432099838686395183115)
        ·
          refine ⟨256175148149758029592774673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170783432099838686395183115 256175148149758029592774673)
          ·
            refine ⟨192131361112318522194581005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256175148149758029592774673 192131361112318522194581005)
            ·
              refine ⟨72049260417119445822967877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192131361112318522194581005 72049260417119445822967877)
              ·
                refine ⟨13509236328209896091806477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72049260417119445822967877 13509236328209896091806477)
                ·
                  refine ⟨5065963623078711034427429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13509236328209896091806477 5065963623078711034427429)
                  ·
                    refine ⟨949868179327258318955143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065963623078711034427429 949868179327258318955143)
                    ·
                      rfl

theorem cell23_5549585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_5549585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549585 prefixEnd_5549585 := by exact prefixLift 5549585
  have htrace : WordTrace (prefixWord ++ tailWord_5549585) baseStart_5549585 baseEnd_5549585 := by
    simpa [prefixWord, tailWord_5549585, baseEnd_5549585] using wordTrace_append hprefix tailTrace_5549585
  have hstable : (prefixWord ++ tailWord_5549585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549585).length < 2 ^ (prefixWord ++ tailWord_5549585).sum := by decide
  have hdescent : baseEnd_5549585 < baseStart_5549585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549642 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_5549642 : Nat := 118140960795 + 5549642 * 2 ^ 59
def prefixEnd_5549642 : Nat := 4983230072969 + 3 ^ 40 * 5549642 * 2
def baseEnd_5549642 : Nat := 2849633806379081233852667

theorem tailTrace_5549642 : CollatzResearch.WordTrace tailWord_5549642 prefixEnd_5549642 2849633806379081233852667 := by
  unfold tailWord_5549642
  simp only [CollatzResearch.WordTrace]
  refine ⟨50603018140150578060056795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134941381707068208160151453 50603018140150578060056795)
  ·
    refine ⟨75904527210225867090085193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50603018140150578060056795 75904527210225867090085193)
    ·
      refine ⟨56928395407669400317563895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75904527210225867090085193 56928395407669400317563895)
      ·
        refine ⟨85392593111504100476345843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56928395407669400317563895 85392593111504100476345843)
        ·
          refine ⟨128088889667256150714518765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85392593111504100476345843 128088889667256150714518765)
          ·
            refine ⟨48033333625221056517944537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128088889667256150714518765 48033333625221056517944537)
            ·
              refine ⟨36025000218915792388458403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48033333625221056517944537 36025000218915792388458403)
              ·
                refine ⟨54037500328373688582687605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36025000218915792388458403 54037500328373688582687605)
                ·
                  refine ⟨5066015655785033304626963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54037500328373688582687605 5066015655785033304626963)
                  ·
                    refine ⟨7599023483677549956940445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5066015655785033304626963 7599023483677549956940445)
                    ·
                      refine ⟨2849633806379081233852667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7599023483677549956940445 2849633806379081233852667)
                      ·
                        rfl

theorem cell23_5549642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_5549642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549642 prefixEnd_5549642 := by exact prefixLift 5549642
  have htrace : WordTrace (prefixWord ++ tailWord_5549642) baseStart_5549642 baseEnd_5549642 := by
    simpa [prefixWord, tailWord_5549642, baseEnd_5549642] using wordTrace_append hprefix tailTrace_5549642
  have hstable : (prefixWord ++ tailWord_5549642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549642).length < 2 ^ (prefixWord ++ tailWord_5549642).sum := by decide
  have hdescent : baseEnd_5549642 < baseStart_5549642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549669 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 2, 3, 2]
def baseStart_5549669 : Nat := 118140960795 + 5549669 * 2 ^ 59
def prefixEnd_5549669 : Nat := 4983230072969 + 3 ^ 40 * 5549669 * 2
def baseEnd_5549669 : Nat := 2849647670356752628215043

theorem tailTrace_5549669 : CollatzResearch.WordTrace tailWord_5549669 prefixEnd_5549669 2849647670356752628215043 := by
  unfold tailWord_5549669
  simp only [CollatzResearch.WordTrace]
  refine ⟨202413057331504495851460061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134942038221002997234306707 202413057331504495851460061)
  ·
    refine ⟨75904896499314185944297523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202413057331504495851460061 75904896499314185944297523)
    ·
      refine ⟨113857344748971278916446285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75904896499314185944297523 113857344748971278916446285)
      ·
        refine ⟨42696504280864229593667357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113857344748971278916446285 42696504280864229593667357)
        ·
          refine ⟨16011189105324086097625259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42696504280864229593667357 16011189105324086097625259)
          ·
            refine ⟨24016783657986129146437889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16011189105324086097625259 24016783657986129146437889)
            ·
              refine ⟨18012587743489596859828417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24016783657986129146437889 18012587743489596859828417)
              ·
                refine ⟨13509440807617197644871313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18012587743489596859828417 13509440807617197644871313)
                ·
                  refine ⟨10132080605712898233653485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13509440807617197644871313 10132080605712898233653485)
                  ·
                    refine ⟨3799530227142336837620057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10132080605712898233653485 3799530227142336837620057)
                    ·
                      refine ⟨2849647670356752628215043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799530227142336837620057 2849647670356752628215043)
                      ·
                        rfl

theorem cell23_5549669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_5549669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549669 prefixEnd_5549669 := by exact prefixLift 5549669
  have htrace : WordTrace (prefixWord ++ tailWord_5549669) baseStart_5549669 baseEnd_5549669 := by
    simpa [prefixWord, tailWord_5549669, baseEnd_5549669] using wordTrace_append hprefix tailTrace_5549669
  have hstable : (prefixWord ++ tailWord_5549669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549669).length < 2 ^ (prefixWord ++ tailWord_5549669).sum := by decide
  have hdescent : baseEnd_5549669 < baseStart_5549669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549675 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 8, 4]
def baseStart_5549675 : Nat := 118140960795 + 5549675 * 2 ^ 59
def prefixEnd_5549675 : Nat := 4983230072969 + 3 ^ 40 * 5549675 * 2
def baseEnd_5549675 : Nat := 949883583746893201580005

theorem tailTrace_5549675 : CollatzResearch.WordTrace tailWord_5549675 prefixEnd_5549675 949883583746893201580005 := by
  unfold tailWord_5549675
  simp only [CollatzResearch.WordTrace]
  refine ⟨202413276169482758876178479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134942184112988505917452319 202413276169482758876178479)
  ·
    refine ⟨303619914254224138314267719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202413276169482758876178479 303619914254224138314267719)
    ·
      refine ⟨455429871381336207471401579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303619914254224138314267719 455429871381336207471401579)
      ·
        refine ⟨683144807072004311207102369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455429871381336207471401579 683144807072004311207102369)
        ·
          refine ⟨512358605304003233405326777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683144807072004311207102369 512358605304003233405326777)
          ·
            refine ⟨384268953978002425053995083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512358605304003233405326777 384268953978002425053995083)
            ·
              refine ⟨576403430967003637580992625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384268953978002425053995083 576403430967003637580992625)
              ·
                refine ⟨432302573225252728185744469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576403430967003637580992625 432302573225252728185744469)
                ·
                  refine ⟨5066045779983430408426693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 432302573225252728185744469 5066045779983430408426693)
                  ·
                    refine ⟨949883583746893201580005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066045779983430408426693 949883583746893201580005)
                    ·
                      rfl

theorem cell23_5549675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 4].length) (baseStart_5549675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549675 prefixEnd_5549675 := by exact prefixLift 5549675
  have htrace : WordTrace (prefixWord ++ tailWord_5549675) baseStart_5549675 baseEnd_5549675 := by
    simpa [prefixWord, tailWord_5549675, baseEnd_5549675] using wordTrace_append hprefix tailTrace_5549675
  have hstable : (prefixWord ++ tailWord_5549675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549675).length < 2 ^ (prefixWord ++ tailWord_5549675).sum := by decide
  have hdescent : baseEnd_5549675 < baseStart_5549675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549682 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5549682 : Nat := 118140960795 + 5549682 * 2 ^ 59
def prefixEnd_5549682 : Nat := 4983230072969 + 3 ^ 40 * 5549682 * 2
def baseEnd_5549682 : Nat := 2849654345605261077352483

theorem tailTrace_5549682 : CollatzResearch.WordTrace tailWord_5549682 prefixEnd_5549682 2849654345605261077352483 := by
  unfold tailWord_5549682
  simp only [CollatzResearch.WordTrace]
  refine ⟨50603382870114349767920825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134942354320304932714455533 50603382870114349767920825)
  ·
    refine ⟨37952537152585762325940619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50603382870114349767920825 37952537152585762325940619)
    ·
      refine ⟨56928805728878643488910929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37952537152585762325940619 56928805728878643488910929)
      ·
        refine ⟨42696604296658982616683197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56928805728878643488910929 42696604296658982616683197)
        ·
          refine ⟨16011226611247118481256199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42696604296658982616683197 16011226611247118481256199)
          ·
            refine ⟨24016839916870677721884299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16011226611247118481256199 24016839916870677721884299)
            ·
              refine ⟨36025259875306016582826449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24016839916870677721884299 36025259875306016582826449)
              ·
                refine ⟨27018944906479512437119837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36025259875306016582826449 27018944906479512437119837)
                ·
                  refine ⟨10132104339929817163919939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27018944906479512437119837 10132104339929817163919939)
                  ·
                    refine ⟨15198156509894725745879909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10132104339929817163919939 15198156509894725745879909)
                    ·
                      refine ⟨2849654345605261077352483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15198156509894725745879909 2849654345605261077352483)
                      ·
                        rfl

theorem cell23_5549682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5549682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549682 prefixEnd_5549682 := by exact prefixLift 5549682
  have htrace : WordTrace (prefixWord ++ tailWord_5549682) baseStart_5549682 baseEnd_5549682 := by
    simpa [prefixWord, tailWord_5549682, baseEnd_5549682] using wordTrace_append hprefix tailTrace_5549682
  have hstable : (prefixWord ++ tailWord_5549682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549682).length < 2 ^ (prefixWord ++ tailWord_5549682).sum := by decide
  have hdescent : baseEnd_5549682 < baseStart_5549682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549716 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5549716 : Nat := 118140960795 + 5549716 * 2 ^ 59
def prefixEnd_5549716 : Nat := 4983230072969 + 3 ^ 40 * 5549716 * 2
def baseEnd_5549716 : Nat := 2849671803947513944327327

theorem tailTrace_5549716 : CollatzResearch.WordTrace tailWord_5549716 prefixEnd_5549716 2849671803947513944327327 := by
  unfold tailWord_5549716
  simp only [CollatzResearch.WordTrace]
  refine ⟨101207385781167111439210501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134943181041556148585614001 101207385781167111439210501)
  ·
    refine ⟨18976384833968833394851969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101207385781167111439210501 18976384833968833394851969)
    ·
      refine ⟨14232288625476625046138977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18976384833968833394851969 14232288625476625046138977)
      ·
        refine ⟨10674216469107468784604233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14232288625476625046138977 10674216469107468784604233)
        ·
          refine ⟨8005662351830601588453175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10674216469107468784604233 8005662351830601588453175)
          ·
            refine ⟨12008493527745902382679763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8005662351830601588453175 12008493527745902382679763)
            ·
              refine ⟨18012740291618853574019645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12008493527745902382679763 18012740291618853574019645)
              ·
                refine ⟨6754777609357070090257367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18012740291618853574019645 6754777609357070090257367)
                ·
                  refine ⟨10132166414035605135386051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754777609357070090257367 10132166414035605135386051)
                  ·
                    refine ⟨15198249621053407703079077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10132166414035605135386051 15198249621053407703079077)
                    ·
                      refine ⟨2849671803947513944327327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15198249621053407703079077 2849671803947513944327327)
                      ·
                        rfl

theorem cell23_5549716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5549716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549716 prefixEnd_5549716 := by exact prefixLift 5549716
  have htrace : WordTrace (prefixWord ++ tailWord_5549716) baseStart_5549716 baseEnd_5549716 := by
    simpa [prefixWord, tailWord_5549716, baseEnd_5549716] using wordTrace_append hprefix tailTrace_5549716
  have hstable : (prefixWord ++ tailWord_5549716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549716).length < 2 ^ (prefixWord ++ tailWord_5549716).sum := by decide
  have hdescent : baseEnd_5549716 < baseStart_5549716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549719 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_5549719 : Nat := 118140960795 + 5549719 * 2 ^ 59
def prefixEnd_5549719 : Nat := 4983230072969 + 3 ^ 40 * 5549719 * 2
def baseEnd_5549719 : Nat := 2849673344389477432589813

theorem tailTrace_5549719 : CollatzResearch.WordTrace tailWord_5549719 prefixEnd_5549719 2849673344389477432589813 := by
  unfold tailWord_5549719
  simp only [CollatzResearch.WordTrace]
  refine ⟨202414880981323354390780211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134943253987548902927186807 202414880981323354390780211)
  ·
    refine ⟨303622321471985031586170317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202414880981323354390780211 303622321471985031586170317)
    ·
      refine ⟨113858370551994386844813869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303622321471985031586170317 113858370551994386844813869)
      ·
        refine ⟨42696888956997895066805201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113858370551994386844813869 42696888956997895066805201)
        ·
          refine ⟨32022666717748421300103901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42696888956997895066805201 32022666717748421300103901)
          ·
            refine ⟨12008500019155657987538963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32022666717748421300103901 12008500019155657987538963)
            ·
              refine ⟨18012750028733486981308445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12008500019155657987538963 18012750028733486981308445)
              ·
                refine ⟨6754781260775057617990667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18012750028733486981308445 6754781260775057617990667)
                ·
                  refine ⟨10132171891162586426986001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754781260775057617990667 10132171891162586426986001)
                  ·
                    refine ⟨7599128918371939820239501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10132171891162586426986001 7599128918371939820239501)
                    ·
                      refine ⟨2849673344389477432589813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7599128918371939820239501 2849673344389477432589813)
                      ·
                        rfl

theorem cell23_5549719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_5549719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549719 prefixEnd_5549719 := by exact prefixLift 5549719
  have htrace : WordTrace (prefixWord ++ tailWord_5549719) baseStart_5549719 baseEnd_5549719 := by
    simpa [prefixWord, tailWord_5549719, baseEnd_5549719] using wordTrace_append hprefix tailTrace_5549719
  have hstable : (prefixWord ++ tailWord_5549719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549719).length < 2 ^ (prefixWord ++ tailWord_5549719).sum := by decide
  have hdescent : baseEnd_5549719 < baseStart_5549719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549725 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5549725 : Nat := 118140960795 + 5549725 * 2 ^ 59
def prefixEnd_5549725 : Nat := 4983230072969 + 3 ^ 40 * 5549725 * 2
def baseEnd_5549725 : Nat := 2849676425273404409114785

theorem tailTrace_5549725 : CollatzResearch.WordTrace tailWord_5549725 prefixEnd_5549725 2849676425273404409114785 := by
  unfold tailWord_5549725
  simp only [CollatzResearch.WordTrace]
  refine ⟨202415099819301617415498629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134943399879534411610332419 202415099819301617415498629)
  ·
    refine ⟨37952831216119053265405993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202415099819301617415498629 37952831216119053265405993)
    ·
      refine ⟨28464623412089289949054495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37952831216119053265405993 28464623412089289949054495)
      ·
        refine ⟨42696935118133934923581743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28464623412089289949054495 42696935118133934923581743)
        ·
          refine ⟨64045402677200902385372615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42696935118133934923581743 64045402677200902385372615)
          ·
            refine ⟨96068104015801353578058923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64045402677200902385372615 96068104015801353578058923)
            ·
              refine ⟨144102156023702030367088385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96068104015801353578058923 144102156023702030367088385)
              ·
                refine ⟨108076617017776522775316289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144102156023702030367088385 108076617017776522775316289)
                ·
                  refine ⟨81057462763332392081487217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108076617017776522775316289 81057462763332392081487217)
                  ·
                    refine ⟨60793097072499294061115413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81057462763332392081487217 60793097072499294061115413)
                    ·
                      refine ⟨2849676425273404409114785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60793097072499294061115413 2849676425273404409114785)
                      ·
                        rfl

theorem cell23_5549725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5549725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549725 prefixEnd_5549725 := by exact prefixLift 5549725
  have htrace : WordTrace (prefixWord ++ tailWord_5549725) baseStart_5549725 baseEnd_5549725 := by
    simpa [prefixWord, tailWord_5549725, baseEnd_5549725] using wordTrace_append hprefix tailTrace_5549725
  have hstable : (prefixWord ++ tailWord_5549725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549725).length < 2 ^ (prefixWord ++ tailWord_5549725).sum := by decide
  have hdescent : baseEnd_5549725 < baseStart_5549725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549726 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_5549726 : Nat := 118140960795 + 5549726 * 2 ^ 59
def prefixEnd_5549726 : Nat := 4983230072969 + 3 ^ 40 * 5549726 * 2
def baseEnd_5549726 : Nat := 949892312918019635067427

theorem tailTrace_5549726 : CollatzResearch.WordTrace tailWord_5549726 prefixEnd_5549726 949892312918019635067427 := by
  unfold tailWord_5549726
  simp only [CollatzResearch.WordTrace]
  refine ⟨25301892036537249323285629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134943424194865329724190021 25301892036537249323285629)
  ·
    refine ⟨9488209513701468496232111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25301892036537249323285629 9488209513701468496232111)
    ·
      refine ⟨14232314270552202744348167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9488209513701468496232111 14232314270552202744348167)
      ·
        refine ⟨21348471405828304116522251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14232314270552202744348167 21348471405828304116522251)
        ·
          refine ⟨32022707108742456174783377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21348471405828304116522251 32022707108742456174783377)
          ·
            refine ⟨24017030331556842131087533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32022707108742456174783377 24017030331556842131087533)
            ·
              refine ⟨9006386374333815799157825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24017030331556842131087533 9006386374333815799157825)
              ·
                refine ⟨6754789780750361849368369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9006386374333815799157825 6754789780750361849368369)
                ·
                  refine ⟨5066092335562771387026277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6754789780750361849368369 5066092335562771387026277)
                  ·
                    refine ⟨949892312918019635067427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066092335562771387026277 949892312918019635067427)
                    ·
                      rfl

theorem cell23_5549726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_5549726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549726 prefixEnd_5549726 := by exact prefixLift 5549726
  have htrace : WordTrace (prefixWord ++ tailWord_5549726) baseStart_5549726 baseEnd_5549726 := by
    simpa [prefixWord, tailWord_5549726, baseEnd_5549726] using wordTrace_append hprefix tailTrace_5549726
  have hstable : (prefixWord ++ tailWord_5549726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549726).length < 2 ^ (prefixWord ++ tailWord_5549726).sum := by decide
  have hdescent : baseEnd_5549726 < baseStart_5549726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549755 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4]
def baseStart_5549755 : Nat := 118140960795 + 5549755 * 2 ^ 59
def prefixEnd_5549755 : Nat := 4983230072969 + 3 ^ 40 * 5549755 * 2
def baseEnd_5549755 : Nat := 2849691829693039291739647

theorem tailTrace_5549755 : CollatzResearch.WordTrace tailWord_5549755 prefixEnd_5549755 2849691829693039291739647 := by
  unfold tailWord_5549755
  simp only [CollatzResearch.WordTrace]
  refine ⟨202416194009192932539090719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134944129339461955026060479 202416194009192932539090719)
  ·
    refine ⟨303624291013789398808636079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202416194009192932539090719 303624291013789398808636079)
    ·
      refine ⟨455436436520684098212954119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303624291013789398808636079 455436436520684098212954119)
      ·
        refine ⟨683154654781026147319431179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455436436520684098212954119 683154654781026147319431179)
        ·
          refine ⟨1024731982171539220979146769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683154654781026147319431179 1024731982171539220979146769)
          ·
            refine ⟨768548986628654415734360077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024731982171539220979146769 768548986628654415734360077)
            ·
              refine ⟨288205869985745405900385029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768548986628654415734360077 288205869985745405900385029)
              ·
                refine ⟨54038600622327263606322193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288205869985745405900385029 54038600622327263606322193)
                ·
                  refine ⟨40528950466745447704741645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54038600622327263606322193 40528950466745447704741645)
                  ·
                    refine ⟨15198356425029542889278117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40528950466745447704741645 15198356425029542889278117)
                    ·
                      refine ⟨2849691829693039291739647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15198356425029542889278117 2849691829693039291739647)
                      ·
                        rfl

theorem cell23_5549755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_5549755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549755 prefixEnd_5549755 := by exact prefixLift 5549755
  have htrace : WordTrace (prefixWord ++ tailWord_5549755) baseStart_5549755 baseEnd_5549755 := by
    simpa [prefixWord, tailWord_5549755, baseEnd_5549755] using wordTrace_append hprefix tailTrace_5549755
  have hstable : (prefixWord ++ tailWord_5549755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549755).length < 2 ^ (prefixWord ++ tailWord_5549755).sum := by decide
  have hdescent : baseEnd_5549755 < baseStart_5549755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549802 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_5549802 : Nat := 118140960795 + 5549802 * 2 ^ 59
def prefixEnd_5549802 : Nat := 4983230072969 + 3 ^ 40 * 5549802 * 2
def baseEnd_5549802 : Nat := 2849715963283800607851931

theorem tailTrace_5549802 : CollatzResearch.WordTrace tailWord_5549802 prefixEnd_5549802 2849715963283800607851931 := by
  unfold tailWord_5549802
  simp only [CollatzResearch.WordTrace]
  refine ⟨50604477060005664891512915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134945272160015106377367773 50604477060005664891512915)
  ·
    refine ⟨75906715590008497337269373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50604477060005664891512915 75906715590008497337269373)
    ·
      refine ⟨28465018346253186501476015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75906715590008497337269373 28465018346253186501476015)
      ·
        refine ⟨42697527519379779752214023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28465018346253186501476015 42697527519379779752214023)
        ·
          refine ⟨64046291279069669628321035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42697527519379779752214023 64046291279069669628321035)
          ·
            refine ⟨96069436918604504442481553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64046291279069669628321035 96069436918604504442481553)
            ·
              refine ⟨72052077688953378331861165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96069436918604504442481553 72052077688953378331861165)
              ·
                refine ⟨27019529133357516874447937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72052077688953378331861165 27019529133357516874447937)
                ·
                  refine ⟨20264646850018137655835953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27019529133357516874447937 20264646850018137655835953)
                  ·
                    refine ⟨15198485137513603241876965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20264646850018137655835953 15198485137513603241876965)
                    ·
                      refine ⟨2849715963283800607851931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15198485137513603241876965 2849715963283800607851931)
                      ·
                        rfl

theorem cell23_5549802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_5549802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549802 prefixEnd_5549802 := by exact prefixLift 5549802
  have htrace : WordTrace (prefixWord ++ tailWord_5549802) baseStart_5549802 baseEnd_5549802 := by
    simpa [prefixWord, tailWord_5549802, baseEnd_5549802] using wordTrace_append hprefix tailTrace_5549802
  have hstable : (prefixWord ++ tailWord_5549802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549802).length < 2 ^ (prefixWord ++ tailWord_5549802).sum := by decide
  have hdescent : baseEnd_5549802 < baseStart_5549802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549852 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_5549852 : Nat := 118140960795 + 5549852 * 2 ^ 59
def prefixEnd_5549852 : Nat := 4983230072969 + 3 ^ 40 * 5549852 * 2
def baseEnd_5549852 : Nat := 2849741637316525412226701

theorem tailTrace_5549852 : CollatzResearch.WordTrace tailWord_5549852 prefixEnd_5549852 2849741637316525412226701 := by
  unfold tailWord_5549852
  simp only [CollatzResearch.WordTrace]
  refine ⟨101209865944920759052685905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134946487926561012070247873 101209865944920759052685905)
  ·
    refine ⟨75907399458690569289514429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101209865944920759052685905 75907399458690569289514429)
    ·
      refine ⟨28465274797008963483567911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75907399458690569289514429 28465274797008963483567911)
      ·
        refine ⟨42697912195513445225351867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28465274797008963483567911 42697912195513445225351867)
        ·
          refine ⟨64046868293270167838027801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42697912195513445225351867 64046868293270167838027801)
          ·
            refine ⟨48035151219952625878520851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64046868293270167838027801 48035151219952625878520851)
            ·
              refine ⟨72052726829928938817781277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48035151219952625878520851 72052726829928938817781277)
              ·
                refine ⟨27019772561223352056667979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72052726829928938817781277 27019772561223352056667979)
                ·
                  refine ⟨40529658841835028085001969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27019772561223352056667979 40529658841835028085001969)
                  ·
                    refine ⟨30397244131376271063751477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40529658841835028085001969 30397244131376271063751477)
                    ·
                      refine ⟨2849741637316525412226701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30397244131376271063751477 2849741637316525412226701)
                      ·
                        rfl

theorem cell23_5549852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_5549852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549852 prefixEnd_5549852 := by exact prefixLift 5549852
  have htrace : WordTrace (prefixWord ++ tailWord_5549852) baseStart_5549852 baseEnd_5549852 := by
    simpa [prefixWord, tailWord_5549852, baseEnd_5549852] using wordTrace_append hprefix tailTrace_5549852
  have hstable : (prefixWord ++ tailWord_5549852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549852).length < 2 ^ (prefixWord ++ tailWord_5549852).sum := by decide
  have hdescent : baseEnd_5549852 < baseStart_5549852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549876 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_5549876 : Nat := 118140960795 + 5549876 * 2 ^ 59
def prefixEnd_5549876 : Nat := 4983230072969 + 3 ^ 40 * 5549876 * 2
def baseEnd_5549876 : Nat := 949917986950744439442197

theorem tailTrace_5549876 : CollatzResearch.WordTrace tailWord_5549876 prefixEnd_5549876 949917986950744439442197 := by
  unfold tailWord_5549876
  simp only [CollatzResearch.WordTrace]
  refine ⟨101210303620877285102122741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134947071494503046802830321 101210303620877285102122741)
  ·
    refine ⟨9488465964457245478324007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101210303620877285102122741 9488465964457245478324007)
    ·
      refine ⟨14232698946685868217486011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9488465964457245478324007 14232698946685868217486011)
      ·
        refine ⟨21349048420028802326229017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14232698946685868217486011 21349048420028802326229017)
        ·
          refine ⟨16011786315021601744671763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21349048420028802326229017 16011786315021601744671763)
          ·
            refine ⟨24017679472532402617007645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16011786315021601744671763 24017679472532402617007645)
            ·
              refine ⟨9006629802199650981377867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24017679472532402617007645 9006629802199650981377867)
              ·
                refine ⟨13509944703299476472066801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9006629802199650981377867 13509944703299476472066801)
                ·
                  refine ⟨10132458527474607354050101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13509944703299476472066801 10132458527474607354050101)
                  ·
                    refine ⟨949917986950744439442197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10132458527474607354050101 949917986950744439442197)
                    ·
                      rfl

theorem cell23_5549876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_5549876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549876 prefixEnd_5549876 := by exact prefixLift 5549876
  have htrace : WordTrace (prefixWord ++ tailWord_5549876) baseStart_5549876 baseEnd_5549876 := by
    simpa [prefixWord, tailWord_5549876, baseEnd_5549876] using wordTrace_append hprefix tailTrace_5549876
  have hstable : (prefixWord ++ tailWord_5549876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549876).length < 2 ^ (prefixWord ++ tailWord_5549876).sum := by decide
  have hdescent : baseEnd_5549876 < baseStart_5549876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549906 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_5549906 : Nat := 118140960795 + 5549906 * 2 ^ 59
def prefixEnd_5549906 : Nat := 4983230072969 + 3 ^ 40 * 5549906 * 2
def baseEnd_5549906 : Nat := 949923121757289400317151

theorem tailTrace_5549906 : CollatzResearch.WordTrace tailWord_5549906 prefixEnd_5549906 949923121757289400317151 := by
  unfold tailWord_5549906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50605425357911471331959393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134947800954430590218558381 50605425357911471331959393)
  ·
    refine ⟨37954069018433603498969545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50605425357911471331959393 37954069018433603498969545)
    ·
      refine ⟨28465551763825202624227159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37954069018433603498969545 28465551763825202624227159)
      ·
        refine ⟨42698327645737803936340739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28465551763825202624227159 42698327645737803936340739)
        ·
          refine ⟨64047491468606705904511109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42698327645737803936340739 64047491468606705904511109)
          ·
            refine ⟨12008904650363757357095833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64047491468606705904511109 12008904650363757357095833)
            ·
              refine ⟨9006678487772818017821875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12008904650363757357095833 9006678487772818017821875)
              ·
                refine ⟨13510017731659227026732813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9006678487772818017821875 13510017731659227026732813)
                ·
                  refine ⟨5066256649372210135024805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13510017731659227026732813 5066256649372210135024805)
                  ·
                    refine ⟨949923121757289400317151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066256649372210135024805 949923121757289400317151)
                    ·
                      rfl

theorem cell23_5549906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_5549906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549906 prefixEnd_5549906 := by exact prefixLift 5549906
  have htrace : WordTrace (prefixWord ++ tailWord_5549906) baseStart_5549906 baseEnd_5549906 := by
    simpa [prefixWord, tailWord_5549906, baseEnd_5549906] using wordTrace_append hprefix tailTrace_5549906
  have hstable : (prefixWord ++ tailWord_5549906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549906).length < 2 ^ (prefixWord ++ tailWord_5549906).sum := by decide
  have hdescent : baseEnd_5549906 < baseStart_5549906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549956 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_5549956 : Nat := 118140960795 + 5549956 * 2 ^ 59
def prefixEnd_5549956 : Nat := 4983230072969 + 3 ^ 40 * 5549956 * 2
def baseEnd_5549956 : Nat := 2849795039304593005326223

theorem tailTrace_5549956 : CollatzResearch.WordTrace tailWord_5549956 prefixEnd_5549956 2849795039304593005326223 := by
  unfold tailWord_5549956
  simp only [CollatzResearch.WordTrace]
  refine ⟨101211762540732371933578861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134949016720976495911438481 101211762540732371933578861)
  ·
    refine ⟨37954410952774639475092073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101211762540732371933578861 37954410952774639475092073)
    ·
      refine ⟨28465808214580979606319055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37954410952774639475092073 28465808214580979606319055)
      ·
        refine ⟨42698712321871469409478583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28465808214580979606319055 42698712321871469409478583)
        ·
          refine ⟨64048068482807204114217875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42698712321871469409478583 64048068482807204114217875)
          ·
            refine ⟨96072102724210806171326813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64048068482807204114217875 96072102724210806171326813)
            ·
              refine ⟨36027038521579052314247555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96072102724210806171326813 36027038521579052314247555)
              ·
                refine ⟨54040557782368578471371333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36027038521579052314247555 54040557782368578471371333)
                ·
                  refine ⟨10132604584194108463382125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54040557782368578471371333 10132604584194108463382125)
                  ·
                    refine ⟨3799726719072790673768297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10132604584194108463382125 3799726719072790673768297)
                    ·
                      refine ⟨2849795039304593005326223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799726719072790673768297 2849795039304593005326223)
                      ·
                        rfl

theorem cell23_5549956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_5549956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549956 prefixEnd_5549956 := by exact prefixLift 5549956
  have htrace : WordTrace (prefixWord ++ tailWord_5549956) baseStart_5549956 baseEnd_5549956 := by
    simpa [prefixWord, tailWord_5549956, baseEnd_5549956] using wordTrace_append hprefix tailTrace_5549956
  have hstable : (prefixWord ++ tailWord_5549956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549956).length < 2 ^ (prefixWord ++ tailWord_5549956).sum := by decide
  have hdescent : baseEnd_5549956 < baseStart_5549956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549983 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 1, 5]
def baseStart_5549983 : Nat := 118140960795 + 5549983 * 2 ^ 59
def prefixEnd_5549983 : Nat := 4983230072969 + 3 ^ 40 * 5549983 * 2
def baseEnd_5549983 : Nat := 949936301094088133229533

theorem tailTrace_5549983 : CollatzResearch.WordTrace tailWord_5549983 prefixEnd_5549983 949936301094088133229533 := by
  unfold tailWord_5549983
  simp only [CollatzResearch.WordTrace]
  refine ⟨202424509852366927478390603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134949673234911284985593735 202424509852366927478390603)
  ·
    refine ⟨303636764778550391217585905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202424509852366927478390603 303636764778550391217585905)
    ·
      refine ⟨227727573583912793413189429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303636764778550391217585905 227727573583912793413189429)
      ·
        refine ⟨21349460023491824382486509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227727573583912793413189429 21349460023491824382486509)
        ·
          refine ⟨8006047508809434143432441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21349460023491824382486509 8006047508809434143432441)
          ·
            refine ⟨6004535631607075607574331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8006047508809434143432441 6004535631607075607574331)
            ·
              refine ⟨9006803447410613411361497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004535631607075607574331 9006803447410613411361497)
              ·
                refine ⟨6755102585557960058521123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9006803447410613411361497 6755102585557960058521123)
                ·
                  refine ⟨10132653878336940087781685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6755102585557960058521123 10132653878336940087781685)
                  ·
                    refine ⟨949936301094088133229533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10132653878336940087781685 949936301094088133229533)
                    ·
                      rfl

theorem cell23_5549983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_5549983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549983 prefixEnd_5549983 := by exact prefixLift 5549983
  have htrace : WordTrace (prefixWord ++ tailWord_5549983) baseStart_5549983 baseEnd_5549983 := by
    simpa [prefixWord, tailWord_5549983, baseEnd_5549983] using wordTrace_append hprefix tailTrace_5549983
  have hstable : (prefixWord ++ tailWord_5549983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549983).length < 2 ^ (prefixWord ++ tailWord_5549983).sum := by decide
  have hdescent : baseEnd_5549983 < baseStart_5549983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5549999 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_5549999 : Nat := 118140960795 + 5549999 * 2 ^ 59
def prefixEnd_5549999 : Nat := 4983230072969 + 3 ^ 40 * 5549999 * 2
def baseEnd_5549999 : Nat := 2849817118972736337088525

theorem tailTrace_5549999 : CollatzResearch.WordTrace tailWord_5549999 prefixEnd_5549999 2849817118972736337088525 := by
  unfold tailWord_5549999
  simp only [CollatzResearch.WordTrace]
  refine ⟨202425093420308962210973051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134950062280205974807315367 202425093420308962210973051)
  ·
    refine ⟨303637640130463443316459577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202425093420308962210973051 303637640130463443316459577)
    ·
      refine ⟨227728230097847582487344683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303637640130463443316459577 227728230097847582487344683)
      ·
        refine ⟨341592345146771373731017025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227728230097847582487344683 341592345146771373731017025)
        ·
          refine ⟨256194258860078530298262769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341592345146771373731017025 256194258860078530298262769)
          ·
            refine ⟨192145694145058897723697077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256194258860078530298262769 192145694145058897723697077)
            ·
              refine ⟨18013658826099271661596601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192145694145058897723697077 18013658826099271661596601)
              ·
                refine ⟨13510244119574453746197451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18013658826099271661596601 13510244119574453746197451)
                ·
                  refine ⟨20265366179361680619296177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13510244119574453746197451 20265366179361680619296177)
                  ·
                    refine ⟨15199024634521260464472133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20265366179361680619296177 15199024634521260464472133)
                    ·
                      refine ⟨2849817118972736337088525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15199024634521260464472133 2849817118972736337088525)
                      ·
                        rfl

theorem cell23_5549999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_5549999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5549999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5549999 prefixEnd_5549999 := by exact prefixLift 5549999
  have htrace : WordTrace (prefixWord ++ tailWord_5549999) baseStart_5549999 baseEnd_5549999 := by
    simpa [prefixWord, tailWord_5549999, baseEnd_5549999] using wordTrace_append hprefix tailTrace_5549999
  have hstable : (prefixWord ++ tailWord_5549999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5549999).length < 2 ^ (prefixWord ++ tailWord_5549999).sum := by decide
  have hdescent : baseEnd_5549999 < baseStart_5549999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5549999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550013 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_5550013 : Nat := 118140960795 + 5550013 * 2 ^ 59
def prefixEnd_5550013 : Nat := 4983230072969 + 3 ^ 40 * 5550013 * 2
def baseEnd_5550013 : Nat := 949941435900633094104487

theorem tailTrace_5550013 : CollatzResearch.WordTrace tailWord_5550013 prefixEnd_5550013 949941435900633094104487 := by
  unfold tailWord_5550013
  simp only [CollatzResearch.WordTrace]
  refine ⟨202425604042258242601982693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134950402694838828401321795 202425604042258242601982693)
  ·
    refine ⟨37954800757923420487871755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202425604042258242601982693 37954800757923420487871755)
    ·
      refine ⟨56932201136885130731807633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37954800757923420487871755 56932201136885130731807633)
      ·
        refine ⟨42699150852663848048855725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56932201136885130731807633 42699150852663848048855725)
        ·
          refine ⟨16012181569748943018320897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42699150852663848048855725 16012181569748943018320897)
          ·
            refine ⟨12009136177311707263740673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16012181569748943018320897 12009136177311707263740673)
            ·
              refine ⟨9006852132983780447805505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12009136177311707263740673 9006852132983780447805505)
              ·
                refine ⟨6755139099737835335854129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9006852132983780447805505 6755139099737835335854129)
                ·
                  refine ⟨5066354324803376501890597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6755139099737835335854129 5066354324803376501890597)
                  ·
                    refine ⟨949941435900633094104487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066354324803376501890597 949941435900633094104487)
                    ·
                      rfl

theorem cell23_5550013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_5550013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550013 prefixEnd_5550013 := by exact prefixLift 5550013
  have htrace : WordTrace (prefixWord ++ tailWord_5550013) baseStart_5550013 baseEnd_5550013 := by
    simpa [prefixWord, tailWord_5550013, baseEnd_5550013] using wordTrace_append hprefix tailTrace_5550013
  have hstable : (prefixWord ++ tailWord_5550013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550013).length < 2 ^ (prefixWord ++ tailWord_5550013).sum := by decide
  have hdescent : baseEnd_5550013 < baseStart_5550013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550063 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 1, 3, 2]
def baseStart_5550063 : Nat := 118140960795 + 5550063 * 2 ^ 59
def prefixEnd_5550063 : Nat := 4983230072969 + 3 ^ 40 * 5550063 * 2
def baseEnd_5550063 : Nat := 2849849981734624086688231

theorem tailTrace_5550063 : CollatzResearch.WordTrace tailWord_5550063 prefixEnd_5550063 2849849981734624086688231 := by
  unfold tailWord_5550063
  simp only [CollatzResearch.WordTrace]
  refine ⟨202427427692077101141302843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134951618461384734094201895 202427427692077101141302843)
  ·
    refine ⟨303641141538115651711954265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202427427692077101141302843 303641141538115651711954265)
    ·
      refine ⟨227730856153586738783965699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303641141538115651711954265 227730856153586738783965699)
      ·
        refine ⟨341596284230380108175948549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227730856153586738783965699 341596284230380108175948549)
        ·
          refine ⟨64049303293196270282990353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 341596284230380108175948549 64049303293196270282990353)
          ·
            refine ⟨48036977469897202712242765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64049303293196270282990353 48036977469897202712242765)
            ·
              refine ⟨18013866551211451017091037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48036977469897202712242765 18013866551211451017091037)
              ·
                refine ⟨6755199956704294131409139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18013866551211451017091037 6755199956704294131409139)
                ·
                  refine ⟨10132799935056441197113709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6755199956704294131409139 10132799935056441197113709)
                  ·
                    refine ⟨3799799975646165448917641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10132799935056441197113709 3799799975646165448917641)
                    ·
                      refine ⟨2849849981734624086688231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799799975646165448917641 2849849981734624086688231)
                      ·
                        rfl

theorem cell23_5550063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 3, 2].length) (baseStart_5550063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550063 prefixEnd_5550063 := by exact prefixLift 5550063
  have htrace : WordTrace (prefixWord ++ tailWord_5550063) baseStart_5550063 baseEnd_5550063 := by
    simpa [prefixWord, tailWord_5550063, baseEnd_5550063] using wordTrace_append hprefix tailTrace_5550063
  have hstable : (prefixWord ++ tailWord_5550063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550063).length < 2 ^ (prefixWord ++ tailWord_5550063).sum := by decide
  have hdescent : baseEnd_5550063 < baseStart_5550063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550070 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5550070 : Nat := 118140960795 + 5550070 * 2 ^ 59
def prefixEnd_5550070 : Nat := 4983230072969 + 3 ^ 40 * 5550070 * 2
def baseEnd_5550070 : Nat := 2849853576099205559300699

theorem tailTrace_5550070 : CollatzResearch.WordTrace tailWord_5550070 prefixEnd_5550070 2849853576099205559300699 := by
  unfold tailWord_5550070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651730187690733833550479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134951788668701160891205109 12651730187690733833550479)
  ·
    refine ⟨18977595281536100750325719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12651730187690733833550479 18977595281536100750325719)
    ·
      refine ⟨28466392922304151125488579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18977595281536100750325719 28466392922304151125488579)
      ·
        refine ⟨42699589383456226688232869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28466392922304151125488579 42699589383456226688232869)
        ·
          refine ⟨8006173009398042504043663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42699589383456226688232869 8006173009398042504043663)
          ·
            refine ⟨12009259514097063756065495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006173009398042504043663 12009259514097063756065495)
            ·
              refine ⟨18013889271145595634098243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12009259514097063756065495 18013889271145595634098243)
              ·
                refine ⟨27020833906718393451147365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18013889271145595634098243 27020833906718393451147365)
                ·
                  refine ⟨5066406357509698772090131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27020833906718393451147365 5066406357509698772090131)
                  ·
                    refine ⟨7599609536264548158135197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5066406357509698772090131 7599609536264548158135197)
                    ·
                      refine ⟨2849853576099205559300699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7599609536264548158135197 2849853576099205559300699)
                      ·
                        rfl

theorem cell23_5550070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5550070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550070 prefixEnd_5550070 := by exact prefixLift 5550070
  have htrace : WordTrace (prefixWord ++ tailWord_5550070) baseStart_5550070 baseEnd_5550070 := by
    simpa [prefixWord, tailWord_5550070, baseEnd_5550070] using wordTrace_append hprefix tailTrace_5550070
  have hstable : (prefixWord ++ tailWord_5550070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550070).length < 2 ^ (prefixWord ++ tailWord_5550070).sum := by decide
  have hdescent : baseEnd_5550070 < baseStart_5550070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550079 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_5550079 : Nat := 118140960795 + 5550079 * 2 ^ 59
def prefixEnd_5550079 : Nat := 4983230072969 + 3 ^ 40 * 5550079 * 2
def baseEnd_5550079 : Nat := 2849858197425096024088157

theorem tailTrace_5550079 : CollatzResearch.WordTrace tailWord_5550079 prefixEnd_5550079 2849858197425096024088157 := by
  unfold tailWord_5550079
  simp only [CollatzResearch.WordTrace]
  refine ⟨202428011260019135873885291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134952007506679423915923527 202428011260019135873885291)
  ·
    refine ⟨303642016890028703810827937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202428011260019135873885291 303642016890028703810827937)
    ·
      refine ⟨227731512667521527858120953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303642016890028703810827937 227731512667521527858120953)
      ·
        refine ⟨170798634500641145893590715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227731512667521527858120953 170798634500641145893590715)
        ·
          refine ⟨256197951750961718840386073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170798634500641145893590715 256197951750961718840386073)
          ·
            refine ⟨192148463813221289130289555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256197951750961718840386073 192148463813221289130289555)
            ·
              refine ⟨288222695719831933695434333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192148463813221289130289555 288222695719831933695434333)
              ·
                refine ⟨108083510894936975135787875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288222695719831933695434333 108083510894936975135787875)
                ·
                  refine ⟨162125266342405462703681813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108083510894936975135787875 162125266342405462703681813)
                  ·
                    refine ⟨7599621859800256064235085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 162125266342405462703681813 7599621859800256064235085)
                    ·
                      refine ⟨2849858197425096024088157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7599621859800256064235085 2849858197425096024088157)
                      ·
                        rfl

theorem cell23_5550079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_5550079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550079 prefixEnd_5550079 := by exact prefixLift 5550079
  have htrace : WordTrace (prefixWord ++ tailWord_5550079) baseStart_5550079 baseEnd_5550079 := by
    simpa [prefixWord, tailWord_5550079, baseEnd_5550079] using wordTrace_append hprefix tailTrace_5550079
  have hstable : (prefixWord ++ tailWord_5550079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550079).length < 2 ^ (prefixWord ++ tailWord_5550079).sum := by decide
  have hdescent : baseEnd_5550079 < baseStart_5550079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550099 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 7]
def baseStart_5550099 : Nat := 118140960795 + 5550099 * 2 ^ 59
def prefixEnd_5550099 : Nat := 4983230072969 + 3 ^ 40 * 5550099 * 2
def baseEnd_5550099 : Nat := 316652051893131771759785

theorem tailTrace_5550099 : CollatzResearch.WordTrace tailWord_5550099 prefixEnd_5550099 316652051893131771759785 := by
  unfold tailWord_5550099
  simp only [CollatzResearch.WordTrace]
  refine ⟨202428740719946679289613351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134952493813297786193075567 202428740719946679289613351)
  ·
    refine ⟨303643111079920018934420027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202428740719946679289613351 303643111079920018934420027)
    ·
      refine ⟨455464666619880028401630041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303643111079920018934420027 455464666619880028401630041)
      ·
        refine ⟨341598499964910021301222531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455464666619880028401630041 341598499964910021301222531)
        ·
          refine ⟨512397749947365031951833797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341598499964910021301222531 512397749947365031951833797)
          ·
            refine ⟨96074578115130943490968837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 512397749947365031951833797 96074578115130943490968837)
            ·
              refine ⟨18013983396587051904556657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96074578115130943490968837 18013983396587051904556657)
              ·
                refine ⟨13510487547440288928417493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18013983396587051904556657 13510487547440288928417493)
                ·
                  refine ⟨316652051893131771759785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13510487547440288928417493 316652051893131771759785)
                  ·
                    rfl

theorem cell23_5550099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 7].length) (baseStart_5550099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550099 prefixEnd_5550099 := by exact prefixLift 5550099
  have htrace : WordTrace (prefixWord ++ tailWord_5550099) baseStart_5550099 baseEnd_5550099 := by
    simpa [prefixWord, tailWord_5550099, baseEnd_5550099] using wordTrace_append hprefix tailTrace_5550099
  have hstable : (prefixWord ++ tailWord_5550099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550099).length < 2 ^ (prefixWord ++ tailWord_5550099).sum := by decide
  have hdescent : baseEnd_5550099 < baseStart_5550099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550139 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5]
def baseStart_5550139 : Nat := 118140960795 + 5550139 * 2 ^ 59
def prefixEnd_5550139 : Nat := 4983230072969 + 3 ^ 40 * 5550139 * 2
def baseEnd_5550139 : Nat := 2849889006264365789337881

theorem tailTrace_5550139 : CollatzResearch.WordTrace tailWord_5550139 prefixEnd_5550139 2849889006264365789337881 := by
  unfold tailWord_5550139
  simp only [CollatzResearch.WordTrace]
  refine ⟨202430199639801766121069471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134953466426534510747379647 202430199639801766121069471)
  ·
    refine ⟨303645299459702649181604207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202430199639801766121069471 303645299459702649181604207)
    ·
      refine ⟨455467949189553973772406311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303645299459702649181604207 455467949189553973772406311)
      ·
        refine ⟨683201923784330960658609467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455467949189553973772406311 683201923784330960658609467)
        ·
          refine ⟨1024802885676496440987914201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683201923784330960658609467 1024802885676496440987914201)
          ·
            refine ⟨768602164257372330740935651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024802885676496440987914201 768602164257372330740935651)
            ·
              refine ⟨1152903246386058496111403477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768602164257372330740935651 1152903246386058496111403477)
              ·
                refine ⟨27021169837173246002611019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1152903246386058496111403477 27021169837173246002611019)
                ·
                  refine ⟨40531754755759869003916529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27021169837173246002611019 40531754755759869003916529)
                  ·
                    refine ⟨30398816066819901752937397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40531754755759869003916529 30398816066819901752937397)
                    ·
                      refine ⟨2849889006264365789337881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30398816066819901752937397 2849889006264365789337881)
                      ·
                        rfl

theorem cell23_5550139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_5550139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550139 prefixEnd_5550139 := by exact prefixLift 5550139
  have htrace : WordTrace (prefixWord ++ tailWord_5550139) baseStart_5550139 baseEnd_5550139 := by
    simpa [prefixWord, tailWord_5550139, baseEnd_5550139] using wordTrace_append hprefix tailTrace_5550139
  have hstable : (prefixWord ++ tailWord_5550139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550139).length < 2 ^ (prefixWord ++ tailWord_5550139).sum := by decide
  have hdescent : baseEnd_5550139 < baseStart_5550139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550173 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5550173 : Nat := 118140960795 + 5550173 * 2 ^ 59
def prefixEnd_5550173 : Nat := 4983230072969 + 3 ^ 40 * 5550173 * 2
def baseEnd_5550173 : Nat := 2849906464606618656312725

theorem tailTrace_5550173 : CollatzResearch.WordTrace tailWord_5550173 prefixEnd_5550173 2849906464606618656312725 := by
  unfold tailWord_5550173
  simp only [CollatzResearch.WordTrace]
  refine ⟨202431439721678589927807173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134954293147785726618538115 202431439721678589927807173)
  ·
    refine ⟨37955894947814735611463845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202431439721678589927807173 37955894947814735611463845)
    ·
      refine ⟨7116730302715262927149471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37955894947814735611463845 7116730302715262927149471)
      ·
        refine ⟨10675095454072894390724207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7116730302715262927149471 10675095454072894390724207)
        ·
          refine ⟨16012643181109341586086311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675095454072894390724207 16012643181109341586086311)
          ·
            refine ⟨24018964771664012379129467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16012643181109341586086311 24018964771664012379129467)
            ·
              refine ⟨36028447157496018568694201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24018964771664012379129467 36028447157496018568694201)
              ·
                refine ⟨27021335368122013926520651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36028447157496018568694201 27021335368122013926520651)
                ·
                  refine ⟨40532003052183020889780977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27021335368122013926520651 40532003052183020889780977)
                  ·
                    refine ⟨30399002289137265667335733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40532003052183020889780977 30399002289137265667335733)
                    ·
                      refine ⟨2849906464606618656312725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30399002289137265667335733 2849906464606618656312725)
                      ·
                        rfl

theorem cell23_5550173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5550173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550173 prefixEnd_5550173 := by exact prefixLift 5550173
  have htrace : WordTrace (prefixWord ++ tailWord_5550173) baseStart_5550173 baseEnd_5550173 := by
    simpa [prefixWord, tailWord_5550173, baseEnd_5550173] using wordTrace_append hprefix tailTrace_5550173
  have hstable : (prefixWord ++ tailWord_5550173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550173).length < 2 ^ (prefixWord ++ tailWord_5550173).sum := by decide
  have hdescent : baseEnd_5550173 < baseStart_5550173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550183 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_5550183 : Nat := 118140960795 + 5550183 * 2 ^ 59
def prefixEnd_5550183 : Nat := 4983230072969 + 3 ^ 40 * 5550183 * 2
def baseEnd_5550183 : Nat := 2849911599413163617187679

theorem tailTrace_5550183 : CollatzResearch.WordTrace tailWord_5550183 prefixEnd_5550183 2849911599413163617187679 := by
  unfold tailWord_5550183
  simp only [CollatzResearch.WordTrace]
  refine ⟨202431804451642361635671203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134954536301094907757114135 202431804451642361635671203)
  ·
    refine ⟨303647706677463542453506805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202431804451642361635671203 303647706677463542453506805)
    ·
      refine ⟨28466972501012207105016263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303647706677463542453506805 28466972501012207105016263)
      ·
        refine ⟨42700458751518310657524395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28466972501012207105016263 42700458751518310657524395)
        ·
          refine ⟨64050688127277465986286593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42700458751518310657524395 64050688127277465986286593)
          ·
            refine ⟨48038016095458099489714945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64050688127277465986286593 48038016095458099489714945)
            ·
              refine ⟨36028512071593574617286209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48038016095458099489714945 36028512071593574617286209)
              ·
                refine ⟨27021384053695180962964657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36028512071593574617286209 27021384053695180962964657)
                ·
                  refine ⟨20266038040271385722223493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27021384053695180962964657 20266038040271385722223493)
                  ·
                    refine ⟨3799882132550884822916905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20266038040271385722223493 3799882132550884822916905)
                    ·
                      refine ⟨2849911599413163617187679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799882132550884822916905 2849911599413163617187679)
                      ·
                        rfl

theorem cell23_5550183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_5550183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550183 prefixEnd_5550183 := by exact prefixLift 5550183
  have htrace : WordTrace (prefixWord ++ tailWord_5550183) baseStart_5550183 baseEnd_5550183 := by
    simpa [prefixWord, tailWord_5550183, baseEnd_5550183] using wordTrace_append hprefix tailTrace_5550183
  have hstable : (prefixWord ++ tailWord_5550183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550183).length < 2 ^ (prefixWord ++ tailWord_5550183).sum := by decide
  have hdescent : baseEnd_5550183 < baseStart_5550183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550290 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_5550290 : Nat := 118140960795 + 5550290 * 2 ^ 59
def prefixEnd_5550290 : Nat := 4983230072969 + 3 ^ 40 * 5550290 * 2
def baseEnd_5550290 : Nat := 2849966541843194698549687

theorem tailTrace_5550290 : CollatzResearch.WordTrace tailWord_5550290 prefixEnd_5550290 2849966541843194698549687 := by
  unfold tailWord_5550290
  simp only [CollatzResearch.WordTrace]
  refine ⟨50608926765563679727454081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134957138041503145939877549 50608926765563679727454081)
  ·
    refine ⟨37956695074172759795590561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50608926765563679727454081 37956695074172759795590561)
    ·
      refine ⟨28467521305629569846692921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37956695074172759795590561 28467521305629569846692921)
      ·
        refine ⟨21350640979222177385019691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28467521305629569846692921 21350640979222177385019691)
        ·
          refine ⟨32025961468833266077529537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21350640979222177385019691 32025961468833266077529537)
          ·
            refine ⟨24019471101624949558147153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32025961468833266077529537 24019471101624949558147153)
            ·
              refine ⟨18014603326218712168610365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24019471101624949558147153 18014603326218712168610365)
              ·
                refine ⟨6755476247332017063228887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18014603326218712168610365 6755476247332017063228887)
                ·
                  refine ⟨10133214370998025594843331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6755476247332017063228887 10133214370998025594843331)
                  ·
                    refine ⟨15199821556497038392264997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10133214370998025594843331 15199821556497038392264997)
                    ·
                      refine ⟨2849966541843194698549687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15199821556497038392264997 2849966541843194698549687)
                      ·
                        rfl

theorem cell23_5550290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_5550290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550290 prefixEnd_5550290 := by exact prefixLift 5550290
  have htrace : WordTrace (prefixWord ++ tailWord_5550290) baseStart_5550290 baseEnd_5550290 := by
    simpa [prefixWord, tailWord_5550290, baseEnd_5550290] using wordTrace_append hprefix tailTrace_5550290
  have hstable : (prefixWord ++ tailWord_5550290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550290).length < 2 ^ (prefixWord ++ tailWord_5550290).sum := by decide
  have hdescent : baseEnd_5550290 < baseStart_5550290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550294 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_5550294 : Nat := 118140960795 + 5550294 * 2 ^ 59
def prefixEnd_5550294 : Nat := 4983230072969 + 3 ^ 40 * 5550294 * 2
def baseEnd_5550294 : Nat := 2849968595765812682899669

theorem tailTrace_5550294 : CollatzResearch.WordTrace tailWord_5550294 prefixEnd_5550294 2849968595765812682899669 := by
  unfold tailWord_5550294
  simp only [CollatzResearch.WordTrace]
  refine ⟨12652240809640014224560121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134957235302826818395307957 12652240809640014224560121)
  ·
    refine ⟨9489180607230010668420091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12652240809640014224560121 9489180607230010668420091)
    ·
      refine ⟨14233770910845016002630137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9489180607230010668420091 14233770910845016002630137)
      ·
        refine ⟨10675328183133762001972603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14233770910845016002630137 10675328183133762001972603)
        ·
          refine ⟨16012992274700643002958905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675328183133762001972603 16012992274700643002958905)
          ·
            refine ⟨12009744206025482252219179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16012992274700643002958905 12009744206025482252219179)
            ·
              refine ⟨18014616309038223378328769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12009744206025482252219179 18014616309038223378328769)
              ·
                refine ⟨13510962231778667533746577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18014616309038223378328769 13510962231778667533746577)
                ·
                  refine ⟨10133221673834000650309933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13510962231778667533746577 10133221673834000650309933)
                  ·
                    refine ⟨3799958127687750243866225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10133221673834000650309933 3799958127687750243866225)
                    ·
                      refine ⟨2849968595765812682899669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3799958127687750243866225 2849968595765812682899669)
                      ·
                        rfl

theorem cell23_5550294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_5550294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550294 prefixEnd_5550294 := by exact prefixLift 5550294
  have htrace : WordTrace (prefixWord ++ tailWord_5550294) baseStart_5550294 baseEnd_5550294 := by
    simpa [prefixWord, tailWord_5550294, baseEnd_5550294] using wordTrace_append hprefix tailTrace_5550294
  have hstable : (prefixWord ++ tailWord_5550294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550294).length < 2 ^ (prefixWord ++ tailWord_5550294).sum := by decide
  have hdescent : baseEnd_5550294 < baseStart_5550294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550296 : List Nat := [2, 1, 2, 2, 4, 1, 11]
def baseStart_5550296 : Nat := 118140960795 + 5550296 * 2 ^ 59
def prefixEnd_5550296 : Nat := 4983230072969 + 3 ^ 40 * 5550296 * 2
def baseEnd_5550296 : Nat := 35184810157124958951539

theorem tailTrace_5550296 : CollatzResearch.WordTrace tailWord_5550296 prefixEnd_5550296 35184810157124958951539 := by
  unfold tailWord_5550296
  simp only [CollatzResearch.WordTrace]
  refine ⟨101217962950116490967267371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134957283933488654623023161 101217962950116490967267371)
  ·
    refine ⟨151826944425174736450901057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101217962950116490967267371 151826944425174736450901057)
    ·
      refine ⟨113870208318881052338175793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151826944425174736450901057 113870208318881052338175793)
      ·
        refine ⟨85402656239160789253631845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113870208318881052338175793 85402656239160789253631845)
        ·
          refine ⟨16012998044842647985055971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85402656239160789253631845 16012998044842647985055971)
          ·
            refine ⟨24019497067263971977583957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16012998044842647985055971 24019497067263971977583957)
            ·
              refine ⟨35184810157124958951539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24019497067263971977583957 35184810157124958951539)
              ·
                rfl

theorem cell23_5550296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 11].length) (baseStart_5550296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550296 prefixEnd_5550296 := by exact prefixLift 5550296
  have htrace : WordTrace (prefixWord ++ tailWord_5550296) baseStart_5550296 baseEnd_5550296 := by
    simpa [prefixWord, tailWord_5550296, baseEnd_5550296] using wordTrace_append hprefix tailTrace_5550296
  have hstable : (prefixWord ++ tailWord_5550296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550296).length < 2 ^ (prefixWord ++ tailWord_5550296).sum := by decide
  have hdescent : baseEnd_5550296 < baseStart_5550296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550301 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5550301 : Nat := 118140960795 + 5550301 * 2 ^ 59
def prefixEnd_5550301 : Nat := 4983230072969 + 3 ^ 40 * 5550301 * 2
def baseEnd_5550301 : Nat := 2849972190130394155512137

theorem tailTrace_5550301 : CollatzResearch.WordTrace tailWord_5550301 prefixEnd_5550301 2849972190130394155512137 := by
  unfold tailWord_5550301
  simp only [CollatzResearch.WordTrace]
  refine ⟨202436108265214867788466757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134957405510143245192311171 202436108265214867788466757)
  ·
    refine ⟨37956770299727787710337517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202436108265214867788466757 37956770299727787710337517)
    ·
      refine ⟨14233788862397920391376569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37956770299727787710337517 14233788862397920391376569)
      ·
        refine ⟨10675341646798440293532427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14233788862397920391376569 10675341646798440293532427)
        ·
          refine ⟨16013012470197660440298641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675341646798440293532427 16013012470197660440298641)
          ·
            refine ⟨12009759352648245330223981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16013012470197660440298641 12009759352648245330223981)
            ·
              refine ⟨4503659757243091998833993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12009759352648245330223981 4503659757243091998833993)
              ·
                refine ⟨3377744817932318999125495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4503659757243091998833993 3377744817932318999125495)
                ·
                  refine ⟨5066617226898478498688243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377744817932318999125495 5066617226898478498688243)
                  ·
                    refine ⟨7599925840347717748032365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5066617226898478498688243 7599925840347717748032365)
                    ·
                      refine ⟨2849972190130394155512137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7599925840347717748032365 2849972190130394155512137)
                      ·
                        rfl

theorem cell23_5550301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5550301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550301 prefixEnd_5550301 := by exact prefixLift 5550301
  have htrace : WordTrace (prefixWord ++ tailWord_5550301) baseStart_5550301 baseEnd_5550301 := by
    simpa [prefixWord, tailWord_5550301, baseEnd_5550301] using wordTrace_append hprefix tailTrace_5550301
  have hstable : (prefixWord ++ tailWord_5550301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550301).length < 2 ^ (prefixWord ++ tailWord_5550301).sum := by decide
  have hdescent : baseEnd_5550301 < baseStart_5550301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550316 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_5550316 : Nat := 118140960795 + 5550316 * 2 ^ 59
def prefixEnd_5550316 : Nat := 4983230072969 + 3 ^ 40 * 5550316 * 2
def baseEnd_5550316 : Nat := 2849979892340211596824567

theorem tailTrace_5550316 : CollatzResearch.WordTrace tailWord_5550316 prefixEnd_5550316 2849979892340211596824567 := by
  unfold tailWord_5550316
  simp only [CollatzResearch.WordTrace]
  refine ⟨101218327680080262675131401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134957770240107016900175201 101218327680080262675131401)
  ·
    refine ⟨75913745760060197006348551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101218327680080262675131401 75913745760060197006348551)
    ·
      refine ⟨113870618640090295509522827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75913745760060197006348551 113870618640090295509522827)
      ·
        refine ⟨170805927960135443264284241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113870618640090295509522827 170805927960135443264284241)
        ·
          refine ⟨128104445970101582448213181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170805927960135443264284241 128104445970101582448213181)
          ·
            refine ⟨48039167238788093418079943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128104445970101582448213181 48039167238788093418079943)
            ·
              refine ⟨72058750858182140127119915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48039167238788093418079943 72058750858182140127119915)
              ·
                refine ⟨108088126287273210190679873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72058750858182140127119915 108088126287273210190679873)
                ·
                  refine ⟨81066094715454907643009905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108088126287273210190679873 81066094715454907643009905)
                  ·
                    refine ⟨60799571036591180732257429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81066094715454907643009905 60799571036591180732257429)
                    ·
                      refine ⟨2849979892340211596824567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60799571036591180732257429 2849979892340211596824567)
                      ·
                        rfl

theorem cell23_5550316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_5550316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550316 prefixEnd_5550316 := by exact prefixLift 5550316
  have htrace : WordTrace (prefixWord ++ tailWord_5550316) baseStart_5550316 baseEnd_5550316 := by
    simpa [prefixWord, tailWord_5550316, baseEnd_5550316] using wordTrace_append hprefix tailTrace_5550316
  have hstable : (prefixWord ++ tailWord_5550316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550316).length < 2 ^ (prefixWord ++ tailWord_5550316).sum := by decide
  have hdescent : baseEnd_5550316 < baseStart_5550316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550317 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_5550317 : Nat := 118140960795 + 5550317 * 2 ^ 59
def prefixEnd_5550317 : Nat := 4983230072969 + 3 ^ 40 * 5550317 * 2
def baseEnd_5550317 : Nat := 949993468606955364304021

theorem tailTrace_5550317 : CollatzResearch.WordTrace tailWord_5550317 prefixEnd_5550317 949993468606955364304021 := by
  unfold tailWord_5550317
  simp only [CollatzResearch.WordTrace]
  refine ⟨202436691833156902521049205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134957794555437935014032803 202436691833156902521049205)
  ·
    refine ⟨18978439859358459611348363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202436691833156902521049205 18978439859358459611348363)
    ·
      refine ⟨28467659789037689417022545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18978439859358459611348363 28467659789037689417022545)
      ·
        refine ⟨21350744841778267062766909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28467659789037689417022545 21350744841778267062766909)
        ·
          refine ⟨8006529315666850148537591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21350744841778267062766909 8006529315666850148537591)
          ·
            refine ⟨12009793973500275222806387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006529315666850148537591 12009793973500275222806387)
            ·
              refine ⟨18014690960250412834209581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12009793973500275222806387 18014690960250412834209581)
              ·
                refine ⟨6755509110093904812828593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18014690960250412834209581 6755509110093904812828593)
                ·
                  refine ⟨5066631832570428609621445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6755509110093904812828593 5066631832570428609621445)
                  ·
                    refine ⟨949993468606955364304021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066631832570428609621445 949993468606955364304021)
                    ·
                      rfl

theorem cell23_5550317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_5550317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550317 prefixEnd_5550317 := by exact prefixLift 5550317
  have htrace : WordTrace (prefixWord ++ tailWord_5550317) baseStart_5550317 baseEnd_5550317 := by
    simpa [prefixWord, tailWord_5550317, baseEnd_5550317] using wordTrace_append hprefix tailTrace_5550317
  have hstable : (prefixWord ++ tailWord_5550317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550317).length < 2 ^ (prefixWord ++ tailWord_5550317).sum := by decide
  have hdescent : baseEnd_5550317 < baseStart_5550317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550323 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 3]
def baseStart_5550323 : Nat := 118140960795 + 5550323 * 2 ^ 59
def prefixEnd_5550323 : Nat := 4983230072969 + 3 ^ 40 * 5550323 * 2
def baseEnd_5550323 : Nat := 2849983486704793069437035

theorem tailTrace_5550323 : CollatzResearch.WordTrace tailWord_5550323 prefixEnd_5550323 2849983486704793069437035 := by
  unfold tailWord_5550323
  simp only [CollatzResearch.WordTrace]
  refine ⟨202436910671135165545767623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134957940447423443697178415 202436910671135165545767623)
  ·
    refine ⟨303655366006702748318651435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202436910671135165545767623 303655366006702748318651435)
    ·
      refine ⟨455483049010054122477977153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303655366006702748318651435 455483049010054122477977153)
      ·
        refine ⟨341612286757540591858482865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455483049010054122477977153 341612286757540591858482865)
        ·
          refine ⟨256209215068155443893862149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341612286757540591858482865 256209215068155443893862149)
          ·
            refine ⟨48039227825279145730099153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256209215068155443893862149 48039227825279145730099153)
            ·
              refine ⟨36029420868959359297574365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48039227825279145730099153 36029420868959359297574365)
              ·
                refine ⟨13511032825859759736590387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36029420868959359297574365 13511032825859759736590387)
                ·
                  refine ⟨20266549238789639604885581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13511032825859759736590387 20266549238789639604885581)
                  ·
                    refine ⟨7599955964546114851832093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20266549238789639604885581 7599955964546114851832093)
                    ·
                      refine ⟨2849983486704793069437035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7599955964546114851832093 2849983486704793069437035)
                      ·
                        rfl

theorem cell23_5550323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_5550323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550323 prefixEnd_5550323 := by exact prefixLift 5550323
  have htrace : WordTrace (prefixWord ++ tailWord_5550323) baseStart_5550323 baseEnd_5550323 := by
    simpa [prefixWord, tailWord_5550323, baseEnd_5550323] using wordTrace_append hprefix tailTrace_5550323
  have hstable : (prefixWord ++ tailWord_5550323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550323).length < 2 ^ (prefixWord ++ tailWord_5550323).sum := by decide
  have hdescent : baseEnd_5550323 < baseStart_5550323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550336 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_5550336 : Nat := 118140960795 + 5550336 * 2 ^ 59
def prefixEnd_5550336 : Nat := 4983230072969 + 3 ^ 40 * 5550336 * 2
def baseEnd_5550336 : Nat := 2849990161953301518574475

theorem tailTrace_5550336 : CollatzResearch.WordTrace tailWord_5550336 prefixEnd_5550336 2849990161953301518574475 := by
  unfold tailWord_5550336
  simp only [CollatzResearch.WordTrace]
  refine ⟨101218692410044034382995431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134958256546725379177327241 101218692410044034382995431)
  ·
    refine ⟨151828038615066051574493147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101218692410044034382995431 151828038615066051574493147)
    ·
      refine ⟨227742057922599077361739721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151828038615066051574493147 227742057922599077361739721)
      ·
        refine ⟨170806543441949308021304791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227742057922599077361739721 170806543441949308021304791)
        ·
          refine ⟨256209815162923962031957187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170806543441949308021304791 256209815162923962031957187)
          ·
            refine ⟨384314722744385943047935781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256209815162923962031957187 384314722744385943047935781)
            ·
              refine ⟨72059010514572364321487959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 384314722744385943047935781 72059010514572364321487959)
              ·
                refine ⟨108088515771858546482231939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72059010514572364321487959 108088515771858546482231939)
                ·
                  refine ⟨162132773657787819723347909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108088515771858546482231939 162132773657787819723347909)
                  ·
                    refine ⟨30399895060835216198127733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162132773657787819723347909 30399895060835216198127733)
                    ·
                      refine ⟨2849990161953301518574475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30399895060835216198127733 2849990161953301518574475)
                      ·
                        rfl

theorem cell23_5550336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_5550336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550336 prefixEnd_5550336 := by exact prefixLift 5550336
  have htrace : WordTrace (prefixWord ++ tailWord_5550336) baseStart_5550336 baseEnd_5550336 := by
    simpa [prefixWord, tailWord_5550336, baseEnd_5550336] using wordTrace_append hprefix tailTrace_5550336
  have hstable : (prefixWord ++ tailWord_5550336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550336).length < 2 ^ (prefixWord ++ tailWord_5550336).sum := by decide
  have hdescent : baseEnd_5550336 < baseStart_5550336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550380 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 1, 4, 2]
def baseStart_5550380 : Nat := 118140960795 + 5550380 * 2 ^ 59
def prefixEnd_5550380 : Nat := 4983230072969 + 3 ^ 40 * 5550380 * 2
def baseEnd_5550380 : Nat := 2850012755102099346424273

theorem tailTrace_5550380 : CollatzResearch.WordTrace tailWord_5550380 prefixEnd_5550380 2850012755102099346424273 := by
  unfold tailWord_5550380
  simp only [CollatzResearch.WordTrace]
  refine ⟨101219494815964332140296297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134959326421285776187061729 101219494815964332140296297)
  ·
    refine ⟨75914621111973249105222223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101219494815964332140296297 75914621111973249105222223)
    ·
      refine ⟨113871931667959873657833335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75914621111973249105222223 113871931667959873657833335)
      ·
        refine ⟨170807897501939810486750003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113871931667959873657833335 170807897501939810486750003)
        ·
          refine ⟨256211846252909715730125005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170807897501939810486750003 256211846252909715730125005)
          ·
            refine ⟨96079442344841143398796877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256211846252909715730125005 96079442344841143398796877)
            ·
              refine ⟨36029790879315428774548829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96079442344841143398796877 36029790879315428774548829)
              ·
                refine ⟨13511171579743285790455811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36029790879315428774548829 13511171579743285790455811)
                ·
                  refine ⟨20266757369614928685683717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13511171579743285790455811 20266757369614928685683717)
                  ·
                    refine ⟨3800017006802799128565697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20266757369614928685683717 3800017006802799128565697)
                    ·
                      refine ⟨2850012755102099346424273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800017006802799128565697 2850012755102099346424273)
                      ·
                        rfl

theorem cell23_5550380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_5550380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550380 prefixEnd_5550380 := by exact prefixLift 5550380
  have htrace : WordTrace (prefixWord ++ tailWord_5550380) baseStart_5550380 baseEnd_5550380 := by
    simpa [prefixWord, tailWord_5550380, baseEnd_5550380] using wordTrace_append hprefix tailTrace_5550380
  have hstable : (prefixWord ++ tailWord_5550380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550380).length < 2 ^ (prefixWord ++ tailWord_5550380).sum := by decide
  have hdescent : baseEnd_5550380 < baseStart_5550380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550420 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 7]
def baseStart_5550420 : Nat := 118140960795 + 5550420 * 2 ^ 59
def prefixEnd_5550420 : Nat := 4983230072969 + 3 ^ 40 * 5550420 * 2
def baseEnd_5550420 : Nat := 316670366036475465547121

theorem tailTrace_5550420 : CollatzResearch.WordTrace tailWord_5550420 prefixEnd_5550420 316670366036475465547121 := by
  unfold tailWord_5550420
  simp only [CollatzResearch.WordTrace]
  refine ⟨101220224275891875556024357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134960299034522500741365809 101220224275891875556024357)
  ·
    refine ⟨18978792051729726666754567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101220224275891875556024357 18978792051729726666754567)
    ·
      refine ⟨28468188077594590000131851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18978792051729726666754567 28468188077594590000131851)
      ·
        refine ⟨42702282116391885000197777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28468188077594590000131851 42702282116391885000197777)
        ·
          refine ⟨32026711587293913750148333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42702282116391885000197777 32026711587293913750148333)
          ·
            refine ⟨12010016845235217656305625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32026711587293913750148333 12010016845235217656305625)
            ·
              refine ⟨9007512633926413242229219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12010016845235217656305625 9007512633926413242229219)
              ·
                refine ⟨13511268950889619863343829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007512633926413242229219 13511268950889619863343829)
                ·
                  refine ⟨316670366036475465547121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13511268950889619863343829 316670366036475465547121)
                  ·
                    rfl

theorem cell23_5550420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_5550420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550420 prefixEnd_5550420 := by exact prefixLift 5550420
  have htrace : WordTrace (prefixWord ++ tailWord_5550420) baseStart_5550420 baseEnd_5550420 := by
    simpa [prefixWord, tailWord_5550420, baseEnd_5550420] using wordTrace_append hprefix tailTrace_5550420
  have hstable : (prefixWord ++ tailWord_5550420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550420).length < 2 ^ (prefixWord ++ tailWord_5550420).sum := by decide
  have hdescent : baseEnd_5550420 < baseStart_5550420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550504 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5550504 : Nat := 118140960795 + 5550504 * 2 ^ 59
def prefixEnd_5550504 : Nat := 4983230072969 + 3 ^ 40 * 5550504 * 2
def baseEnd_5550504 : Nat := 2850076426703256861273703

theorem tailTrace_5550504 : CollatzResearch.WordTrace tailWord_5550504 prefixEnd_5550504 2850076426703256861273703 := by
  unfold tailWord_5550504
  simp only [CollatzResearch.WordTrace]
  refine ⟨101221756141739716729053283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134962341522319622305404377 101221756141739716729053283)
  ·
    refine ⟨151832634212609575093579925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101221756141739716729053283 151832634212609575093579925)
    ·
      refine ⟨7117154728716073832511559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151832634212609575093579925 7117154728716073832511559)
      ·
        refine ⟨10675732093074110748767339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7117154728716073832511559 10675732093074110748767339)
        ·
          refine ⟨16013598139611166123151009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675732093074110748767339 16013598139611166123151009)
          ·
            refine ⟨12010198604708374592363257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16013598139611166123151009 12010198604708374592363257)
            ·
              refine ⟨9007648953531280944272443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12010198604708374592363257 9007648953531280944272443)
              ·
                refine ⟨13511473430296921416408665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007648953531280944272443 13511473430296921416408665)
                ·
                  refine ⟨10133605072722691062306499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13511473430296921416408665 10133605072722691062306499)
                  ·
                    refine ⟨15200407609084036593459749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10133605072722691062306499 15200407609084036593459749)
                    ·
                      refine ⟨2850076426703256861273703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15200407609084036593459749 2850076426703256861273703)
                      ·
                        rfl

theorem cell23_5550504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5550504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550504 prefixEnd_5550504 := by exact prefixLift 5550504
  have htrace : WordTrace (prefixWord ++ tailWord_5550504) baseStart_5550504 baseEnd_5550504 := by
    simpa [prefixWord, tailWord_5550504, baseEnd_5550504] using wordTrace_append hprefix tailTrace_5550504
  have hstable : (prefixWord ++ tailWord_5550504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550504).length < 2 ^ (prefixWord ++ tailWord_5550504).sum := by decide
  have hdescent : baseEnd_5550504 < baseStart_5550504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550533 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_5550533 : Nat := 118140960795 + 5550533 * 2 ^ 59
def prefixEnd_5550533 : Nat := 4983230072969 + 3 ^ 40 * 5550533 * 2
def baseEnd_5550533 : Nat := 2850091317642237247811069

theorem tailTrace_5550533 : CollatzResearch.WordTrace tailWord_5550533 prefixEnd_5550533 2850091317642237247811069 := by
  unfold tailWord_5550533
  simp only [CollatzResearch.WordTrace]
  refine ⟨202444570000374371410912253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134963046666916247607274835 202444570000374371410912253)
  ·
    refine ⟨75916713750140389279092095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202444570000374371410912253 75916713750140389279092095)
    ·
      refine ⟨113875070625210583918638143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75916713750140389279092095 113875070625210583918638143)
      ·
        refine ⟨170812605937815875877957215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113875070625210583918638143 170812605937815875877957215)
        ·
          refine ⟨256218908906723813816935823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170812605937815875877957215 256218908906723813816935823)
          ·
            refine ⟨384328363360085720725403735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256218908906723813816935823 384328363360085720725403735)
            ·
              refine ⟨576492545040128581088105603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384328363360085720725403735 576492545040128581088105603)
              ·
                refine ⟨864738817560192871632158405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576492545040128581088105603 864738817560192871632158405)
                ·
                  refine ⟨162138528292536163431029701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864738817560192871632158405 162138528292536163431029701)
                  ·
                    refine ⟨30400974054850530643318069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162138528292536163431029701 30400974054850530643318069)
                    ·
                      refine ⟨2850091317642237247811069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30400974054850530643318069 2850091317642237247811069)
                      ·
                        rfl

theorem cell23_5550533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_5550533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550533 prefixEnd_5550533 := by exact prefixLift 5550533
  have htrace : WordTrace (prefixWord ++ tailWord_5550533) baseStart_5550533 baseEnd_5550533 := by
    simpa [prefixWord, tailWord_5550533, baseEnd_5550533] using wordTrace_append hprefix tailTrace_5550533
  have hstable : (prefixWord ++ tailWord_5550533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550533).length < 2 ^ (prefixWord ++ tailWord_5550533).sum := by decide
  have hdescent : baseEnd_5550533 < baseStart_5550533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550557 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_5550557 : Nat := 118140960795 + 5550557 * 2 ^ 59
def prefixEnd_5550557 : Nat := 4983230072969 + 3 ^ 40 * 5550557 * 2
def baseEnd_5550557 : Nat := 950034547059315051303653

theorem tailTrace_5550557 : CollatzResearch.WordTrace tailWord_5550557 prefixEnd_5550557 950034547059315051303653 := by
  unfold tailWord_5550557
  simp only [CollatzResearch.WordTrace]
  refine ⟨202445445352287423509785925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134963630234858282339857283 202445445352287423509785925)
  ·
    refine ⟨37958521003553891908084861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202445445352287423509785925 37958521003553891908084861)
    ·
      refine ⟨14234445376332709465531823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37958521003553891908084861 14234445376332709465531823)
      ·
        refine ⟨21351668064499064198297735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14234445376332709465531823 21351668064499064198297735)
        ·
          refine ⟨32027502096748596297446603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21351668064499064198297735 32027502096748596297446603)
          ·
            refine ⟨48041253145122894446169905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32027502096748596297446603 48041253145122894446169905)
            ·
              refine ⟨36030939858842170834627429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48041253145122894446169905 36030939858842170834627429)
              ·
                refine ⟨6755801223532907031492643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36030939858842170834627429 6755801223532907031492643)
                ·
                  refine ⟨10133701835299360547238965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6755801223532907031492643 10133701835299360547238965)
                  ·
                    refine ⟨950034547059315051303653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10133701835299360547238965 950034547059315051303653)
                    ·
                      rfl

theorem cell23_5550557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_5550557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550557 prefixEnd_5550557 := by exact prefixLift 5550557
  have htrace : WordTrace (prefixWord ++ tailWord_5550557) baseStart_5550557 baseEnd_5550557 := by
    simpa [prefixWord, tailWord_5550557, baseEnd_5550557] using wordTrace_append hprefix tailTrace_5550557
  have hstable : (prefixWord ++ tailWord_5550557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550557).length < 2 ^ (prefixWord ++ tailWord_5550557).sum := by decide
  have hdescent : baseEnd_5550557 < baseStart_5550557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550560 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_5550560 : Nat := 118140960795 + 5550560 * 2 ^ 59
def prefixEnd_5550560 : Nat := 4983230072969 + 3 ^ 40 * 5550560 * 2
def baseEnd_5550560 : Nat := 2850105181619908642173445

theorem tailTrace_5550560 : CollatzResearch.WordTrace tailWord_5550560 prefixEnd_5550560 2850105181619908642173445 := by
  unfold tailWord_5550560
  simp only [CollatzResearch.WordTrace]
  refine ⟨101222777385638277511072567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134963703180851036681430089 101222777385638277511072567)
  ·
    refine ⟨151834166078457416266608851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101222777385638277511072567 151834166078457416266608851)
    ·
      refine ⟨227751249117686124399913277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151834166078457416266608851 227751249117686124399913277)
      ·
        refine ⟨85406718419132296649967479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227751249117686124399913277 85406718419132296649967479)
        ·
          refine ⟨128110077628698444974951219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85406718419132296649967479 128110077628698444974951219)
          ·
            refine ⟨192165116443047667462426829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128110077628698444974951219 192165116443047667462426829)
            ·
              refine ⟨72061918666142875298410061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192165116443047667462426829 72061918666142875298410061)
              ·
                refine ⟨27023219499803578236903773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72061918666142875298410061 27023219499803578236903773)
                ·
                  refine ⟨10133707312426341838838915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27023219499803578236903773 10133707312426341838838915)
                  ·
                    refine ⟨15200560968639512758258373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10133707312426341838838915 15200560968639512758258373)
                    ·
                      refine ⟨2850105181619908642173445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15200560968639512758258373 2850105181619908642173445)
                      ·
                        rfl

theorem cell23_5550560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_5550560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550560 prefixEnd_5550560 := by exact prefixLift 5550560
  have htrace : WordTrace (prefixWord ++ tailWord_5550560) baseStart_5550560 baseEnd_5550560 := by
    simpa [prefixWord, tailWord_5550560, baseEnd_5550560] using wordTrace_append hprefix tailTrace_5550560
  have hstable : (prefixWord ++ tailWord_5550560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550560).length < 2 ^ (prefixWord ++ tailWord_5550560).sum := by decide
  have hdescent : baseEnd_5550560 < baseStart_5550560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550574 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_5550574 : Nat := 118140960795 + 5550574 * 2 ^ 59
def prefixEnd_5550574 : Nat := 4983230072969 + 3 ^ 40 * 5550574 * 2
def baseEnd_5550574 : Nat := 950037456783023862466127

theorem tailTrace_5550574 : CollatzResearch.WordTrace tailWord_5550574 prefixEnd_5550574 950037456783023862466127 := by
  unfold tailWord_5550574
  simp only [CollatzResearch.WordTrace]
  refine ⟨25305758174153229426644347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134964043595483890275436517 25305758174153229426644347)
  ·
    refine ⟨37958637261229844139966521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25305758174153229426644347 37958637261229844139966521)
    ·
      refine ⟨28468977945922383104974891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37958637261229844139966521 28468977945922383104974891)
      ·
        refine ⟨42703466918883574657462337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28468977945922383104974891 42703466918883574657462337)
        ·
          refine ⟨32027600189162680993096753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42703466918883574657462337 32027600189162680993096753)
          ·
            refine ⟨24020700141872010744822565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32027600189162680993096753 24020700141872010744822565)
            ·
              refine ⟨4503881276601002014654231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24020700141872010744822565 4503881276601002014654231)
              ·
                refine ⟨6755821914901503021981347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503881276601002014654231 6755821914901503021981347)
                ·
                  refine ⟨10133732872352254532972021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6755821914901503021981347 10133732872352254532972021)
                  ·
                    refine ⟨950037456783023862466127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10133732872352254532972021 950037456783023862466127)
                    ·
                      rfl

theorem cell23_5550574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_5550574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550574 prefixEnd_5550574 := by exact prefixLift 5550574
  have htrace : WordTrace (prefixWord ++ tailWord_5550574) baseStart_5550574 baseEnd_5550574 := by
    simpa [prefixWord, tailWord_5550574, baseEnd_5550574] using wordTrace_append hprefix tailTrace_5550574
  have hstable : (prefixWord ++ tailWord_5550574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550574).length < 2 ^ (prefixWord ++ tailWord_5550574).sum := by decide
  have hdescent : baseEnd_5550574 < baseStart_5550574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550577 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_5550577 : Nat := 118140960795 + 5550577 * 2 ^ 59
def prefixEnd_5550577 : Nat := 4983230072969 + 3 ^ 40 * 5550577 * 2
def baseEnd_5550577 : Nat := 2850113910791035075660867

theorem tailTrace_5550577 : CollatzResearch.WordTrace tailWord_5550577 prefixEnd_5550577 2850113910791035075660867 := by
  unfold tailWord_5550577
  simp only [CollatzResearch.WordTrace]
  refine ⟨202446174812214966925513985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134964116541476644617009323 202446174812214966925513985)
  ·
    refine ⟨151834631109161225194135489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202446174812214966925513985 151834631109161225194135489)
    ·
      refine ⟨113875973331870918895601617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151834631109161225194135489 113875973331870918895601617)
      ·
        refine ⟨85406979998903189171701213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113875973331870918895601617 85406979998903189171701213)
        ·
          refine ⟨32027617499588695939387955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85406979998903189171701213 32027617499588695939387955)
          ·
            refine ⟨48041426249383043909081933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32027617499588695939387955 48041426249383043909081933)
            ·
              refine ⟨18015534843518641465905725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48041426249383043909081933 18015534843518641465905725)
              ·
                refine ⟨6755825566319490549714647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18015534843518641465905725 6755825566319490549714647)
                ·
                  refine ⟨10133738349479235824571971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6755825566319490549714647 10133738349479235824571971)
                  ·
                    refine ⟨15200607524218853736857957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10133738349479235824571971 15200607524218853736857957)
                    ·
                      refine ⟨2850113910791035075660867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15200607524218853736857957 2850113910791035075660867)
                      ·
                        rfl

theorem cell23_5550577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_5550577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550577 prefixEnd_5550577 := by exact prefixLift 5550577
  have htrace : WordTrace (prefixWord ++ tailWord_5550577) baseStart_5550577 baseEnd_5550577 := by
    simpa [prefixWord, tailWord_5550577, baseEnd_5550577] using wordTrace_append hprefix tailTrace_5550577
  have hstable : (prefixWord ++ tailWord_5550577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550577).length < 2 ^ (prefixWord ++ tailWord_5550577).sum := by decide
  have hdescent : baseEnd_5550577 < baseStart_5550577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550598 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5550598 : Nat := 118140960795 + 5550598 * 2 ^ 59
def prefixEnd_5550598 : Nat := 4983230072969 + 3 ^ 40 * 5550598 * 2
def baseEnd_5550598 : Nat := 2850124693884779493498271

theorem tailTrace_5550598 : CollatzResearch.WordTrace tailWord_5550598 prefixEnd_5550598 2850124693884779493498271 := by
  unfold tailWord_5550598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326466898285590234750889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134964627163425925008018965 6326466898285590234750889)
  ·
    refine ⟨4744850173714192676063167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6326466898285590234750889 4744850173714192676063167)
    ·
      refine ⟨7117275260571289014094751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4744850173714192676063167 7117275260571289014094751)
      ·
        refine ⟨10675912890856933521142127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7117275260571289014094751 10675912890856933521142127)
        ·
          refine ⟨16013869336285400281713191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675912890856933521142127 16013869336285400281713191)
          ·
            refine ⟨24020804004428100422569787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16013869336285400281713191 24020804004428100422569787)
            ·
              refine ⟨36031206006642150633854681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24020804004428100422569787 36031206006642150633854681)
              ·
                refine ⟨27023404504981612975391011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36031206006642150633854681 27023404504981612975391011)
                ·
                  refine ⟨40535106757472419463086517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27023404504981612975391011 40535106757472419463086517)
                  ·
                    refine ⟨3800166258513039324664361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40535106757472419463086517 3800166258513039324664361)
                    ·
                      refine ⟨2850124693884779493498271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800166258513039324664361 2850124693884779493498271)
                      ·
                        rfl

theorem cell23_5550598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5550598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550598 prefixEnd_5550598 := by exact prefixLift 5550598
  have htrace : WordTrace (prefixWord ++ tailWord_5550598) baseStart_5550598 baseEnd_5550598 := by
    simpa [prefixWord, tailWord_5550598, baseEnd_5550598] using wordTrace_append hprefix tailTrace_5550598
  have hstable : (prefixWord ++ tailWord_5550598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550598).length < 2 ^ (prefixWord ++ tailWord_5550598).sum := by decide
  have hdescent : baseEnd_5550598 < baseStart_5550598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550631 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5550631 : Nat := 118140960795 + 5550631 * 2 ^ 59
def prefixEnd_5550631 : Nat := 4983230072969 + 3 ^ 40 * 5550631 * 2
def baseEnd_5550631 : Nat := 2850141638746377864385619

theorem tailTrace_5550631 : CollatzResearch.WordTrace tailWord_5550631 prefixEnd_5550631 2850141638746377864385619 := by
  unfold tailWord_5550631
  simp only [CollatzResearch.WordTrace]
  refine ⟨202448144354019334147979747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134965429569346222765319831 202448144354019334147979747)
  ·
    refine ⟨303672216531029001221969621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202448144354019334147979747 303672216531029001221969621)
    ·
      refine ⟨7117317574945992216139913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 303672216531029001221969621 7117317574945992216139913)
      ·
        refine ⟨5337988181209494162104935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7117317574945992216139913 5337988181209494162104935)
        ·
          refine ⟨8006982271814241243157403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337988181209494162104935 8006982271814241243157403)
          ·
            refine ⟨12010473407721361864736105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006982271814241243157403 12010473407721361864736105)
            ·
              refine ⟨9007855055791021398552079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12010473407721361864736105 9007855055791021398552079)
              ·
                refine ⟨13511782583686532097828119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007855055791021398552079 13511782583686532097828119)
                ·
                  refine ⟨20267673875529798146742179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13511782583686532097828119 20267673875529798146742179)
                  ·
                    refine ⟨30401510813294697220113269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20267673875529798146742179 30401510813294697220113269)
                    ·
                      refine ⟨2850141638746377864385619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30401510813294697220113269 2850141638746377864385619)
                      ·
                        rfl

theorem cell23_5550631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5550631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550631 prefixEnd_5550631 := by exact prefixLift 5550631
  have htrace : WordTrace (prefixWord ++ tailWord_5550631) baseStart_5550631 baseEnd_5550631 := by
    simpa [prefixWord, tailWord_5550631, baseEnd_5550631] using wordTrace_append hprefix tailTrace_5550631
  have hstable : (prefixWord ++ tailWord_5550631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550631).length < 2 ^ (prefixWord ++ tailWord_5550631).sum := by decide
  have hdescent : baseEnd_5550631 < baseStart_5550631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550661 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 2, 1, 3]
def baseStart_5550661 : Nat := 118140960795 + 5550661 * 2 ^ 59
def prefixEnd_5550661 : Nat := 4983230072969 + 3 ^ 40 * 5550661 * 2
def baseEnd_5550661 : Nat := 2850157043166012747010481

theorem tailTrace_5550661 : CollatzResearch.WordTrace tailWord_5550661 prefixEnd_5550661 2850157043166012747010481 := by
  unfold tailWord_5550661
  simp only [CollatzResearch.WordTrace]
  refine ⟨202449238543910649271571837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134966159029273766181047891 202449238543910649271571837)
  ·
    refine ⟨75918464453966493476839439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202449238543910649271571837 75918464453966493476839439)
    ·
      refine ⟨113877696680949740215259159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75918464453966493476839439 113877696680949740215259159)
      ·
        refine ⟨170816545021424610322888739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113877696680949740215259159 170816545021424610322888739)
        ·
          refine ⟨256224817532136915484333109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170816545021424610322888739 256224817532136915484333109)
          ·
            refine ⟨24021076643637835826656229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256224817532136915484333109 24021076643637835826656229)
            ·
              refine ⟨4503951870682094217498043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24021076643637835826656229 4503951870682094217498043)
              ·
                refine ⟨6755927806023141326247065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503951870682094217498043 6755927806023141326247065)
                ·
                  refine ⟨5066945854517355994685299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6755927806023141326247065 5066945854517355994685299)
                  ·
                    refine ⟨7600418781776033992027949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5066945854517355994685299 7600418781776033992027949)
                    ·
                      refine ⟨2850157043166012747010481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7600418781776033992027949 2850157043166012747010481)
                      ·
                        rfl

theorem cell23_5550661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_5550661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550661 prefixEnd_5550661 := by exact prefixLift 5550661
  have htrace : WordTrace (prefixWord ++ tailWord_5550661) baseStart_5550661 baseEnd_5550661 := by
    simpa [prefixWord, tailWord_5550661, baseEnd_5550661] using wordTrace_append hprefix tailTrace_5550661
  have hstable : (prefixWord ++ tailWord_5550661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550661).length < 2 ^ (prefixWord ++ tailWord_5550661).sum := by decide
  have hdescent : baseEnd_5550661 < baseStart_5550661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550700 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_5550700 : Nat := 118140960795 + 5550700 * 2 ^ 59
def prefixEnd_5550700 : Nat := 4983230072969 + 3 ^ 40 * 5550700 * 2
def baseEnd_5550700 : Nat := 2850177068911538094422801

theorem tailTrace_5550700 : CollatzResearch.WordTrace tailWord_5550700 prefixEnd_5550700 2850177068911538094422801 := by
  unfold tailWord_5550700
  simp only [CollatzResearch.WordTrace]
  refine ⟨101225330495384679466120777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134967107327179572621494369 101225330495384679466120777)
  ·
    refine ⟨75918997871538509599590583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101225330495384679466120777 75918997871538509599590583)
    ·
      refine ⟨113878496807307764399385875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75918997871538509599590583 113878496807307764399385875)
      ·
        refine ⟨170817745210961646599078813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113878496807307764399385875 170817745210961646599078813)
        ·
          refine ⟨64056654454110617474654555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170817745210961646599078813 64056654454110617474654555)
          ·
            refine ⟨96084981681165926211981833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64056654454110617474654555 96084981681165926211981833)
            ·
              refine ⟨72063736260874444658986375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96084981681165926211981833 72063736260874444658986375)
              ·
                refine ⟨108095604391311666988479563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72063736260874444658986375 108095604391311666988479563)
                ·
                  refine ⟨162143406586967500482719345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108095604391311666988479563 162143406586967500482719345)
                  ·
                    refine ⟨121607554940225625362039509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162143406586967500482719345 121607554940225625362039509)
                    ·
                      refine ⟨2850177068911538094422801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121607554940225625362039509 2850177068911538094422801)
                      ·
                        rfl

theorem cell23_5550700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_5550700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550700 prefixEnd_5550700 := by exact prefixLift 5550700
  have htrace : WordTrace (prefixWord ++ tailWord_5550700) baseStart_5550700 baseEnd_5550700 := by
    simpa [prefixWord, tailWord_5550700, baseEnd_5550700] using wordTrace_append hprefix tailTrace_5550700
  have hstable : (prefixWord ++ tailWord_5550700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550700).length < 2 ^ (prefixWord ++ tailWord_5550700).sum := by decide
  have hdescent : baseEnd_5550700 < baseStart_5550700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550757 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_5550757 : Nat := 118140960795 + 5550757 * 2 ^ 59
def prefixEnd_5550757 : Nat := 4983230072969 + 3 ^ 40 * 5550757 * 2
def baseEnd_5550757 : Nat := 2850206337308844371410039

theorem tailTrace_5550757 : CollatzResearch.WordTrace tailWord_5550757 prefixEnd_5550757 2850206337308844371410039 := by
  unfold tailWord_5550757
  simp only [CollatzResearch.WordTrace]
  refine ⟨202452739951562857667066525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134968493301041905111377683 202452739951562857667066525)
  ·
    refine ⟨75919777481836071625149947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202452739951562857667066525 75919777481836071625149947)
    ·
      refine ⟨113879666222754107437724921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75919777481836071625149947 113879666222754107437724921)
      ·
        refine ⟨85409749667065580578293691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113879666222754107437724921 85409749667065580578293691)
        ·
          refine ⟨128114624500598370867440537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85409749667065580578293691 128114624500598370867440537)
          ·
            refine ⟨96085968375448778150580403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128114624500598370867440537 96085968375448778150580403)
            ·
              refine ⟨144128952563173167225870605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96085968375448778150580403 144128952563173167225870605)
              ·
                refine ⟨54048357211189937709701477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144128952563173167225870605 54048357211189937709701477)
                ·
                  refine ⟨10134066977098113320569027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54048357211189937709701477 10134066977098113320569027)
                  ·
                    refine ⟨15201100465647169980853541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10134066977098113320569027 15201100465647169980853541)
                    ·
                      refine ⟨2850206337308844371410039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15201100465647169980853541 2850206337308844371410039)
                      ·
                        rfl

theorem cell23_5550757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_5550757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550757 prefixEnd_5550757 := by exact prefixLift 5550757
  have htrace : WordTrace (prefixWord ++ tailWord_5550757) baseStart_5550757 baseEnd_5550757 := by
    simpa [prefixWord, tailWord_5550757, baseEnd_5550757] using wordTrace_append hprefix tailTrace_5550757
  have hstable : (prefixWord ++ tailWord_5550757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550757).length < 2 ^ (prefixWord ++ tailWord_5550757).sum := by decide
  have hdescent : baseEnd_5550757 < baseStart_5550757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550784 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 3, 4]
def baseStart_5550784 : Nat := 118140960795 + 5550784 * 2 ^ 59
def prefixEnd_5550784 : Nat := 4983230072969 + 3 ^ 40 * 5550784 * 2
def baseEnd_5550784 : Nat := 950073400428838588590805

theorem tailTrace_5550784 : CollatzResearch.WordTrace tailWord_5550784 prefixEnd_5550784 950073400428838588590805 := by
  unfold tailWord_5550784
  simp only [CollatzResearch.WordTrace]
  refine ⟨101226862361232520639149703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134969149814976694185532937 101226862361232520639149703)
  ·
    refine ⟨151840293541848780958724555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101226862361232520639149703 151840293541848780958724555)
    ·
      refine ⟨227760440312773171438086833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151840293541848780958724555 227760440312773171438086833)
      ·
        refine ⟨170820330234579878578565125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227760440312773171438086833 170820330234579878578565125)
        ·
          refine ⟨32028811918983727233480961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170820330234579878578565125 32028811918983727233480961)
          ·
            refine ⟨24021608939237795425110721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32028811918983727233480961 24021608939237795425110721)
            ·
              refine ⟨18016206704428346568833041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24021608939237795425110721 18016206704428346568833041)
              ·
                refine ⟨13512155028321259926624781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18016206704428346568833041 13512155028321259926624781)
                ·
                  refine ⟨5067058135620472472484293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13512155028321259926624781 5067058135620472472484293)
                  ·
                    refine ⟨950073400428838588590805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067058135620472472484293 950073400428838588590805)
                    ·
                      rfl

theorem cell23_5550784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_5550784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550784 prefixEnd_5550784 := by exact prefixLift 5550784
  have htrace : WordTrace (prefixWord ++ tailWord_5550784) baseStart_5550784 baseEnd_5550784 := by
    simpa [prefixWord, tailWord_5550784, baseEnd_5550784] using wordTrace_append hprefix tailTrace_5550784
  have hstable : (prefixWord ++ tailWord_5550784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550784).length < 2 ^ (prefixWord ++ tailWord_5550784).sum := by decide
  have hdescent : baseEnd_5550784 < baseStart_5550784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550794 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_5550794 : Nat := 118140960795 + 5550794 * 2 ^ 59
def prefixEnd_5550794 : Nat := 4983230072969 + 3 ^ 40 * 5550794 * 2
def baseEnd_5550794 : Nat := 2850225336093060726647369

theorem tailTrace_5550794 : CollatzResearch.WordTrace tailWord_5550794 prefixEnd_5550794 2850225336093060726647369 := by
  unfold tailWord_5550794
  simp only [CollatzResearch.WordTrace]
  refine ⟨50613522363107203246540859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134969392968285875324108957 50613522363107203246540859)
  ·
    refine ⟨75920283544660804869811289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50613522363107203246540859 75920283544660804869811289)
    ·
      refine ⟨56940212658495603652358467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75920283544660804869811289 56940212658495603652358467)
      ·
        refine ⟨85410318987743405478537701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56940212658495603652358467 85410318987743405478537701)
        ·
          refine ⟨16014434810201888527225819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85410318987743405478537701 16014434810201888527225819)
          ·
            refine ⟨24021652215302832790838729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16014434810201888527225819 24021652215302832790838729)
            ·
              refine ⟨18016239161477124593129047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24021652215302832790838729 18016239161477124593129047)
              ·
                refine ⟨27024358742215686889693571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18016239161477124593129047 27024358742215686889693571)
                ·
                  refine ⟨40536538113323530334540357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27024358742215686889693571 40536538113323530334540357)
                  ·
                    refine ⟨7600600896248161937726317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40536538113323530334540357 7600600896248161937726317)
                    ·
                      refine ⟨2850225336093060726647369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7600600896248161937726317 2850225336093060726647369)
                      ·
                        rfl

theorem cell23_5550794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_5550794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550794 prefixEnd_5550794 := by exact prefixLift 5550794
  have htrace : WordTrace (prefixWord ++ tailWord_5550794) baseStart_5550794 baseEnd_5550794 := by
    simpa [prefixWord, tailWord_5550794, baseEnd_5550794] using wordTrace_append hprefix tailTrace_5550794
  have hstable : (prefixWord ++ tailWord_5550794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550794).length < 2 ^ (prefixWord ++ tailWord_5550794).sum := by decide
  have hdescent : baseEnd_5550794 < baseStart_5550794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550827 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 3, 5]
def baseStart_5550827 : Nat := 118140960795 + 5550827 * 2 ^ 59
def prefixEnd_5550827 : Nat := 4983230072969 + 3 ^ 40 * 5550827 * 2
def baseEnd_5550827 : Nat := 950080760318219699178239

theorem tailTrace_5550827 : CollatzResearch.WordTrace tailWord_5550827 prefixEnd_5550827 950080760318219699178239 := by
  unfold tailWord_5550827
  simp only [CollatzResearch.WordTrace]
  refine ⟨202455293061309259622114735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134970195374206173081409823 202455293061309259622114735)
  ·
    refine ⟨303682939591963889433172103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202455293061309259622114735 303682939591963889433172103)
    ·
      refine ⟨455524409387945834149758155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303682939591963889433172103 455524409387945834149758155)
      ·
        refine ⟨683286614081918751224637233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455524409387945834149758155 683286614081918751224637233)
        ·
          refine ⟨512464960561439063418477925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683286614081918751224637233 512464960561439063418477925)
          ·
            refine ⟨96087180105269824390964611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 512464960561439063418477925 96087180105269824390964611)
            ·
              refine ⟨144130770157904736586446917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96087180105269824390964611 144130770157904736586446917)
              ·
                refine ⟨27024519404607138109958797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144130770157904736586446917 27024519404607138109958797)
                ·
                  refine ⟨10134194776727676791234549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27024519404607138109958797 10134194776727676791234549)
                  ·
                    refine ⟨950080760318219699178239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10134194776727676791234549 950080760318219699178239)
                    ·
                      rfl

theorem cell23_5550827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 5].length) (baseStart_5550827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550827 prefixEnd_5550827 := by exact prefixLift 5550827
  have htrace : WordTrace (prefixWord ++ tailWord_5550827) baseStart_5550827 baseEnd_5550827 := by
    simpa [prefixWord, tailWord_5550827, baseEnd_5550827] using wordTrace_append hprefix tailTrace_5550827
  have hstable : (prefixWord ++ tailWord_5550827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550827).length < 2 ^ (prefixWord ++ tailWord_5550827).sum := by decide
  have hdescent : baseEnd_5550827 < baseStart_5550827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550831 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 6]
def baseStart_5550831 : Nat := 118140960795 + 5550831 * 2 ^ 59
def prefixEnd_5550831 : Nat := 4983230072969 + 3 ^ 40 * 5550831 * 2
def baseEnd_5550831 : Nat := 316693814986364120209411

theorem tailTrace_5550831 : CollatzResearch.WordTrace tailWord_5550831 prefixEnd_5550831 316693814986364120209411 := by
  unfold tailWord_5550831
  simp only [CollatzResearch.WordTrace]
  refine ⟨202455438953294768305260347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134970292635529845536840231 202455438953294768305260347)
  ·
    refine ⟨303683158429942152457890521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202455438953294768305260347 303683158429942152457890521)
    ·
      refine ⟨227762368822456614343417891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303683158429942152457890521 227762368822456614343417891)
      ·
        refine ⟨341643553233684921515126837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227762368822456614343417891 341643553233684921515126837)
        ·
          refine ⟨32029083115657961392043141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 341643553233684921515126837 32029083115657961392043141)
          ·
            refine ⟨6005453084185867761008089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32029083115657961392043141 6005453084185867761008089)
            ·
              refine ⟨4504089813139400820756067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6005453084185867761008089 4504089813139400820756067)
              ·
                refine ⟨6756134719709101231134101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504089813139400820756067 6756134719709101231134101)
                ·
                  refine ⟨316693814986364120209411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6756134719709101231134101 316693814986364120209411)
                  ·
                    rfl

theorem cell23_5550831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 6].length) (baseStart_5550831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550831 prefixEnd_5550831 := by exact prefixLift 5550831
  have htrace : WordTrace (prefixWord ++ tailWord_5550831) baseStart_5550831 baseEnd_5550831 := by
    simpa [prefixWord, tailWord_5550831, baseEnd_5550831] using wordTrace_append hprefix tailTrace_5550831
  have hstable : (prefixWord ++ tailWord_5550831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550831).length < 2 ^ (prefixWord ++ tailWord_5550831).sum := by decide
  have hdescent : baseEnd_5550831 < baseStart_5550831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550844 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_5550844 : Nat := 118140960795 + 5550844 * 2 ^ 59
def prefixEnd_5550844 : Nat := 4983230072969 + 3 ^ 40 * 5550844 * 2
def baseEnd_5550844 : Nat := 950083670041928510340713

theorem tailTrace_5550844 : CollatzResearch.WordTrace tailWord_5550844 prefixEnd_5550844 950083670041928510340713 := by
  unfold tailWord_5550844
  simp only [CollatzResearch.WordTrace]
  refine ⟨101227956551123835762741793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134970608734831781016989057 101227956551123835762741793)
  ·
    refine ⟨75920967413342876822056345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101227956551123835762741793 75920967413342876822056345)
    ·
      refine ⟨56940725560007157616542259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75920967413342876822056345 56940725560007157616542259)
      ·
        refine ⟨85411088340010736424813389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56940725560007157616542259 85411088340010736424813389)
        ·
          refine ⟨32029158127504026159305021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85411088340010736424813389 32029158127504026159305021)
          ·
            refine ⟨12010934297814009809739383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32029158127504026159305021 12010934297814009809739383)
            ·
              refine ⟨18016401446721014714609075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12010934297814009809739383 18016401446721014714609075)
              ·
                refine ⟨27024602170081522071913613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18016401446721014714609075 27024602170081522071913613)
                ·
                  refine ⟨10134225813780570776967605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27024602170081522071913613 10134225813780570776967605)
                  ·
                    refine ⟨950083670041928510340713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10134225813780570776967605 950083670041928510340713)
                    ·
                      rfl

theorem cell23_5550844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_5550844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550844 prefixEnd_5550844 := by exact prefixLift 5550844
  have htrace : WordTrace (prefixWord ++ tailWord_5550844) baseStart_5550844 baseEnd_5550844 := by
    simpa [prefixWord, tailWord_5550844, baseEnd_5550844] using wordTrace_append hprefix tailTrace_5550844
  have hstable : (prefixWord ++ tailWord_5550844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550844).length < 2 ^ (prefixWord ++ tailWord_5550844).sum := by decide
  have hdescent : baseEnd_5550844 < baseStart_5550844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550857 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_5550857 : Nat := 118140960795 + 5550857 * 2 ^ 59
def prefixEnd_5550857 : Nat := 4983230072969 + 3 ^ 40 * 5550857 * 2
def baseEnd_5550857 : Nat := 950085895124764660053193

theorem tailTrace_5550857 : CollatzResearch.WordTrace tailWord_5550857 prefixEnd_5550857 950085895124764660053193 := by
  unfold tailWord_5550857
  simp only [CollatzResearch.WordTrace]
  refine ⟨202456387251200574745706825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134970924834133716497137883 202456387251200574745706825)
  ·
    refine ⟨151842290438400431059280119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202456387251200574745706825 151842290438400431059280119)
    ·
      refine ⟨227763435657600646588920179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151842290438400431059280119 227763435657600646588920179)
      ·
        refine ⟨341645153486400969883380269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227763435657600646588920179 341645153486400969883380269)
        ·
          refine ⟨128116932557400363706267601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341645153486400969883380269 128116932557400363706267601)
          ·
            refine ⟨96087699418050272779700701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128116932557400363706267601 96087699418050272779700701)
            ·
              refine ⟨36032887281768852292387763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96087699418050272779700701 36032887281768852292387763)
              ·
                refine ⟨54049330922653278438581645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36032887281768852292387763 54049330922653278438581645)
                ·
                  refine ⟨20268499095994979414468117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54049330922653278438581645 20268499095994979414468117)
                  ·
                    refine ⟨950085895124764660053193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20268499095994979414468117 950085895124764660053193)
                    ·
                      rfl

theorem cell23_5550857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_5550857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550857 prefixEnd_5550857 := by exact prefixLift 5550857
  have htrace : WordTrace (prefixWord ++ tailWord_5550857) baseStart_5550857 baseEnd_5550857 := by
    simpa [prefixWord, tailWord_5550857, baseEnd_5550857] using wordTrace_append hprefix tailTrace_5550857
  have hstable : (prefixWord ++ tailWord_5550857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550857).length < 2 ^ (prefixWord ++ tailWord_5550857).sum := by decide
  have hdescent : baseEnd_5550857 < baseStart_5550857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550858 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_5550858 : Nat := 118140960795 + 5550858 * 2 ^ 59
def prefixEnd_5550858 : Nat := 4983230072969 + 3 ^ 40 * 5550858 * 2
def baseEnd_5550858 : Nat := 2850258198854948476247075

theorem tailTrace_5550858 : CollatzResearch.WordTrace tailWord_5550858 prefixEnd_5550858 2850258198854948476247075 := by
  unfold tailWord_5550858
  simp only [CollatzResearch.WordTrace]
  refine ⟨50614105931049237979123307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134970949149464634610995485 50614105931049237979123307)
  ·
    refine ⟨75921158896573856968684961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50614105931049237979123307 75921158896573856968684961)
    ·
      refine ⟨56940869172430392726513721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75921158896573856968684961 56940869172430392726513721)
      ·
        refine ⟨42705651879322794544885291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56940869172430392726513721 42705651879322794544885291)
        ·
          refine ⟨64058477818984191817327937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42705651879322794544885291 64058477818984191817327937)
          ·
            refine ⟨48043858364238143862995953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64058477818984191817327937 48043858364238143862995953)
            ·
              refine ⟨36032893773178607897246965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48043858364238143862995953 36032893773178607897246965)
              ·
                refine ⟨3378083791235494490366903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36032893773178607897246965 3378083791235494490366903)
                ·
                  refine ⟨5067125686853241735550355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378083791235494490366903 5067125686853241735550355)
                  ·
                    refine ⟨7600688530279862603325533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5067125686853241735550355 7600688530279862603325533)
                    ·
                      refine ⟨2850258198854948476247075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7600688530279862603325533 2850258198854948476247075)
                      ·
                        rfl

theorem cell23_5550858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_5550858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550858 prefixEnd_5550858 := by exact prefixLift 5550858
  have htrace : WordTrace (prefixWord ++ tailWord_5550858) baseStart_5550858 baseEnd_5550858 := by
    simpa [prefixWord, tailWord_5550858, baseEnd_5550858] using wordTrace_append hprefix tailTrace_5550858
  have hstable : (prefixWord ++ tailWord_5550858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550858).length < 2 ^ (prefixWord ++ tailWord_5550858).sum := by decide
  have hdescent : baseEnd_5550858 < baseStart_5550858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550898 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_5550898 : Nat := 118140960795 + 5550898 * 2 ^ 59
def prefixEnd_5550898 : Nat := 4983230072969 + 3 ^ 40 * 5550898 * 2
def baseEnd_5550898 : Nat := 2850278738081128319746891

theorem tailTrace_5550898 : CollatzResearch.WordTrace tailWord_5550898 prefixEnd_5550898 2850278738081128319746891 := by
  unfold tailWord_5550898
  simp only [CollatzResearch.WordTrace]
  refine ⟨50614470661013009686987337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134971921762701359165299565 50614470661013009686987337)
  ·
    refine ⟨37960852995759757265240503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50614470661013009686987337 37960852995759757265240503)
    ·
      refine ⟨56941279493639635897860755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37960852995759757265240503 56941279493639635897860755)
      ·
        refine ⟨85411919240459453846791133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56941279493639635897860755 85411919240459453846791133)
        ·
          refine ⟨32029469715172295192546675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85411919240459453846791133 32029469715172295192546675)
          ·
            refine ⟨48044204572758442788820013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32029469715172295192546675 48044204572758442788820013)
            ·
              refine ⟨18016576714784416045807505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48044204572758442788820013 18016576714784416045807505)
              ·
                refine ⟨13512432536088312034355629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18016576714784416045807505 13512432536088312034355629)
                ·
                  refine ⟨5067162201033117012883361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13512432536088312034355629 5067162201033117012883361)
                  ·
                    refine ⟨3800371650774837759662521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067162201033117012883361 3800371650774837759662521)
                    ·
                      refine ⟨2850278738081128319746891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800371650774837759662521 2850278738081128319746891)
                      ·
                        rfl

theorem cell23_5550898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_5550898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550898 prefixEnd_5550898 := by exact prefixLift 5550898
  have htrace : WordTrace (prefixWord ++ tailWord_5550898) baseStart_5550898 baseEnd_5550898 := by
    simpa [prefixWord, tailWord_5550898, baseEnd_5550898] using wordTrace_append hprefix tailTrace_5550898
  have hstable : (prefixWord ++ tailWord_5550898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550898).length < 2 ^ (prefixWord ++ tailWord_5550898).sum := by decide
  have hdescent : baseEnd_5550898 < baseStart_5550898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550901 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_5550901 : Nat := 118140960795 + 5550901 * 2 ^ 59
def prefixEnd_5550901 : Nat := 4983230072969 + 3 ^ 40 * 5550901 * 2
def baseEnd_5550901 : Nat := 2850280278523091808009377

theorem tailTrace_5550901 : CollatzResearch.WordTrace tailWord_5550901 prefixEnd_5550901 2850280278523091808009377 := by
  unfold tailWord_5550901
  simp only [CollatzResearch.WordTrace]
  refine ⟨202457992063041170260308557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134971994708694113506872371 202457992063041170260308557)
  ·
    refine ⟨75921747023640438847615709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202457992063041170260308557 75921747023640438847615709)
    ·
      refine ⟨28470655133865164567855891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75921747023640438847615709 28470655133865164567855891)
      ·
        refine ⟨42705982700797746851783837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28470655133865164567855891 42705982700797746851783837)
        ·
          refine ⟨16014743512799155069418939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42705982700797746851783837 16014743512799155069418939)
          ·
            refine ⟨24022115269198732604128409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16014743512799155069418939 24022115269198732604128409)
            ·
              refine ⟨18016586451899049453096307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24022115269198732604128409 18016586451899049453096307)
              ·
                refine ⟨27024879677848574179644461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18016586451899049453096307 27024879677848574179644461)
                ·
                  refine ⟨10134329879193215317366673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27024879677848574179644461 10134329879193215317366673)
                  ·
                    refine ⟨7600747409394911488025005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10134329879193215317366673 7600747409394911488025005)
                    ·
                      refine ⟨2850280278523091808009377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7600747409394911488025005 2850280278523091808009377)
                      ·
                        rfl

theorem cell23_5550901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_5550901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550901 prefixEnd_5550901 := by exact prefixLift 5550901
  have htrace : WordTrace (prefixWord ++ tailWord_5550901) baseStart_5550901 baseEnd_5550901 := by
    simpa [prefixWord, tailWord_5550901, baseEnd_5550901] using wordTrace_append hprefix tailTrace_5550901
  have hstable : (prefixWord ++ tailWord_5550901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550901).length < 2 ^ (prefixWord ++ tailWord_5550901).sum := by decide
  have hdescent : baseEnd_5550901 < baseStart_5550901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550902 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5550902 : Nat := 118140960795 + 5550902 * 2 ^ 59
def prefixEnd_5550902 : Nat := 4983230072969 + 3 ^ 40 * 5550902 * 2
def baseEnd_5550902 : Nat := 2850280792003746304096873

theorem tailTrace_5550902 : CollatzResearch.WordTrace tailWord_5550902 prefixEnd_5550902 2850280792003746304096873 := by
  unfold tailWord_5550902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12653626783502346714443435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134972019024025031620729973 12653626783502346714443435)
  ·
    refine ⟨18980440175253520071665153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12653626783502346714443435 18980440175253520071665153)
    ·
      refine ⟨14235330131440140053748865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18980440175253520071665153 14235330131440140053748865)
      ·
        refine ⟨10676497598580105040311649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14235330131440140053748865 10676497598580105040311649)
        ·
          refine ⟨8007373198935078780233737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10676497598580105040311649 8007373198935078780233737)
          ·
            refine ⟨6005529899201309085175303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8007373198935078780233737 6005529899201309085175303)
            ·
              refine ⟨9008294848801963627762955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005529899201309085175303 9008294848801963627762955)
              ·
                refine ⟨13512442273202945441644433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9008294848801963627762955 13512442273202945441644433)
                ·
                  refine ⟨10134331704902209081233325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13512442273202945441644433 10134331704902209081233325)
                  ·
                    refine ⟨3800374389338328405462497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10134331704902209081233325 3800374389338328405462497)
                    ·
                      refine ⟨2850280792003746304096873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800374389338328405462497 2850280792003746304096873)
                      ·
                        rfl

theorem cell23_5550902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5550902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550902 prefixEnd_5550902 := by exact prefixLift 5550902
  have htrace : WordTrace (prefixWord ++ tailWord_5550902) baseStart_5550902 baseEnd_5550902 := by
    simpa [prefixWord, tailWord_5550902, baseEnd_5550902] using wordTrace_append hprefix tailTrace_5550902
  have hstable : (prefixWord ++ tailWord_5550902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550902).length < 2 ^ (prefixWord ++ tailWord_5550902).sum := by decide
  have hdescent : baseEnd_5550902 < baseStart_5550902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550904 : List Nat := [2, 1, 2, 1, 3, 2, 5, 7]
def baseStart_5550904 : Nat := 118140960795 + 5550904 * 2 ^ 59
def prefixEnd_5550904 : Nat := 4983230072969 + 3 ^ 40 * 5550904 * 2
def baseEnd_5550904 : Nat := 105565993295002048010069

theorem tailTrace_5550904 : CollatzResearch.WordTrace tailWord_5550904 prefixEnd_5550904 105565993295002048010069 := by
  unfold tailWord_5550904
  simp only [CollatzResearch.WordTrace]
  refine ⟨101229050741015150886333883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134972067654686867848445177 101229050741015150886333883)
  ·
    refine ⟨151843576111522726329500825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101229050741015150886333883 151843576111522726329500825)
    ·
      refine ⟨113882682083642044747125619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151843576111522726329500825 113882682083642044747125619)
      ·
        refine ⟨170824023125463067120688429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113882682083642044747125619 170824023125463067120688429)
        ·
          refine ⟨64059008672048650170258161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170824023125463067120688429 64059008672048650170258161)
          ·
            refine ⟨48044256504036487627693621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64059008672048650170258161 48044256504036487627693621)
            ·
              refine ⟨4504149047253420715096277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48044256504036487627693621 4504149047253420715096277)
              ·
                refine ⟨105565993295002048010069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4504149047253420715096277 105565993295002048010069)
                ·
                  rfl

theorem cell23_5550904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 7].length) (baseStart_5550904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550904 prefixEnd_5550904 := by exact prefixLift 5550904
  have htrace : WordTrace (prefixWord ++ tailWord_5550904) baseStart_5550904 baseEnd_5550904 := by
    simpa [prefixWord, tailWord_5550904, baseEnd_5550904] using wordTrace_append hprefix tailTrace_5550904
  have hstable : (prefixWord ++ tailWord_5550904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550904).length < 2 ^ (prefixWord ++ tailWord_5550904).sum := by decide
  have hdescent : baseEnd_5550904 < baseStart_5550904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550915 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 1, 2, 2]
def baseStart_5550915 : Nat := 118140960795 + 5550915 * 2 ^ 59
def prefixEnd_5550915 : Nat := 4983230072969 + 3 ^ 40 * 5550915 * 2
def baseEnd_5550915 : Nat := 2850287467252254753234313

theorem tailTrace_5550915 : CollatzResearch.WordTrace tailWord_5550915 prefixEnd_5550915 2850287467252254753234313 := by
  unfold tailWord_5550915
  simp only [CollatzResearch.WordTrace]
  refine ⟨202458502684990450651318199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134972335123326967100878799 202458502684990450651318199)
  ·
    refine ⟨303687754027485675976977299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202458502684990450651318199 303687754027485675976977299)
    ·
      refine ⟨455531631041228513965465949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303687754027485675976977299 455531631041228513965465949)
      ·
        refine ⟨170824361640460692737049731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455531631041228513965465949 170824361640460692737049731)
        ·
          refine ⟨256236542460691039105574597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170824361640460692737049731 256236542460691039105574597)
          ·
            refine ⟨48044351711379569832295237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256236542460691039105574597 48044351711379569832295237)
            ·
              refine ⟨9008315945883669343555357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48044351711379569832295237 9008315945883669343555357)
              ·
                refine ⟨3378118479706376003833259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9008315945883669343555357 3378118479706376003833259)
                ·
                  refine ⟨5067177719559564005749889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378118479706376003833259 5067177719559564005749889)
                  ·
                    refine ⟨3800383289669673004312417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067177719559564005749889 3800383289669673004312417)
                    ·
                      refine ⟨2850287467252254753234313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800383289669673004312417 2850287467252254753234313)
                      ·
                        rfl

theorem cell23_5550915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_5550915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550915 prefixEnd_5550915 := by exact prefixLift 5550915
  have htrace : WordTrace (prefixWord ++ tailWord_5550915) baseStart_5550915 baseEnd_5550915 := by
    simpa [prefixWord, tailWord_5550915, baseEnd_5550915] using wordTrace_append hprefix tailTrace_5550915
  have hstable : (prefixWord ++ tailWord_5550915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550915).length < 2 ^ (prefixWord ++ tailWord_5550915).sum := by decide
  have hdescent : baseEnd_5550915 < baseStart_5550915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550917 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_5550917 : Nat := 118140960795 + 5550917 * 2 ^ 59
def prefixEnd_5550917 : Nat := 4983230072969 + 3 ^ 40 * 5550917 * 2
def baseEnd_5550917 : Nat := 950096164737854581803101

theorem tailTrace_5550917 : CollatzResearch.WordTrace tailWord_5550917 prefixEnd_5550917 950096164737854581803101 := by
  unfold tailWord_5550917
  simp only [CollatzResearch.WordTrace]
  refine ⟨202458575630983204992891005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134972383753988803328594003 202458575630983204992891005)
  ·
    refine ⟨75921965861618701872334127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202458575630983204992891005 75921965861618701872334127)
    ·
      refine ⟨113882948792428052808501191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75921965861618701872334127 113882948792428052808501191)
      ·
        refine ⟨170824423188642079212751787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113882948792428052808501191 170824423188642079212751787)
        ·
          refine ⟨256236634782963118819127681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170824423188642079212751787 256236634782963118819127681)
          ·
            refine ⟨192177476087222339114345761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256236634782963118819127681 192177476087222339114345761)
            ·
              refine ⟨144133107065416754335759321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192177476087222339114345761 144133107065416754335759321)
              ·
                refine ⟨108099830299062565751819491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144133107065416754335759321 108099830299062565751819491)
                ·
                  refine ⟨162149745448593848627729237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108099830299062565751819491 162149745448593848627729237)
                  ·
                    refine ⟨950096164737854581803101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162149745448593848627729237 950096164737854581803101)
                    ·
                      rfl

theorem cell23_5550917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_5550917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550917 prefixEnd_5550917 := by exact prefixLift 5550917
  have htrace : WordTrace (prefixWord ++ tailWord_5550917) baseStart_5550917 baseEnd_5550917 := by
    simpa [prefixWord, tailWord_5550917, baseEnd_5550917] using wordTrace_append hprefix tailTrace_5550917
  have hstable : (prefixWord ++ tailWord_5550917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550917).length < 2 ^ (prefixWord ++ tailWord_5550917).sum := by decide
  have hdescent : baseEnd_5550917 < baseStart_5550917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550948 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_5550948 : Nat := 118140960795 + 5550948 * 2 ^ 59
def prefixEnd_5550948 : Nat := 4983230072969 + 3 ^ 40 * 5550948 * 2
def baseEnd_5550948 : Nat := 2850304412113853124121661

theorem tailTrace_5550948 : CollatzResearch.WordTrace tailWord_5550948 prefixEnd_5550948 2850304412113853124121661 := by
  unfold tailWord_5550948
  simp only [CollatzResearch.WordTrace]
  refine ⟨101229853146935448643634749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134973137529247264858179665 101229853146935448643634749)
  ·
    refine ⟨37961194930100793241363031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101229853146935448643634749 37961194930100793241363031)
    ·
      refine ⟨56941792395151189862044547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37961194930100793241363031 56941792395151189862044547)
      ·
        refine ⟨85412688592726784793066821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56941792395151189862044547 85412688592726784793066821)
        ·
          refine ⟨16014879111136272148700029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85412688592726784793066821 16014879111136272148700029)
          ·
            refine ⟨6005579666676102055762511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16014879111136272148700029 6005579666676102055762511)
            ·
              refine ⟨9008369500014153083643767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005579666676102055762511 9008369500014153083643767)
              ·
                refine ⟨13512554250021229625465651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9008369500014153083643767 13512554250021229625465651)
                ·
                  refine ⟨20268831375031844438198477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13512554250021229625465651 20268831375031844438198477)
                  ·
                    refine ⟨7600811765636941664324429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20268831375031844438198477 7600811765636941664324429)
                    ·
                      refine ⟨2850304412113853124121661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7600811765636941664324429 2850304412113853124121661)
                      ·
                        rfl

theorem cell23_5550948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_5550948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550948 prefixEnd_5550948 := by exact prefixLift 5550948
  have htrace : WordTrace (prefixWord ++ tailWord_5550948) baseStart_5550948 baseEnd_5550948 := by
    simpa [prefixWord, tailWord_5550948, baseEnd_5550948] using wordTrace_append hprefix tailTrace_5550948
  have hstable : (prefixWord ++ tailWord_5550948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550948).length < 2 ^ (prefixWord ++ tailWord_5550948).sum := by decide
  have hdescent : baseEnd_5550948 < baseStart_5550948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550971 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 1, 4, 2]
def baseStart_5550971 : Nat := 118140960795 + 5550971 * 2 ^ 59
def prefixEnd_5550971 : Nat := 4983230072969 + 3 ^ 40 * 5550971 * 2
def baseEnd_5550971 : Nat := 2850316222168906534134055

theorem tailTrace_5550971 : CollatzResearch.WordTrace tailWord_5550971 prefixEnd_5550971 2850316222168906534134055 := by
  unfold tailWord_5550971
  simp only [CollatzResearch.WordTrace]
  refine ⟨202460545172787572215356767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134973696781858381476904511 202460545172787572215356767)
  ·
    refine ⟨303690817759181358323035151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202460545172787572215356767 303690817759181358323035151)
    ·
      refine ⟨455536226638772037484552727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303690817759181358323035151 455536226638772037484552727)
      ·
        refine ⟨683304339958158056226829091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455536226638772037484552727 683304339958158056226829091)
        ·
          refine ⟨1024956509937237084340243637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683304339958158056226829091 1024956509937237084340243637)
          ·
            refine ⟨96089672806615976656897841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1024956509937237084340243637 96089672806615976656897841)
            ·
              refine ⟨72067254604961982492673381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96089672806615976656897841 72067254604961982492673381)
              ·
                refine ⟨13512610238430371717376259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72067254604961982492673381 13512610238430371717376259)
                ·
                  refine ⟨20268915357645557576064389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13512610238430371717376259 20268915357645557576064389)
                  ·
                    refine ⟨3800421629558542045512073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20268915357645557576064389 3800421629558542045512073)
                    ·
                      refine ⟨2850316222168906534134055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800421629558542045512073 2850316222168906534134055)
                      ·
                        rfl

theorem cell23_5550971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4, 2].length) (baseStart_5550971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550971 prefixEnd_5550971 := by exact prefixLift 5550971
  have htrace : WordTrace (prefixWord ++ tailWord_5550971) baseStart_5550971 baseEnd_5550971 := by
    simpa [prefixWord, tailWord_5550971, baseEnd_5550971] using wordTrace_append hprefix tailTrace_5550971
  have hstable : (prefixWord ++ tailWord_5550971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550971).length < 2 ^ (prefixWord ++ tailWord_5550971).sum := by decide
  have hdescent : baseEnd_5550971 < baseStart_5550971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5550988 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 4, 2, 2]
def baseStart_5550988 : Nat := 118140960795 + 5550988 * 2 ^ 59
def prefixEnd_5550988 : Nat := 4983230072969 + 3 ^ 40 * 5550988 * 2
def baseEnd_5550988 : Nat := 2850324951340032967621477

theorem tailTrace_5550988 : CollatzResearch.WordTrace tailWord_5550988 prefixEnd_5550988 2850324951340032967621477 := by
  unfold tailWord_5550988
  simp only [CollatzResearch.WordTrace]
  refine ⟨101230582606862992059362809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134974110142483989412483745 101230582606862992059362809)
  ·
    refine ⟨75922936955147244044522107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101230582606862992059362809 75922936955147244044522107)
    ·
      refine ⟨113884405432720866066783161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75922936955147244044522107 113884405432720866066783161)
      ·
        refine ⟨85413304074540649550087371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113884405432720866066783161 85413304074540649550087371)
        ·
          refine ⟨128119956111810974325131057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85413304074540649550087371 128119956111810974325131057)
          ·
            refine ⟨96089967083858230743848293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128119956111810974325131057 96089967083858230743848293)
            ·
              refine ⟨18016868828223418264471555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96089967083858230743848293 18016868828223418264471555)
              ·
                refine ⟨27025303242335127396707333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18016868828223418264471555 27025303242335127396707333)
                ·
                  refine ⟨5067244357937836386882625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27025303242335127396707333 5067244357937836386882625)
                  ·
                    refine ⟨3800433268453377290161969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067244357937836386882625 3800433268453377290161969)
                    ·
                      refine ⟨2850324951340032967621477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800433268453377290161969 2850324951340032967621477)
                      ·
                        rfl

theorem cell23_5550988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_5550988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5550988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5550988 prefixEnd_5550988 := by exact prefixLift 5550988
  have htrace : WordTrace (prefixWord ++ tailWord_5550988) baseStart_5550988 baseEnd_5550988 := by
    simpa [prefixWord, tailWord_5550988, baseEnd_5550988] using wordTrace_append hprefix tailTrace_5550988
  have hstable : (prefixWord ++ tailWord_5550988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5550988).length < 2 ^ (prefixWord ++ tailWord_5550988).sum := by decide
  have hdescent : baseEnd_5550988 < baseStart_5550988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5550988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551005 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_5551005 : Nat := 118140960795 + 5551005 * 2 ^ 59
def prefixEnd_5551005 : Nat := 4983230072969 + 3 ^ 40 * 5551005 * 2
def baseEnd_5551005 : Nat := 2850333680511159401108899

theorem tailTrace_5551005 : CollatzResearch.WordTrace tailWord_5551005 prefixEnd_5551005 2850333680511159401108899 := by
  unfold tailWord_5551005
  simp only [CollatzResearch.WordTrace]
  refine ⟨202461785254664396022094469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134974523503109597348062979 202461785254664396022094469)
  ·
    refine ⟨37961584735249574254142713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202461785254664396022094469 37961584735249574254142713)
    ·
      refine ⟨28471188551437180690607035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37961584735249574254142713 28471188551437180690607035)
      ·
        refine ⟨42706782827155771035910553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28471188551437180690607035 42706782827155771035910553)
        ·
          refine ⟨32030087120366828276932915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42706782827155771035910553 32030087120366828276932915)
          ·
            refine ⟨48045130680550242415399373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32030087120366828276932915 48045130680550242415399373)
            ·
              refine ⟨18016924005206340905774765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48045130680550242415399373 18016924005206340905774765)
              ·
                refine ⟨6756346501952377839665537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18016924005206340905774765 6756346501952377839665537)
                ·
                  refine ⟨5067259876464283379749153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6756346501952377839665537 5067259876464283379749153)
                  ·
                    refine ⟨3800444907348212534811865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067259876464283379749153 3800444907348212534811865)
                    ·
                      refine ⟨2850333680511159401108899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800444907348212534811865 2850333680511159401108899)
                      ·
                        rfl

theorem cell23_5551005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_5551005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551005 prefixEnd_5551005 := by exact prefixLift 5551005
  have htrace : WordTrace (prefixWord ++ tailWord_5551005) baseStart_5551005 baseEnd_5551005 := by
    simpa [prefixWord, tailWord_5551005, baseEnd_5551005] using wordTrace_append hprefix tailTrace_5551005
  have hstable : (prefixWord ++ tailWord_5551005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551005).length < 2 ^ (prefixWord ++ tailWord_5551005).sum := by decide
  have hdescent : baseEnd_5551005 < baseStart_5551005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551034 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_5551034 : Nat := 118140960795 + 5551034 * 2 ^ 59
def prefixEnd_5551034 : Nat := 4983230072969 + 3 ^ 40 * 5551034 * 2
def baseEnd_5551034 : Nat := 2850348571450139787646265

theorem tailTrace_5551034 : CollatzResearch.WordTrace tailWord_5551034 prefixEnd_5551034 2850348571450139787646265 := by
  unfold tailWord_5551034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50615710742889833493725039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134975228647706222649933437 50615710742889833493725039)
  ·
    refine ⟨75923566114334750240587559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50615710742889833493725039 75923566114334750240587559)
    ·
      refine ⟨113885349171502125360881339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75923566114334750240587559 113885349171502125360881339)
      ·
        refine ⟨170828023757253188041322009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113885349171502125360881339 170828023757253188041322009)
        ·
          refine ⟨128121017817939891030991507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170828023757253188041322009 128121017817939891030991507)
          ·
            refine ⟨192181526726909836546487261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128121017817939891030991507 192181526726909836546487261)
            ·
              refine ⟨72068072522591188704932723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192181526726909836546487261 72068072522591188704932723)
              ·
                refine ⟨108102108783886783057399085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72068072522591188704932723 108102108783886783057399085)
                ·
                  refine ⟨40538290793957543646524657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108102108783886783057399085 40538290793957543646524657)
                  ·
                    refine ⟨30403718095468157734893493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40538290793957543646524657 30403718095468157734893493)
                    ·
                      refine ⟨2850348571450139787646265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30403718095468157734893493 2850348571450139787646265)
                      ·
                        rfl

theorem cell23_5551034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_5551034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551034 prefixEnd_5551034 := by exact prefixLift 5551034
  have htrace : WordTrace (prefixWord ++ tailWord_5551034) baseStart_5551034 baseEnd_5551034 := by
    simpa [prefixWord, tailWord_5551034, baseEnd_5551034] using wordTrace_append hprefix tailTrace_5551034
  have hstable : (prefixWord ++ tailWord_5551034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551034).length < 2 ^ (prefixWord ++ tailWord_5551034).sum := by decide
  have hdescent : baseEnd_5551034 < baseStart_5551034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551105 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 1, 4]
def baseStart_5551105 : Nat := 118140960795 + 5551105 * 2 ^ 59
def prefixEnd_5551105 : Nat := 4983230072969 + 3 ^ 40 * 5551105 * 2
def baseEnd_5551105 : Nat := 950128342858869669952813

theorem tailTrace_5551105 : CollatzResearch.WordTrace tailWord_5551105 prefixEnd_5551105 950128342858869669952813 := by
  unfold tailWord_5551105
  simp only [CollatzResearch.WordTrace]
  refine ⟨202465432554302113100734769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134976955036201408733823179 202465432554302113100734769)
  ·
    refine ⟨151849074415726584825551077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202465432554302113100734769 151849074415726584825551077)
    ·
      refine ⟨28471701452948734654790827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151849074415726584825551077 28471701452948734654790827)
      ·
        refine ⟨42707552179423101982186241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28471701452948734654790827 42707552179423101982186241)
        ·
          refine ⟨32030664134567326486639681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42707552179423101982186241 32030664134567326486639681)
          ·
            refine ⟨24022998100925494864979761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32030664134567326486639681 24022998100925494864979761)
            ·
              refine ⟨18017248575694121148734821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24022998100925494864979761 18017248575694121148734821)
              ·
                refine ⟨3378234107942647715387779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18017248575694121148734821 3378234107942647715387779)
                ·
                  refine ⟨5067351161913971573081669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378234107942647715387779 5067351161913971573081669)
                  ·
                    refine ⟨950128342858869669952813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067351161913971573081669 950128342858869669952813)
                    ·
                      rfl

theorem cell23_5551105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_5551105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551105 prefixEnd_5551105 := by exact prefixLift 5551105
  have htrace : WordTrace (prefixWord ++ tailWord_5551105) baseStart_5551105 baseEnd_5551105 := by
    simpa [prefixWord, tailWord_5551105, baseEnd_5551105] using wordTrace_append hprefix tailTrace_5551105
  have hstable : (prefixWord ++ tailWord_5551105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551105).length < 2 ^ (prefixWord ++ tailWord_5551105).sum := by decide
  have hdescent : baseEnd_5551105 < baseStart_5551105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551171 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5]
def baseStart_5551171 : Nat := 118140960795 + 5551171 * 2 ^ 59
def prefixEnd_5551171 : Nat := 4983230072969 + 3 ^ 40 * 5551171 * 2
def baseEnd_5551171 : Nat := 2850418918299805751633135

theorem tailTrace_5551171 : CollatzResearch.WordTrace tailWord_5551171 prefixEnd_5551171 2850418918299805751633135 := by
  unfold tailWord_5551171
  simp only [CollatzResearch.WordTrace]
  refine ⟨202467839772063006372637367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134978559848042004248424911 202467839772063006372637367)
  ·
    refine ⟨303701759658094509558956051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202467839772063006372637367 303701759658094509558956051)
    ·
      refine ⟨455552639487141764338434077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303701759658094509558956051 455552639487141764338434077)
      ·
        refine ⟨170832239807678161626912779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455552639487141764338434077 170832239807678161626912779)
        ·
          refine ⟨256248359711517242440369169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170832239807678161626912779 256248359711517242440369169)
          ·
            refine ⟨192186269783637931830276877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256248359711517242440369169 192186269783637931830276877)
            ·
              refine ⟨72069851168864224436353829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192186269783637931830276877 72069851168864224436353829)
              ·
                refine ⟨13513097094162042081816343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72069851168864224436353829 13513097094162042081816343)
                ·
                  refine ⟨20269645641243063122724515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13513097094162042081816343 20269645641243063122724515)
                  ·
                    refine ⟨30404468461864594684086773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20269645641243063122724515 30404468461864594684086773)
                    ·
                      refine ⟨2850418918299805751633135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30404468461864594684086773 2850418918299805751633135)
                      ·
                        rfl

theorem cell23_5551171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_5551171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551171 prefixEnd_5551171 := by exact prefixLift 5551171
  have htrace : WordTrace (prefixWord ++ tailWord_5551171) baseStart_5551171 baseEnd_5551171 := by
    simpa [prefixWord, tailWord_5551171, baseEnd_5551171] using wordTrace_append hprefix tailTrace_5551171
  have hstable : (prefixWord ++ tailWord_5551171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551171).length < 2 ^ (prefixWord ++ tailWord_5551171).sum := by decide
  have hdescent : baseEnd_5551171 < baseStart_5551171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551185 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 3, 2, 2]
def baseStart_5551185 : Nat := 118140960795 + 5551185 * 2 ^ 59
def prefixEnd_5551185 : Nat := 4983230072969 + 3 ^ 40 * 5551185 * 2
def baseEnd_5551185 : Nat := 2850426107028968696858071

theorem tailTrace_5551185 : CollatzResearch.WordTrace tailWord_5551185 prefixEnd_5551185 2850426107028968696858071 := by
  unfold tailWord_5551185
  simp only [CollatzResearch.WordTrace]
  refine ⟨202468350394012286763647009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134978900262674857842431339 202468350394012286763647009)
  ·
    refine ⟨151851262795509215072735257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202468350394012286763647009 151851262795509215072735257)
    ·
      refine ⟨113888447096631911304551443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151851262795509215072735257 113888447096631911304551443)
      ·
        refine ⟨170832670644947866956827165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113888447096631911304551443 170832670644947866956827165)
        ·
          refine ⟨64062251491855450108810187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170832670644947866956827165 64062251491855450108810187)
          ·
            refine ⟨96093377237783175163215281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64062251491855450108810187 96093377237783175163215281)
            ·
              refine ⟨72070032928337381372411461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96093377237783175163215281 72070032928337381372411461)
              ·
                refine ⟨13513131174063259007327149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72070032928337381372411461 13513131174063259007327149)
                ·
                  refine ⟨5067424190273722127747681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13513131174063259007327149 5067424190273722127747681)
                  ·
                    refine ⟨3800568142705291595810761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067424190273722127747681 3800568142705291595810761)
                    ·
                      refine ⟨2850426107028968696858071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800568142705291595810761 2850426107028968696858071)
                      ·
                        rfl

theorem cell23_5551185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_5551185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551185 prefixEnd_5551185 := by exact prefixLift 5551185
  have htrace : WordTrace (prefixWord ++ tailWord_5551185) baseStart_5551185 baseEnd_5551185 := by
    simpa [prefixWord, tailWord_5551185, baseEnd_5551185] using wordTrace_append hprefix tailTrace_5551185
  have hstable : (prefixWord ++ tailWord_5551185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551185).length < 2 ^ (prefixWord ++ tailWord_5551185).sum := by decide
  have hdescent : baseEnd_5551185 < baseStart_5551185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551208 : List Nat := [2, 1, 4, 4, 1, 11]
def baseStart_5551208 : Nat := 118140960795 + 5551208 * 2 ^ 59
def prefixEnd_5551208 : Nat := 4983230072969 + 3 ^ 40 * 5551208 * 2
def baseEnd_5551208 : Nat := 11730197189646181509755

theorem tailTrace_5551208 : CollatzResearch.WordTrace tailWord_5551208 prefixEnd_5551208 11730197189646181509755 := by
  unfold tailWord_5551208
  simp only [CollatzResearch.WordTrace]
  refine ⟨101234594636464480845867139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134979459515285974461156185 101234594636464480845867139)
  ·
    refine ⟨151851891954696721268800709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101234594636464480845867139 151851891954696721268800709)
    ·
      refine ⟨28472229741505635237900133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151851891954696721268800709 28472229741505635237900133)
      ·
        refine ⟨5338543076532306607106275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28472229741505635237900133 5338543076532306607106275)
        ·
          refine ⟨8007814614798459910659413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5338543076532306607106275 8007814614798459910659413)
          ·
            refine ⟨11730197189646181509755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8007814614798459910659413 11730197189646181509755)
            ·
              rfl

theorem cell23_5551208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 11].length) (baseStart_5551208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551208 prefixEnd_5551208 := by exact prefixLift 5551208
  have htrace : WordTrace (prefixWord ++ tailWord_5551208) baseStart_5551208 baseEnd_5551208 := by
    simpa [prefixWord, tailWord_5551208, baseEnd_5551208] using wordTrace_append hprefix tailTrace_5551208
  have hstable : (prefixWord ++ tailWord_5551208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551208).length < 2 ^ (prefixWord ++ tailWord_5551208).sum := by decide
  have hdescent : baseEnd_5551208 < baseStart_5551208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551218 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_5551218 : Nat := 118140960795 + 5551218 * 2 ^ 59
def prefixEnd_5551218 : Nat := 4983230072969 + 3 ^ 40 * 5551218 * 2
def baseEnd_5551218 : Nat := 2850443051890567067745419

theorem tailTrace_5551218 : CollatzResearch.WordTrace tailWord_5551218 prefixEnd_5551218 2850443051890567067745419 := by
  unfold tailWord_5551218
  simp only [CollatzResearch.WordTrace]
  refine ⟨50617388500723183349899577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134979702668595155599732205 50617388500723183349899577)
  ·
    refine ⟨37963041375542387512424683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50617388500723183349899577 37963041375542387512424683)
    ·
      refine ⟨56944562063313581268637025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37963041375542387512424683 56944562063313581268637025)
      ·
        refine ⟨42708421547485185951477769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56944562063313581268637025 42708421547485185951477769)
        ·
          refine ⟨32031316160613889463608327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42708421547485185951477769 32031316160613889463608327)
          ·
            refine ⟨48046974240920834195412491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32031316160613889463608327 48046974240920834195412491)
            ·
              refine ⟨72070461361381251293118737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48046974240920834195412491 72070461361381251293118737)
              ·
                refine ⟨54052846021035938469839053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72070461361381251293118737 54052846021035938469839053)
                ·
                  refine ⟨20269817257888476926189645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54052846021035938469839053 20269817257888476926189645)
                  ·
                    refine ⟨7601181471708178847321117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20269817257888476926189645 7601181471708178847321117)
                    ·
                      refine ⟨2850443051890567067745419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7601181471708178847321117 2850443051890567067745419)
                      ·
                        rfl

theorem cell23_5551218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_5551218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551218 prefixEnd_5551218 := by exact prefixLift 5551218
  have htrace : WordTrace (prefixWord ++ tailWord_5551218) baseStart_5551218 baseEnd_5551218 := by
    simpa [prefixWord, tailWord_5551218, baseEnd_5551218] using wordTrace_append hprefix tailTrace_5551218
  have hstable : (prefixWord ++ tailWord_5551218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551218).length < 2 ^ (prefixWord ++ tailWord_5551218).sum := by decide
  have hdescent : baseEnd_5551218 < baseStart_5551218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551225 : List Nat := [1, 2, 1, 3, 6, 1, 1, 8]
def baseStart_5551225 : Nat := 118140960795 + 5551225 * 2 ^ 59
def prefixEnd_5551225 : Nat := 4983230072969 + 3 ^ 40 * 5551225 * 2
def baseEnd_5551225 : Nat := 105572098009449945939181

theorem tailTrace_5551225 : CollatzResearch.WordTrace tailWord_5551225 prefixEnd_5551225 105572098009449945939181 := by
  unfold tailWord_5551225
  simp only [CollatzResearch.WordTrace]
  refine ⟨202469809313867373595103129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134979872875911582396735419 202469809313867373595103129)
  ·
    refine ⟨151852356985400530196327347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202469809313867373595103129 151852356985400530196327347)
    ·
      refine ⟨227778535478100795294491021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151852356985400530196327347 227778535478100795294491021)
      ·
        refine ⟨85416950804287798235434133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227778535478100795294491021 85416950804287798235434133)
        ·
          refine ⟨4003919568950990542285975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85416950804287798235434133 4003919568950990542285975)
          ·
            refine ⟨6005879353426485813428963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003919568950990542285975 6005879353426485813428963)
            ·
              refine ⟨9008819030139728720143445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005879353426485813428963 9008819030139728720143445)
              ·
                refine ⟨105572098009449945939181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9008819030139728720143445 105572098009449945939181)
                ·
                  rfl

theorem cell23_5551225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 8].length) (baseStart_5551225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551225 prefixEnd_5551225 := by exact prefixLift 5551225
  have htrace : WordTrace (prefixWord ++ tailWord_5551225) baseStart_5551225 baseEnd_5551225 := by
    simpa [prefixWord, tailWord_5551225, baseEnd_5551225] using wordTrace_append hprefix tailTrace_5551225
  have hstable : (prefixWord ++ tailWord_5551225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551225).length < 2 ^ (prefixWord ++ tailWord_5551225).sum := by decide
  have hdescent : baseEnd_5551225 < baseStart_5551225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551235 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 3]
def baseStart_5551235 : Nat := 118140960795 + 5551235 * 2 ^ 59
def prefixEnd_5551235 : Nat := 4983230072969 + 3 ^ 40 * 5551235 * 2
def baseEnd_5551235 : Nat := 2850451781061693501232841

theorem tailTrace_5551235 : CollatzResearch.WordTrace tailWord_5551235 prefixEnd_5551235 2850451781061693501232841 := by
  unfold tailWord_5551235
  simp only [CollatzResearch.WordTrace]
  refine ⟨202470174043831145302967159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134980116029220763535311439 202470174043831145302967159)
  ·
    refine ⟨303705261065746717954450739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202470174043831145302967159 303705261065746717954450739)
    ·
      refine ⟨455557891598620076931676109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303705261065746717954450739 455557891598620076931676109)
      ·
        refine ⟨170834209349482528849378541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455557891598620076931676109 170834209349482528849378541)
        ·
          refine ⟨64062828506055948318516953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170834209349482528849378541 64062828506055948318516953)
          ·
            refine ⟨48047121379541961238887715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64062828506055948318516953 48047121379541961238887715)
            ·
              refine ⟨72070682069312941858331573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48047121379541961238887715 72070682069312941858331573)
              ·
                refine ⟨6756626443998088299218585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72070682069312941858331573 6756626443998088299218585)
                ·
                  refine ⟨5067469832998566224413939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6756626443998088299218585 5067469832998566224413939)
                  ·
                    refine ⟨7601204749497849336620909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5067469832998566224413939 7601204749497849336620909)
                    ·
                      refine ⟨2850451781061693501232841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7601204749497849336620909 2850451781061693501232841)
                      ·
                        rfl

theorem cell23_5551235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_5551235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551235 prefixEnd_5551235 := by exact prefixLift 5551235
  have htrace : WordTrace (prefixWord ++ tailWord_5551235) baseStart_5551235 baseEnd_5551235 := by
    simpa [prefixWord, tailWord_5551235, baseEnd_5551235] using wordTrace_append hprefix tailTrace_5551235
  have hstable : (prefixWord ++ tailWord_5551235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551235).length < 2 ^ (prefixWord ++ tailWord_5551235).sum := by decide
  have hdescent : baseEnd_5551235 < baseStart_5551235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551268 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_5551268 : Nat := 118140960795 + 5551268 * 2 ^ 59
def prefixEnd_5551268 : Nat := 4983230072969 + 3 ^ 40 * 5551268 * 2
def baseEnd_5551268 : Nat := 950156241974430624040063

theorem tailTrace_5551268 : CollatzResearch.WordTrace tailWord_5551268 prefixEnd_5551268 950156241974430624040063 := by
  unfold tailWord_5551268
  simp only [CollatzResearch.WordTrace]
  refine ⟨101235688826355795969459229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134980918435141061292612305 101235688826355795969459229)
  ·
    refine ⟨37963383309883423488547211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101235688826355795969459229 37963383309883423488547211)
    ·
      refine ⟨56945074964825135232820817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37963383309883423488547211 56945074964825135232820817)
      ·
        refine ⟨42708806223618851424615613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56945074964825135232820817 42708806223618851424615613)
        ·
          refine ⟨16015802333857069284230855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42708806223618851424615613 16015802333857069284230855)
          ·
            refine ⟨24023703500785603926346283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16015802333857069284230855 24023703500785603926346283)
            ·
              refine ⟨36035555251178405889519425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24023703500785603926346283 36035555251178405889519425)
              ·
                refine ⟨27026666438383804417139569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36035555251178405889519425 27026666438383804417139569)
                ·
                  refine ⟨20269999828787853312854677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27026666438383804417139569 20269999828787853312854677)
                  ·
                    refine ⟨950156241974430624040063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20269999828787853312854677 950156241974430624040063)
                    ·
                      rfl

theorem cell23_5551268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_5551268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551268 prefixEnd_5551268 := by exact prefixLift 5551268
  have htrace : WordTrace (prefixWord ++ tailWord_5551268) baseStart_5551268 baseEnd_5551268 := by
    simpa [prefixWord, tailWord_5551268, baseEnd_5551268] using wordTrace_append hprefix tailTrace_5551268
  have hstable : (prefixWord ++ tailWord_5551268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551268).length < 2 ^ (prefixWord ++ tailWord_5551268).sum := by decide
  have hdescent : baseEnd_5551268 < baseStart_5551268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551286 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5551286 : Nat := 118140960795 + 5551286 * 2 ^ 59
def prefixEnd_5551286 : Nat := 4983230072969 + 3 ^ 40 * 5551286 * 2
def baseEnd_5551286 : Nat := 2850477968575072801695107

theorem tailTrace_5551286 : CollatzResearch.WordTrace tailWord_5551286 prefixEnd_5551286 2850477968575072801695107 := by
  unfold tailWord_5551286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654502135415398813317107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134981356111097587342049141 12654502135415398813317107)
  ·
    refine ⟨18981753203123098219975661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12654502135415398813317107 18981753203123098219975661)
    ·
      refine ⟨7118157451171161832490873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18981753203123098219975661 7118157451171161832490873)
      ·
        refine ⟨5338618088378371374368155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7118157451171161832490873 5338618088378371374368155)
        ·
          refine ⟨8007927132567557061552233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5338618088378371374368155 8007927132567557061552233)
          ·
            refine ⟨6005945349425667796164175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8007927132567557061552233 6005945349425667796164175)
            ·
              refine ⟨9008918024138501694246263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005945349425667796164175 9008918024138501694246263)
              ·
                refine ⟨13513377036207752541369395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9008918024138501694246263 13513377036207752541369395)
                ·
                  refine ⟨20270065554311628812054093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13513377036207752541369395 20270065554311628812054093)
                  ·
                    refine ⟨7601274582866860804520285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20270065554311628812054093 7601274582866860804520285)
                    ·
                      refine ⟨2850477968575072801695107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7601274582866860804520285 2850477968575072801695107)
                      ·
                        rfl

theorem cell23_5551286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5551286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551286 prefixEnd_5551286 := by exact prefixLift 5551286
  have htrace : WordTrace (prefixWord ++ tailWord_5551286) baseStart_5551286 baseEnd_5551286 := by
    simpa [prefixWord, tailWord_5551286, baseEnd_5551286] using wordTrace_append hprefix tailTrace_5551286
  have hstable : (prefixWord ++ tailWord_5551286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551286).length < 2 ^ (prefixWord ++ tailWord_5551286).sum := by decide
  have hdescent : baseEnd_5551286 < baseStart_5551286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551292 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_5551292 : Nat := 118140960795 + 5551292 * 2 ^ 59
def prefixEnd_5551292 : Nat := 4983230072969 + 3 ^ 40 * 5551292 * 2
def baseEnd_5551292 : Nat := 2850481049458999778220079

theorem tailTrace_5551292 : CollatzResearch.WordTrace tailWord_5551292 prefixEnd_5551292 2850481049458999778220079 := by
  unfold tailWord_5551292
  simp only [CollatzResearch.WordTrace]
  refine ⟨101236126502312322018896065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134981502003083096025194753 101236126502312322018896065)
  ·
    refine ⟨75927094876734241514172049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101236126502312322018896065 75927094876734241514172049)
    ·
      refine ⟨56945321157550681135629037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75927094876734241514172049 56945321157550681135629037)
      ·
        refine ⟨21354495434081505425860889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56945321157550681135629037 21354495434081505425860889)
        ·
          refine ⟨16015871575561129069395667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21354495434081505425860889 16015871575561129069395667)
          ·
            refine ⟨24023807363341693604093501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16015871575561129069395667 24023807363341693604093501)
            ·
              refine ⟨9008927761253135101535063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24023807363341693604093501 9008927761253135101535063)
              ·
                refine ⟨13513391641879702652302595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9008927761253135101535063 13513391641879702652302595)
                ·
                  refine ⟨20270087462819553978453893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13513391641879702652302595 20270087462819553978453893)
                  ·
                    refine ⟨3800641399278666370960105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20270087462819553978453893 3800641399278666370960105)
                    ·
                      refine ⟨2850481049458999778220079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800641399278666370960105 2850481049458999778220079)
                      ·
                        rfl

theorem cell23_5551292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_5551292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551292 prefixEnd_5551292 := by exact prefixLift 5551292
  have htrace : WordTrace (prefixWord ++ tailWord_5551292) baseStart_5551292 baseEnd_5551292 := by
    simpa [prefixWord, tailWord_5551292, baseEnd_5551292] using wordTrace_append hprefix tailTrace_5551292
  have hstable : (prefixWord ++ tailWord_5551292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551292).length < 2 ^ (prefixWord ++ tailWord_5551292).sum := by decide
  have hdescent : baseEnd_5551292 < baseStart_5551292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551328 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_5551328 : Nat := 118140960795 + 5551328 * 2 ^ 59
def prefixEnd_5551328 : Nat := 4983230072969 + 3 ^ 40 * 5551328 * 2
def baseEnd_5551328 : Nat := 950166511587520545789971

theorem tailTrace_5551328 : CollatzResearch.WordTrace tailWord_5551328 prefixEnd_5551328 950166511587520545789971 := by
  unfold tailWord_5551328
  simp only [CollatzResearch.WordTrace]
  refine ⟨101236783016247111093051319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134982377354996148124068425 101236783016247111093051319)
  ·
    refine ⟨151855174524370666639576979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101236783016247111093051319 151855174524370666639576979)
    ·
      refine ⟨227782761786555999959365469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151855174524370666639576979 227782761786555999959365469)
      ·
        refine ⟨85418535669958499984762051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227782761786555999959365469 85418535669958499984762051)
        ·
          refine ⟨128127803504937749977143077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85418535669958499984762051 128127803504937749977143077)
          ·
            refine ⟨24023963157175828120714327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128127803504937749977143077 24023963157175828120714327)
            ·
              refine ⟨36035944735763742181071491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24023963157175828120714327 36035944735763742181071491)
              ·
                refine ⟨54053917103645613271607237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36035944735763742181071491 54053917103645613271607237)
                ·
                  refine ⟨10135109456933552488426357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54053917103645613271607237 10135109456933552488426357)
                  ·
                    refine ⟨950166511587520545789971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10135109456933552488426357 950166511587520545789971)
                    ·
                      rfl

theorem cell23_5551328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_5551328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551328 prefixEnd_5551328 := by exact prefixLift 5551328
  have htrace : WordTrace (prefixWord ++ tailWord_5551328) baseStart_5551328 baseEnd_5551328 := by
    simpa [prefixWord, tailWord_5551328, baseEnd_5551328] using wordTrace_append hprefix tailTrace_5551328
  have hstable : (prefixWord ++ tailWord_5551328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551328).length < 2 ^ (prefixWord ++ tailWord_5551328).sum := by decide
  have hdescent : baseEnd_5551328 < baseStart_5551328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551338 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_5551338 : Nat := 118140960795 + 5551338 * 2 ^ 59
def prefixEnd_5551338 : Nat := 4983230072969 + 3 ^ 40 * 5551338 * 2
def baseEnd_5551338 : Nat := 2850504669569106598244867

theorem tailTrace_5551338 : CollatzResearch.WordTrace tailWord_5551338 prefixEnd_5551338 2850504669569106598244867 := by
  unfold tailWord_5551338
  simp only [CollatzResearch.WordTrace]
  refine ⟨50618482690614498473491667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134982620508305329262644445 50618482690614498473491667)
  ·
    refine ⟨75927724035921747710237501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50618482690614498473491667 75927724035921747710237501)
    ·
      refine ⟨28472896513470655391339063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75927724035921747710237501 28472896513470655391339063)
      ·
        refine ⟨42709344770205983087008595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28472896513470655391339063 42709344770205983087008595)
        ·
          refine ⟨64064017155308974630512893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42709344770205983087008595 64064017155308974630512893)
          ·
            refine ⟨24024006433240865486442335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64064017155308974630512893 24024006433240865486442335)
            ·
              refine ⟨36036009649861298229663503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24024006433240865486442335 36036009649861298229663503)
              ·
                refine ⟨54054014474791947344495255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36036009649861298229663503 54054014474791947344495255)
                ·
                  refine ⟨81081021712187921016742883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54054014474791947344495255 81081021712187921016742883)
                  ·
                    refine ⟨121621532568281881525114325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81081021712187921016742883 121621532568281881525114325)
                    ·
                      refine ⟨2850504669569106598244867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121621532568281881525114325 2850504669569106598244867)
                      ·
                        rfl

theorem cell23_5551338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_5551338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551338 prefixEnd_5551338 := by exact prefixLift 5551338
  have htrace : WordTrace (prefixWord ++ tailWord_5551338) baseStart_5551338 baseEnd_5551338 := by
    simpa [prefixWord, tailWord_5551338, baseEnd_5551338] using wordTrace_append hprefix tailTrace_5551338
  have hstable : (prefixWord ++ tailWord_5551338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551338).length < 2 ^ (prefixWord ++ tailWord_5551338).sum := by decide
  have hdescent : baseEnd_5551338 < baseStart_5551338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551343 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 2, 2, 2]
def baseStart_5551343 : Nat := 118140960795 + 5551343 * 2 ^ 59
def prefixEnd_5551343 : Nat := 4983230072969 + 3 ^ 40 * 5551343 * 2
def baseEnd_5551343 : Nat := 2850507236972379078682345

theorem tailTrace_5551343 : CollatzResearch.WordTrace tailWord_5551343 prefixEnd_5551343 2850507236972379078682345 := by
  unfold tailWord_5551343
  simp only [CollatzResearch.WordTrace]
  refine ⟨202474113127439879747898683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134982742084959919831932455 202474113127439879747898683)
  ·
    refine ⟨303711169691159819621848025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202474113127439879747898683 303711169691159819621848025)
    ·
      refine ⟨227783377268369864716386019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303711169691159819621848025 227783377268369864716386019)
      ·
        refine ⟨341675065902554797074579029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227783377268369864716386019 341675065902554797074579029)
        ·
          refine ⟨4004004678545564028217723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 341675065902554797074579029 4004004678545564028217723)
          ·
            refine ⟨6006007017818346042326585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004004678545564028217723 6006007017818346042326585)
            ·
              refine ⟨4504505263363759531744939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6006007017818346042326585 4504505263363759531744939)
              ·
                refine ⟨6756757895045639297617409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504505263363759531744939 6756757895045639297617409)
                ·
                  refine ⟨5067568421284229473213057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6756757895045639297617409 5067568421284229473213057)
                  ·
                    refine ⟨3800676315963172104909793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067568421284229473213057 3800676315963172104909793)
                    ·
                      refine ⟨2850507236972379078682345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800676315963172104909793 2850507236972379078682345)
                      ·
                        rfl

theorem cell23_5551343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 2, 2].length) (baseStart_5551343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551343 prefixEnd_5551343 := by exact prefixLift 5551343
  have htrace : WordTrace (prefixWord ++ tailWord_5551343) baseStart_5551343 baseEnd_5551343 := by
    simpa [prefixWord, tailWord_5551343, baseEnd_5551343] using wordTrace_append hprefix tailTrace_5551343
  have hstable : (prefixWord ++ tailWord_5551343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551343).length < 2 ^ (prefixWord ++ tailWord_5551343).sum := by decide
  have hdescent : baseEnd_5551343 < baseStart_5551343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551365 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_5551365 : Nat := 118140960795 + 5551365 * 2 ^ 59
def prefixEnd_5551365 : Nat := 4983230072969 + 3 ^ 40 * 5551365 * 2
def baseEnd_5551365 : Nat := 2850518533546777992607243

theorem tailTrace_5551365 : CollatzResearch.WordTrace tailWord_5551365 prefixEnd_5551365 2850518533546777992607243 := by
  unfold tailWord_5551365
  simp only [CollatzResearch.WordTrace]
  refine ⟨202474915533360177505199549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134983277022240118336799699 202474915533360177505199549)
  ·
    refine ⟨75928093325010066564449831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202474915533360177505199549 75928093325010066564449831)
    ·
      refine ⟨113892139987515099846674747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75928093325010066564449831 113892139987515099846674747)
      ·
        refine ⟨170838209981272649770012121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113892139987515099846674747 170838209981272649770012121)
        ·
          refine ⟨128128657485954487327509091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170838209981272649770012121 128128657485954487327509091)
          ·
            refine ⟨192192986228931730991263637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128128657485954487327509091 192192986228931730991263637)
            ·
              refine ⟨9009046229481174890215483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192192986228931730991263637 9009046229481174890215483)
              ·
                refine ⟨13513569344221762335323225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009046229481174890215483 13513569344221762335323225)
                ·
                  refine ⟨10135177008166321751492419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13513569344221762335323225 10135177008166321751492419)
                  ·
                    refine ⟨15202765512249482627238629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10135177008166321751492419 15202765512249482627238629)
                    ·
                      refine ⟨2850518533546777992607243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15202765512249482627238629 2850518533546777992607243)
                      ·
                        rfl

theorem cell23_5551365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_5551365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551365 prefixEnd_5551365 := by exact prefixLift 5551365
  have htrace : WordTrace (prefixWord ++ tailWord_5551365) baseStart_5551365 baseEnd_5551365 := by
    simpa [prefixWord, tailWord_5551365, baseEnd_5551365] using wordTrace_append hprefix tailTrace_5551365
  have hstable : (prefixWord ++ tailWord_5551365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551365).length < 2 ^ (prefixWord ++ tailWord_5551365).sum := by decide
  have hdescent : baseEnd_5551365 < baseStart_5551365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551388 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 8]
def baseStart_5551388 : Nat := 118140960795 + 5551388 * 2 ^ 59
def prefixEnd_5551388 : Nat := 4983230072969 + 3 ^ 40 * 5551388 * 2
def baseEnd_5551388 : Nat := 316725593733536822513293

theorem tailTrace_5551388 : CollatzResearch.WordTrace tailWord_5551388 prefixEnd_5551388 316725593733536822513293 := by
  unfold tailWord_5551388
  simp only [CollatzResearch.WordTrace]
  refine ⟨101237877206138426216643409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134983836274851234955524545 101237877206138426216643409)
  ·
    refine ⟨75928407904603819662482557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101237877206138426216643409 75928407904603819662482557)
    ·
      refine ⟨28473152964226432373430959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75928407904603819662482557 28473152964226432373430959)
      ·
        refine ⟨42709729446339648560146439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28473152964226432373430959 42709729446339648560146439)
        ·
          refine ⟨64064594169509472840219659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42709729446339648560146439 64064594169509472840219659)
          ·
            refine ⟨96096891254264209260329489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64064594169509472840219659 96096891254264209260329489)
            ·
              refine ⟨72072668440698156945247117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96096891254264209260329489 72072668440698156945247117)
              ·
                refine ⟨27027250665261808854467669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72072668440698156945247117 27027250665261808854467669)
                ·
                  refine ⟨316725593733536822513293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27027250665261808854467669 316725593733536822513293)
                  ·
                    rfl

theorem cell23_5551388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_5551388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551388 prefixEnd_5551388 := by exact prefixLift 5551388
  have htrace : WordTrace (prefixWord ++ tailWord_5551388) baseStart_5551388 baseEnd_5551388 := by
    simpa [prefixWord, tailWord_5551388, baseEnd_5551388] using wordTrace_append hprefix tailTrace_5551388
  have hstable : (prefixWord ++ tailWord_5551388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551388).length < 2 ^ (prefixWord ++ tailWord_5551388).sum := by decide
  have hdescent : baseEnd_5551388 < baseStart_5551388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551442 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_5551442 : Nat := 118140960795 + 5551442 * 2 ^ 59
def prefixEnd_5551442 : Nat := 4983230072969 + 3 ^ 40 * 5551442 * 2
def baseEnd_5551442 : Nat := 2850558071557174191344389

theorem tailTrace_5551442 : CollatzResearch.WordTrace tailWord_5551442 prefixEnd_5551442 2850558071557174191344389 := by
  unfold tailWord_5551442
  simp only [CollatzResearch.WordTrace]
  refine ⟨50619430988520304913938145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134985149302720813103835053 50619430988520304913938145)
  ·
    refine ⟨37964573241390228685453609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50619430988520304913938145 37964573241390228685453609)
    ·
      refine ⟨28473429931042671514090207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37964573241390228685453609 28473429931042671514090207)
      ·
        refine ⟨42710144896564007271135311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28473429931042671514090207 42710144896564007271135311)
        ·
          refine ⟨64065217344846010906702967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42710144896564007271135311 64065217344846010906702967)
          ·
            refine ⟨96097826017269016360054451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64065217344846010906702967 96097826017269016360054451)
            ·
              refine ⟨144146739025903524540081677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96097826017269016360054451 144146739025903524540081677)
              ·
                refine ⟨54055027134713821702530629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144146739025903524540081677 54055027134713821702530629)
                ·
                  refine ⟨10135317587758841569224493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54055027134713821702530629 10135317587758841569224493)
                  ·
                    refine ⟨3800744095409565588459185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10135317587758841569224493 3800744095409565588459185)
                    ·
                      refine ⟨2850558071557174191344389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800744095409565588459185 2850558071557174191344389)
                      ·
                        rfl

theorem cell23_5551442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_5551442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551442 prefixEnd_5551442 := by exact prefixLift 5551442
  have htrace : WordTrace (prefixWord ++ tailWord_5551442) baseStart_5551442 baseEnd_5551442 := by
    simpa [prefixWord, tailWord_5551442, baseEnd_5551442] using wordTrace_append hprefix tailTrace_5551442
  have hstable : (prefixWord ++ tailWord_5551442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551442).length < 2 ^ (prefixWord ++ tailWord_5551442).sum := by decide
  have hdescent : baseEnd_5551442 < baseStart_5551442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551449 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 1, 1, 3]
def baseStart_5551449 : Nat := 118140960795 + 5551449 * 2 ^ 59
def prefixEnd_5551449 : Nat := 4983230072969 + 3 ^ 40 * 5551449 * 2
def baseEnd_5551449 : Nat := 2850561665921755663956857

theorem tailTrace_5551449 : CollatzResearch.WordTrace tailWord_5551449 prefixEnd_5551449 2850561665921755663956857 := by
  unfold tailWord_5551449
  simp only [CollatzResearch.WordTrace]
  refine ⟨202477979265055859851257401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134985319510037239900838267 202477979265055859851257401)
  ·
    refine ⟨151858484448791894888443051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202477979265055859851257401 151858484448791894888443051)
    ·
      refine ⟨227787726673187842332664577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151858484448791894888443051 227787726673187842332664577)
      ·
        refine ⟨170840795004890881749498433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227787726673187842332664577 170840795004890881749498433)
        ·
          refine ⟨128130596253668161312123825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170840795004890881749498433 128130596253668161312123825)
          ·
            refine ⟨96097947190251120984092869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128130596253668161312123825 96097947190251120984092869)
            ·
              refine ⟨18018365098172085184517413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96097947190251120984092869 18018365098172085184517413)
              ·
                refine ⟨3378443455907265972097015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18018365098172085184517413 3378443455907265972097015)
                ·
                  refine ⟨5067665183860898958145523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378443455907265972097015 5067665183860898958145523)
                  ·
                    refine ⟨7601497775791348437218285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5067665183860898958145523 7601497775791348437218285)
                    ·
                      refine ⟨2850561665921755663956857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7601497775791348437218285 2850561665921755663956857)
                      ·
                        rfl

theorem cell23_5551449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_5551449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551449 prefixEnd_5551449 := by exact prefixLift 5551449
  have htrace : WordTrace (prefixWord ++ tailWord_5551449) baseStart_5551449 baseEnd_5551449 := by
    simpa [prefixWord, tailWord_5551449, baseEnd_5551449] using wordTrace_append hprefix tailTrace_5551449
  have hstable : (prefixWord ++ tailWord_5551449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551449).length < 2 ^ (prefixWord ++ tailWord_5551449).sum := by decide
  have hdescent : baseEnd_5551449 < baseStart_5551449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551472 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4]
def baseStart_5551472 : Nat := 118140960795 + 5551472 * 2 ^ 59
def prefixEnd_5551472 : Nat := 4983230072969 + 3 ^ 40 * 5551472 * 2
def baseEnd_5551472 : Nat := 2850573475976809073969251

theorem tailTrace_5551472 : CollatzResearch.WordTrace tailWord_5551472 prefixEnd_5551472 2850573475976809073969251 := by
  unfold tailWord_5551472
  simp only [CollatzResearch.WordTrace]
  refine ⟨101239409071986267389672335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134985878762648356519563113 101239409071986267389672335)
  ·
    refine ⟨151859113607979401084508503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101239409071986267389672335 151859113607979401084508503)
    ·
      refine ⟨227788670411969101626762755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151859113607979401084508503 227788670411969101626762755)
      ·
        refine ⟨341683005617953652440144133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227788670411969101626762755 341683005617953652440144133)
        ·
          refine ⟨64065563553366309832527025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 341683005617953652440144133 64065563553366309832527025)
          ·
            refine ⟨48049172665024732374395269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64065563553366309832527025 48049172665024732374395269)
            ·
              refine ⟨9009219874692137320199113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48049172665024732374395269 9009219874692137320199113)
              ·
                refine ⟨6756914906019102990149335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9009219874692137320199113 6756914906019102990149335)
                ·
                  refine ⟨10135372359028654485224003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6756914906019102990149335 10135372359028654485224003)
                  ·
                    refine ⟨15203058538542981727836005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10135372359028654485224003 15203058538542981727836005)
                    ·
                      refine ⟨2850573475976809073969251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15203058538542981727836005 2850573475976809073969251)
                      ·
                        rfl

theorem cell23_5551472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_5551472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551472 prefixEnd_5551472 := by exact prefixLift 5551472
  have htrace : WordTrace (prefixWord ++ tailWord_5551472) baseStart_5551472 baseEnd_5551472 := by
    simpa [prefixWord, tailWord_5551472, baseEnd_5551472] using wordTrace_append hprefix tailTrace_5551472
  have hstable : (prefixWord ++ tailWord_5551472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551472).length < 2 ^ (prefixWord ++ tailWord_5551472).sum := by decide
  have hdescent : baseEnd_5551472 < baseStart_5551472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551485 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_5551485 : Nat := 118140960795 + 5551485 * 2 ^ 59
def prefixEnd_5551485 : Nat := 4983230072969 + 3 ^ 40 * 5551485 * 2
def baseEnd_5551485 : Nat := 2850580151225317523106691

theorem tailTrace_5551485 : CollatzResearch.WordTrace tailWord_5551485 prefixEnd_5551485 2850580151225317523106691 := by
  unfold tailWord_5551485
  simp only [CollatzResearch.WordTrace]
  refine ⟨202479292292925437999567909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134986194861950291999711939 202479292292925437999567909)
  ·
    refine ⟨37964867304923519624918983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202479292292925437999567909 37964867304923519624918983)
    ·
      refine ⟨56947300957385279437378475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37964867304923519624918983 56947300957385279437378475)
      ·
        refine ⟨85420951436077919156067713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56947300957385279437378475 85420951436077919156067713)
        ·
          refine ⟨64065713577058439367050785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85420951436077919156067713 64065713577058439367050785)
          ·
            refine ⟨48049285182793829525288089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64065713577058439367050785 48049285182793829525288089)
            ·
              refine ⟨36036963887095372143966067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48049285182793829525288089 36036963887095372143966067)
              ·
                refine ⟨54055445830643058215949101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36036963887095372143966067 54055445830643058215949101)
                ·
                  refine ⟨20270792186491146830980913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54055445830643058215949101 20270792186491146830980913)
                  ·
                    refine ⟨15203094139868360123235685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20270792186491146830980913 15203094139868360123235685)
                    ·
                      refine ⟨2850580151225317523106691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15203094139868360123235685 2850580151225317523106691)
                      ·
                        rfl

theorem cell23_5551485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_5551485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551485 prefixEnd_5551485 := by exact prefixLift 5551485
  have htrace : WordTrace (prefixWord ++ tailWord_5551485) baseStart_5551485 baseEnd_5551485 := by
    simpa [prefixWord, tailWord_5551485, baseEnd_5551485] using wordTrace_append hprefix tailTrace_5551485
  have hstable : (prefixWord ++ tailWord_5551485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551485).length < 2 ^ (prefixWord ++ tailWord_5551485).sum := by decide
  have hdescent : baseEnd_5551485 < baseStart_5551485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551492 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_5551492 : Nat := 118140960795 + 5551492 * 2 ^ 59
def prefixEnd_5551492 : Nat := 4983230072969 + 3 ^ 40 * 5551492 * 2
def baseEnd_5551492 : Nat := 2850583745589898995719159

theorem tailTrace_5551492 : CollatzResearch.WordTrace tailWord_5551492 prefixEnd_5551492 2850583745589898995719159 := by
  unfold tailWord_5551492
  simp only [CollatzResearch.WordTrace]
  refine ⟨101239773801950039097536365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134986365069266718796715153 101239773801950039097536365)
  ·
    refine ⟨37964915175731264661576137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101239773801950039097536365 37964915175731264661576137)
    ·
      refine ⟨28473686381798448496182103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37964915175731264661576137 28473686381798448496182103)
      ·
        refine ⟨42710529572697672744273155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28473686381798448496182103 42710529572697672744273155)
        ·
          refine ⟨64065794359046509116409733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42710529572697672744273155 64065794359046509116409733)
          ·
            refine ⟨12012336442321220459326825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64065794359046509116409733 12012336442321220459326825)
            ·
              refine ⟨9009252331740915344495119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12012336442321220459326825 9009252331740915344495119)
              ·
                refine ⟨13513878497611373016742679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009252331740915344495119 13513878497611373016742679)
                ·
                  refine ⟨20270817746417059525114019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13513878497611373016742679 20270817746417059525114019)
                  ·
                    refine ⟨30406226619625589287671029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20270817746417059525114019 30406226619625589287671029)
                    ·
                      refine ⟨2850583745589898995719159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30406226619625589287671029 2850583745589898995719159)
                      ·
                        rfl

theorem cell23_5551492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_5551492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551492 prefixEnd_5551492 := by exact prefixLift 5551492
  have htrace : WordTrace (prefixWord ++ tailWord_5551492) baseStart_5551492 baseEnd_5551492 := by
    simpa [prefixWord, tailWord_5551492, baseEnd_5551492] using wordTrace_append hprefix tailTrace_5551492
  have hstable : (prefixWord ++ tailWord_5551492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551492).length < 2 ^ (prefixWord ++ tailWord_5551492).sum := by decide
  have hdescent : baseEnd_5551492 < baseStart_5551492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551495 : List Nat := [1, 1, 4, 2, 2, 4, 9]
def baseStart_5551495 : Nat := 118140960795 + 5551495 * 2 ^ 59
def prefixEnd_5551495 : Nat := 4983230072969 + 3 ^ 40 * 5551495 * 2
def baseEnd_5551495 : Nat := 35192410938664968938045

theorem tailTrace_5551495 : CollatzResearch.WordTrace tailWord_5551495 prefixEnd_5551495 35192410938664968938045 := by
  unfold tailWord_5551495
  simp only [CollatzResearch.WordTrace]
  refine ⟨202479657022889209707431939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134986438015259473138287959 202479657022889209707431939)
  ·
    refine ⟨303719485534333814561147909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202479657022889209707431939 303719485534333814561147909)
    ·
      refine ⟨56947403537687590230215233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303719485534333814561147909 56947403537687590230215233)
      ·
        refine ⟨42710552653265692672661425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56947403537687590230215233 42710552653265692672661425)
        ·
          refine ⟨32032914489949269504496069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42710552653265692672661425 32032914489949269504496069)
          ·
            refine ⟨6006171466865488032093013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32032914489949269504496069 6006171466865488032093013)
            ·
              refine ⟨35192410938664968938045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6006171466865488032093013 35192410938664968938045)
              ·
                rfl

theorem cell23_5551495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 9].length) (baseStart_5551495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551495 prefixEnd_5551495 := by exact prefixLift 5551495
  have htrace : WordTrace (prefixWord ++ tailWord_5551495) baseStart_5551495 baseEnd_5551495 := by
    simpa [prefixWord, tailWord_5551495, baseEnd_5551495] using wordTrace_append hprefix tailTrace_5551495
  have hstable : (prefixWord ++ tailWord_5551495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551495).length < 2 ^ (prefixWord ++ tailWord_5551495).sum := by decide
  have hdescent : baseEnd_5551495 < baseStart_5551495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551505 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_5551505 : Nat := 118140960795 + 5551505 * 2 ^ 59
def prefixEnd_5551505 : Nat := 4983230072969 + 3 ^ 40 * 5551505 * 2
def baseEnd_5551505 : Nat := 2850590420838407444856599

theorem tailTrace_5551505 : CollatzResearch.WordTrace tailWord_5551505 prefixEnd_5551505 2850590420838407444856599 := by
  unfold tailWord_5551505
  simp only [CollatzResearch.WordTrace]
  refine ⟨202480021752852981415295969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134986681168568654276863979 202480021752852981415295969)
  ·
    refine ⟨151860016314639736061471977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202480021752852981415295969 151860016314639736061471977)
    ·
      refine ⟨113895012235979802046103983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151860016314639736061471977 113895012235979802046103983)
      ·
        refine ⟨170842518353969703069155975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113895012235979802046103983 170842518353969703069155975)
        ·
          refine ⟨256263777530954554603733963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170842518353969703069155975 256263777530954554603733963)
          ·
            refine ⟨384395666296431831905600945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256263777530954554603733963 384395666296431831905600945)
            ·
              refine ⟨288296749722323873929200709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384395666296431831905600945 288296749722323873929200709)
              ·
                refine ⟨54055640572935726361725133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288296749722323873929200709 54055640572935726361725133)
                ·
                  refine ⟨20270865214850897385646925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54055640572935726361725133 20270865214850897385646925)
                  ·
                    refine ⟨7601574455569086519617597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20270865214850897385646925 7601574455569086519617597)
                    ·
                      refine ⟨2850590420838407444856599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7601574455569086519617597 2850590420838407444856599)
                      ·
                        rfl

theorem cell23_5551505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_5551505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551505 prefixEnd_5551505 := by exact prefixLift 5551505
  have htrace : WordTrace (prefixWord ++ tailWord_5551505) baseStart_5551505 baseEnd_5551505 := by
    simpa [prefixWord, tailWord_5551505, baseEnd_5551505] using wordTrace_append hprefix tailTrace_5551505
  have hstable : (prefixWord ++ tailWord_5551505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551505).length < 2 ^ (prefixWord ++ tailWord_5551505).sum := by decide
  have hdescent : baseEnd_5551505 < baseStart_5551505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551512 : List Nat := [2, 1, 2, 5, 2, 1, 2, 8]
def baseStart_5551512 : Nat := 118140960795 + 5551512 * 2 ^ 59
def prefixEnd_5551512 : Nat := 4983230072969 + 3 ^ 40 * 5551512 * 2
def baseEnd_5551512 : Nat := 105577556118629219165521

theorem tailTrace_5551512 : CollatzResearch.WordTrace tailWord_5551512 prefixEnd_5551512 105577556118629219165521 := by
  unfold tailWord_5551512
  simp only [CollatzResearch.WordTrace]
  refine ⟨101240138531913810805400395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134986851375885081073867193 101240138531913810805400395)
  ·
    refine ⟨151860207797870716208100593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101240138531913810805400395 151860207797870716208100593)
    ·
      refine ⟨113895155848403037156075445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151860207797870716208100593 113895155848403037156075445)
      ·
        refine ⟨10677670860787784733382073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113895155848403037156075445 10677670860787784733382073)
        ·
          refine ⟨8008253145590838550036555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10677670860787784733382073 8008253145590838550036555)
          ·
            refine ⟨12012379718386257825054833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008253145590838550036555 12012379718386257825054833)
            ·
              refine ⟨9009284788789693368791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12012379718386257825054833 9009284788789693368791125)
              ·
                refine ⟨105577556118629219165521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9009284788789693368791125 105577556118629219165521)
                ·
                  rfl

theorem cell23_5551512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 8].length) (baseStart_5551512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551512 prefixEnd_5551512 := by exact prefixLift 5551512
  have htrace : WordTrace (prefixWord ++ tailWord_5551512) baseStart_5551512 baseEnd_5551512 := by
    simpa [prefixWord, tailWord_5551512, baseEnd_5551512] using wordTrace_append hprefix tailTrace_5551512
  have hstable : (prefixWord ++ tailWord_5551512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551512).length < 2 ^ (prefixWord ++ tailWord_5551512).sum := by decide
  have hdescent : baseEnd_5551512 < baseStart_5551512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551516 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_5551516 : Nat := 118140960795 + 5551516 * 2 ^ 59
def prefixEnd_5551516 : Nat := 4983230072969 + 3 ^ 40 * 5551516 * 2
def baseEnd_5551516 : Nat := 950198689708535633939683

theorem tailTrace_5551516 : CollatzResearch.WordTrace tailWord_5551516 prefixEnd_5551516 950198689708535633939683 := by
  unfold tailWord_5551516
  simp only [CollatzResearch.WordTrace]
  refine ⟨101240211477906565146973201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134986948637208753529297601 101240211477906565146973201)
  ·
    refine ⟨75930158608429923860229901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101240211477906565146973201 75930158608429923860229901)
    ·
      refine ⟨28473809478161221447586213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75930158608429923860229901 28473809478161221447586213)
      ·
        refine ⟨5338839277155229021422415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28473809478161221447586213 5338839277155229021422415)
        ·
          refine ⟨8008258915732843532133623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5338839277155229021422415 8008258915732843532133623)
          ·
            refine ⟨12012388373599265298200435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008258915732843532133623 12012388373599265298200435)
            ·
              refine ⟨18018582560398897947300653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12012388373599265298200435 18018582560398897947300653)
              ·
                refine ⟨6756968460149586730237745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18018582560398897947300653 6756968460149586730237745)
                ·
                  refine ⟨5067726345112190047678309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6756968460149586730237745 5067726345112190047678309)
                  ·
                    refine ⟨950198689708535633939683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067726345112190047678309 950198689708535633939683)
                    ·
                      rfl

theorem cell23_5551516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_5551516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551516 prefixEnd_5551516 := by exact prefixLift 5551516
  have htrace : WordTrace (prefixWord ++ tailWord_5551516) baseStart_5551516 baseEnd_5551516 := by
    simpa [prefixWord, tailWord_5551516, baseEnd_5551516] using wordTrace_append hprefix tailTrace_5551516
  have hstable : (prefixWord ++ tailWord_5551516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551516).length < 2 ^ (prefixWord ++ tailWord_5551516).sum := by decide
  have hdescent : baseEnd_5551516 < baseStart_5551516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551556 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5551556 : Nat := 118140960795 + 5551556 * 2 ^ 59
def prefixEnd_5551556 : Nat := 4983230072969 + 3 ^ 40 * 5551556 * 2
def baseEnd_5551556 : Nat := 2850616608351786745318865

theorem tailTrace_5551556 : CollatzResearch.WordTrace tailWord_5551556 prefixEnd_5551556 2850616608351786745318865 := by
  unfold tailWord_5551556
  simp only [CollatzResearch.WordTrace]
  refine ⟨101240940937834108562701261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134987921250445478083601681 101240940937834108562701261)
  ·
    refine ⟨37965352851687790711012973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101240940937834108562701261 37965352851687790711012973)
    ·
      refine ⟨14237007319382921516629865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37965352851687790711012973 14237007319382921516629865)
      ·
        refine ⟨10677755489537191137472399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14237007319382921516629865 10677755489537191137472399)
        ·
          refine ⟨16016633234305786706208599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10677755489537191137472399 16016633234305786706208599)
          ·
            refine ⟨24024949851458680059312899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16016633234305786706208599 24024949851458680059312899)
            ·
              refine ⟨36037424777188020088969349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24024949851458680059312899 36037424777188020088969349)
              ·
                refine ⟨6757017145722753766681753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36037424777188020088969349 6757017145722753766681753)
                ·
                  refine ⟨5067762859292065325011315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757017145722753766681753 5067762859292065325011315)
                  ·
                    refine ⟨7601644288938097987516973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5067762859292065325011315 7601644288938097987516973)
                    ·
                      refine ⟨2850616608351786745318865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7601644288938097987516973 2850616608351786745318865)
                      ·
                        rfl

theorem cell23_5551556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5551556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551556 prefixEnd_5551556 := by exact prefixLift 5551556
  have htrace : WordTrace (prefixWord ++ tailWord_5551556) baseStart_5551556 baseEnd_5551556 := by
    simpa [prefixWord, tailWord_5551556, baseEnd_5551556] using wordTrace_append hprefix tailTrace_5551556
  have hstable : (prefixWord ++ tailWord_5551556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551556).length < 2 ^ (prefixWord ++ tailWord_5551556).sum := by decide
  have hdescent : baseEnd_5551556 < baseStart_5551556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551585 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 9]
def baseStart_5551585 : Nat := 118140960795 + 5551585 * 2 ^ 59
def prefixEnd_5551585 : Nat := 4983230072969 + 3 ^ 40 * 5551585 * 2
def baseEnd_5551585 : Nat := 316736833254529681317359

theorem tailTrace_5551585 : CollatzResearch.WordTrace tailWord_5551585 prefixEnd_5551585 316736833254529681317359 := by
  unfold tailWord_5551585
  simp only [CollatzResearch.WordTrace]
  refine ⟨202482939592563155078208209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134988626395042103385472139 202482939592563155078208209)
  ·
    refine ⟨151862204694422366308656157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202482939592563155078208209 151862204694422366308656157)
    ·
      refine ⟨56948326760408387365746059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151862204694422366308656157 56948326760408387365746059)
      ·
        refine ⟨85422490140612581048619089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56948326760408387365746059 85422490140612581048619089)
        ·
          refine ⟨64066867605459435786464317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85422490140612581048619089 64066867605459435786464317)
          ·
            refine ⟨24025075352047288419924119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64066867605459435786464317 24025075352047288419924119)
            ·
              refine ⟨36037613028070932629886179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24025075352047288419924119 36037613028070932629886179)
              ·
                refine ⟨54056419542106398944829269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36037613028070932629886179 54056419542106398944829269)
                ·
                  refine ⟨316736833254529681317359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54056419542106398944829269 316736833254529681317359)
                  ·
                    rfl

theorem cell23_5551585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_5551585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551585 prefixEnd_5551585 := by exact prefixLift 5551585
  have htrace : WordTrace (prefixWord ++ tailWord_5551585) baseStart_5551585 baseEnd_5551585 := by
    simpa [prefixWord, tailWord_5551585, baseEnd_5551585] using wordTrace_append hprefix tailTrace_5551585
  have hstable : (prefixWord ++ tailWord_5551585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551585).length < 2 ^ (prefixWord ++ tailWord_5551585).sum := by decide
  have hdescent : baseEnd_5551585 < baseStart_5551585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551612 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_5551612 : Nat := 118140960795 + 5551612 * 2 ^ 59
def prefixEnd_5551612 : Nat := 4983230072969 + 3 ^ 40 * 5551612 * 2
def baseEnd_5551612 : Nat := 2850645363268438526218607

theorem tailTrace_5551612 : CollatzResearch.WordTrace tailWord_5551612 prefixEnd_5551612 2850645363268438526218607 := by
  unfold tailWord_5551612
  simp only [CollatzResearch.WordTrace]
  refine ⟨101241962181732669344720545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134989282908976892459627393 101241962181732669344720545)
  ·
    refine ⟨75931471636299502008540409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101241962181732669344720545 75931471636299502008540409)
    ·
      refine ⟨56948603727224626506405307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75931471636299502008540409 56948603727224626506405307)
      ·
        refine ⟨85422905590836939759607961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56948603727224626506405307 85422905590836939759607961)
        ·
          refine ⟨64067179193127704819705971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85422905590836939759607961 64067179193127704819705971)
          ·
            refine ⟨96100768789691557229558957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64067179193127704819705971 96100768789691557229558957)
            ·
              refine ⟨36037788296134333961084609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96100768789691557229558957 36037788296134333961084609)
              ·
                refine ⟨27028341222100750470813457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36037788296134333961084609 27028341222100750470813457)
                ·
                  refine ⟨20271255916575562853110093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27028341222100750470813457 20271255916575562853110093)
                  ·
                    refine ⟨7601720968715836069916285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20271255916575562853110093 7601720968715836069916285)
                    ·
                      refine ⟨2850645363268438526218607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7601720968715836069916285 2850645363268438526218607)
                      ·
                        rfl

theorem cell23_5551612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_5551612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551612 prefixEnd_5551612 := by exact prefixLift 5551612
  have htrace : WordTrace (prefixWord ++ tailWord_5551612) baseStart_5551612 baseEnd_5551612 := by
    simpa [prefixWord, tailWord_5551612, baseEnd_5551612] using wordTrace_append hprefix tailTrace_5551612
  have hstable : (prefixWord ++ tailWord_5551612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551612).length < 2 ^ (prefixWord ++ tailWord_5551612).sum := by decide
  have hdescent : baseEnd_5551612 < baseStart_5551612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551613 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_5551613 : Nat := 118140960795 + 5551613 * 2 ^ 59
def prefixEnd_5551613 : Nat := 4983230072969 + 3 ^ 40 * 5551613 * 2
def baseEnd_5551613 : Nat := 2850645876749093022306103

theorem tailTrace_5551613 : CollatzResearch.WordTrace tailWord_5551613 prefixEnd_5551613 2850645876749093022306103 := by
  unfold tailWord_5551613
  simp only [CollatzResearch.WordTrace]
  refine ⟨202483960836461715860227493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134989307224307810573484995 202483960836461715860227493)
  ·
    refine ⟨37965742656836571723792655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202483960836461715860227493 37965742656836571723792655)
    ·
      refine ⟨56948613985254857585688983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37965742656836571723792655 56948613985254857585688983)
      ·
        refine ⟨85422920977882286378533475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56948613985254857585688983 85422920977882286378533475)
        ·
          refine ⟨128134381466823429567800213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85422920977882286378533475 128134381466823429567800213)
          ·
            refine ⟨6006299131257348260990635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128134381466823429567800213 6006299131257348260990635)
            ·
              refine ⟨9009448696886022391485953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6006299131257348260990635 9009448696886022391485953)
              ·
                refine ⟨6757086522664516793614465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9009448696886022391485953 6757086522664516793614465)
                ·
                  refine ⟨5067814891998387595210849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757086522664516793614465 5067814891998387595210849)
                  ·
                    refine ⟨3800861168998790696408137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067814891998387595210849 3800861168998790696408137)
                    ·
                      refine ⟨2850645876749093022306103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800861168998790696408137 2850645876749093022306103)
                      ·
                        rfl

theorem cell23_5551613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_5551613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551613 prefixEnd_5551613 := by exact prefixLift 5551613
  have htrace : WordTrace (prefixWord ++ tailWord_5551613) baseStart_5551613 baseEnd_5551613 := by
    simpa [prefixWord, tailWord_5551613, baseEnd_5551613] using wordTrace_append hprefix tailTrace_5551613
  have hstable : (prefixWord ++ tailWord_5551613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551613).length < 2 ^ (prefixWord ++ tailWord_5551613).sum := by decide
  have hdescent : baseEnd_5551613 < baseStart_5551613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551625 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_5551625 : Nat := 118140960795 + 5551625 * 2 ^ 59
def prefixEnd_5551625 : Nat := 4983230072969 + 3 ^ 40 * 5551625 * 2
def baseEnd_5551625 : Nat := 2850652038516946975356047

theorem tailTrace_5551625 : CollatzResearch.WordTrace tailWord_5551625 prefixEnd_5551625 2850652038516946975356047 := by
  unfold tailWord_5551625
  simp only [CollatzResearch.WordTrace]
  refine ⟨202484398512418241909664329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134989599008278827939776219 202484398512418241909664329)
  ·
    refine ⟨151863298884313681432248247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202484398512418241909664329 151863298884313681432248247)
    ·
      refine ⟨227794948326470522148372371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151863298884313681432248247 227794948326470522148372371)
      ·
        refine ⟨341692422489705783222558557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227794948326470522148372371 341692422489705783222558557)
        ·
          refine ⟨128134658433639668708459459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341692422489705783222558557 128134658433639668708459459)
          ·
            refine ⟨192201987650459503062689189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128134658433639668708459459 192201987650459503062689189)
            ·
              refine ⟨36037872684461156824254223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192201987650459503062689189 36037872684461156824254223)
              ·
                refine ⟨54056809026691735236381335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36037872684461156824254223 54056809026691735236381335)
                ·
                  refine ⟨81085213540037602854572003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54056809026691735236381335 81085213540037602854572003)
                  ·
                    refine ⟨121627820310056404281858005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81085213540037602854572003 121627820310056404281858005)
                    ·
                      refine ⟨2850652038516946975356047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121627820310056404281858005 2850652038516946975356047)
                      ·
                        rfl

theorem cell23_5551625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_5551625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551625 prefixEnd_5551625 := by exact prefixLift 5551625
  have htrace : WordTrace (prefixWord ++ tailWord_5551625) baseStart_5551625 baseEnd_5551625 := by
    simpa [prefixWord, tailWord_5551625, baseEnd_5551625] using wordTrace_append hprefix tailTrace_5551625
  have hstable : (prefixWord ++ tailWord_5551625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551625).length < 2 ^ (prefixWord ++ tailWord_5551625).sum := by decide
  have hdescent : baseEnd_5551625 < baseStart_5551625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551630 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5551630 : Nat := 118140960795 + 5551630 * 2 ^ 59
def prefixEnd_5551630 : Nat := 4983230072969 + 3 ^ 40 * 5551630 * 2
def baseEnd_5551630 : Nat := 2850654605920219455793525

theorem tailTrace_5551630 : CollatzResearch.WordTrace tailWord_5551630 prefixEnd_5551630 2850654605920219455793525 := by
  unfold tailWord_5551630
  simp only [CollatzResearch.WordTrace]
  refine ⟨25310572609675015970449543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134989720584933418509064229 25310572609675015970449543)
  ·
    refine ⟨37965858914512523955674315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25310572609675015970449543 37965858914512523955674315)
    ·
      refine ⟨56948788371768785933511473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37965858914512523955674315 56948788371768785933511473)
      ·
        refine ⟨42711591278826589450133605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56948788371768785933511473 42711591278826589450133605)
        ·
          refine ⟨8008423364779985521900051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42711591278826589450133605 8008423364779985521900051)
          ·
            refine ⟨12012635047169978282850077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008423364779985521900051 12012635047169978282850077)
            ·
              refine ⟨4504738142688741856068779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12012635047169978282850077 4504738142688741856068779)
              ·
                refine ⟨6757107214033112784103169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504738142688741856068779 6757107214033112784103169)
                ·
                  refine ⟨5067830410524834588077377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757107214033112784103169 5067830410524834588077377)
                  ·
                    refine ⟨3800872807893625941058033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067830410524834588077377 3800872807893625941058033)
                    ·
                      refine ⟨2850654605920219455793525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3800872807893625941058033 2850654605920219455793525)
                      ·
                        rfl

theorem cell23_5551630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5551630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551630 prefixEnd_5551630 := by exact prefixLift 5551630
  have htrace : WordTrace (prefixWord ++ tailWord_5551630) baseStart_5551630 baseEnd_5551630 := by
    simpa [prefixWord, tailWord_5551630, baseEnd_5551630] using wordTrace_append hprefix tailTrace_5551630
  have hstable : (prefixWord ++ tailWord_5551630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551630).length < 2 ^ (prefixWord ++ tailWord_5551630).sum := by decide
  have hdescent : baseEnd_5551630 < baseStart_5551630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551669 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5551669 : Nat := 118140960795 + 5551669 * 2 ^ 59
def prefixEnd_5551669 : Nat := 4983230072969 + 3 ^ 40 * 5551669 * 2
def baseEnd_5551669 : Nat := 2850674631665744803205845

theorem tailTrace_5551669 : CollatzResearch.WordTrace tailWord_5551669 prefixEnd_5551669 2850674631665744803205845 := by
  unfold tailWord_5551669
  simp only [CollatzResearch.WordTrace]
  refine ⟨202486003324258837424266061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134990668882839224949510707 202486003324258837424266061)
  ·
    refine ⟨75932251246597064034099773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202486003324258837424266061 75932251246597064034099773)
    ·
      refine ⟨28474594217473899012787415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75932251246597064034099773 28474594217473899012787415)
      ·
        refine ⟨42711891326210848519181123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28474594217473899012787415 42711891326210848519181123)
        ·
          refine ⟨64067836989316272778771685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42711891326210848519181123 64067836989316272778771685)
          ·
            refine ⟨12012719435496801146019691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64067836989316272778771685 12012719435496801146019691)
            ·
              refine ⟨18019079153245201719029537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12012719435496801146019691 18019079153245201719029537)
              ·
                refine ⟨13514309364933901289272153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18019079153245201719029537 13514309364933901289272153)
                ·
                  refine ⟨10135732023700425966954115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13514309364933901289272153 10135732023700425966954115)
                  ·
                    refine ⟨15203598035550638950431173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10135732023700425966954115 15203598035550638950431173)
                    ·
                      refine ⟨2850674631665744803205845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15203598035550638950431173 2850674631665744803205845)
                      ·
                        rfl

theorem cell23_5551669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5551669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551669 prefixEnd_5551669 := by exact prefixLift 5551669
  have htrace : WordTrace (prefixWord ++ tailWord_5551669) baseStart_5551669 baseEnd_5551669 := by
    simpa [prefixWord, tailWord_5551669, baseEnd_5551669] using wordTrace_append hprefix tailTrace_5551669
  have hstable : (prefixWord ++ tailWord_5551669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551669).length < 2 ^ (prefixWord ++ tailWord_5551669).sum := by decide
  have hdescent : baseEnd_5551669 < baseStart_5551669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551679 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 3, 4]
def baseStart_5551679 : Nat := 118140960795 + 5551679 * 2 ^ 59
def prefixEnd_5551679 : Nat := 4983230072969 + 3 ^ 40 * 5551679 * 2
def baseEnd_5551679 : Nat := 950226588824096588026933

theorem tailTrace_5551679 : CollatzResearch.WordTrace tailWord_5551679 prefixEnd_5551679 950226588824096588026933 := by
  unfold tailWord_5551679
  simp only [CollatzResearch.WordTrace]
  refine ⟨202486368054222609132130091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134990912036148406088086727 202486368054222609132130091)
  ·
    refine ⟨303729552081333913698195137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202486368054222609132130091 303729552081333913698195137)
    ·
      refine ⟨227797164061000435273646353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303729552081333913698195137 227797164061000435273646353)
      ·
        refine ⟨170847873045750326455234765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227797164061000435273646353 170847873045750326455234765)
        ·
          refine ⟨64067952392156372420713037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170847873045750326455234765 64067952392156372420713037)
          ·
            refine ⟨24025482147058639657767389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64067952392156372420713037 24025482147058639657767389)
            ·
              refine ⟨9009555805146989871662771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24025482147058639657767389 9009555805146989871662771)
              ·
                refine ⟨13514333707720484807494157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009555805146989871662771 13514333707720484807494157)
                ·
                  refine ⟨5067875140395181802810309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13514333707720484807494157 5067875140395181802810309)
                  ·
                    refine ⟨950226588824096588026933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067875140395181802810309 950226588824096588026933)
                    ·
                      rfl

theorem cell23_5551679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_5551679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551679 prefixEnd_5551679 := by exact prefixLift 5551679
  have htrace : WordTrace (prefixWord ++ tailWord_5551679) baseStart_5551679 baseEnd_5551679 := by
    simpa [prefixWord, tailWord_5551679, baseEnd_5551679] using wordTrace_append hprefix tailTrace_5551679
  have hstable : (prefixWord ++ tailWord_5551679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551679).length < 2 ^ (prefixWord ++ tailWord_5551679).sum := by decide
  have hdescent : baseEnd_5551679 < baseStart_5551679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551726 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_5551726 : Nat := 118140960795 + 5551726 * 2 ^ 59
def prefixEnd_5551726 : Nat := 4983230072969 + 3 ^ 40 * 5551726 * 2
def baseEnd_5551726 : Nat := 316744877784783453354787

theorem tailTrace_5551726 : CollatzResearch.WordTrace tailWord_5551726 prefixEnd_5551726 316744877784783453354787 := by
  unfold tailWord_5551726
  simp only [CollatzResearch.WordTrace]
  refine ⟨25311010285631542019886379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134992054856701557439394021 25311010285631542019886379)
  ·
    refine ⟨37966515428447313029829569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25311010285631542019886379 37966515428447313029829569)
    ·
      refine ⟨28474886571335484772372177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37966515428447313029829569 28474886571335484772372177)
      ·
        refine ⟨21356164928501613579279133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28474886571335484772372177 21356164928501613579279133)
        ·
          refine ⟨8008561848188105092229675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21356164928501613579279133 8008561848188105092229675)
          ·
            refine ⟨12012842772282157638344513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008561848188105092229675 12012842772282157638344513)
            ·
              refine ⟨9009632079211618228758385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12012842772282157638344513 9009632079211618228758385)
              ·
                refine ⟨6757224059408713671568789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9009632079211618228758385 6757224059408713671568789)
                ·
                  refine ⟨316744877784783453354787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6757224059408713671568789 316744877784783453354787)
                  ·
                    rfl

theorem cell23_5551726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_5551726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551726 prefixEnd_5551726 := by exact prefixLift 5551726
  have htrace : WordTrace (prefixWord ++ tailWord_5551726) baseStart_5551726 baseEnd_5551726 := by
    simpa [prefixWord, tailWord_5551726, baseEnd_5551726] using wordTrace_append hprefix tailTrace_5551726
  have hstable : (prefixWord ++ tailWord_5551726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551726).length < 2 ^ (prefixWord ++ tailWord_5551726).sum := by decide
  have hdescent : baseEnd_5551726 < baseStart_5551726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551730 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_5551730 : Nat := 118140960795 + 5551730 * 2 ^ 59
def prefixEnd_5551730 : Nat := 4983230072969 + 3 ^ 40 * 5551730 * 2
def baseEnd_5551730 : Nat := 950235317995223021514355

theorem tailTrace_5551730 : CollatzResearch.WordTrace tailWord_5551730 prefixEnd_5551730 950235317995223021514355 := by
  unfold tailWord_5551730
  simp only [CollatzResearch.WordTrace]
  refine ⟨50622057044259461210559161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134992152118025229894824429 50622057044259461210559161)
  ·
    refine ⟨37966542783194595907919371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50622057044259461210559161 37966542783194595907919371)
    ·
      refine ⟨56949814174791893861879057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37966542783194595907919371 56949814174791893861879057)
      ·
        refine ⟨42712360631093920396409293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56949814174791893861879057 42712360631093920396409293)
        ·
          refine ⟨16017135236660220148653485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42712360631093920396409293 16017135236660220148653485)
          ·
            refine ⟨6006425713747582555745057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16017135236660220148653485 6006425713747582555745057)
            ·
              refine ⟨4504819285310686916808793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6006425713747582555745057 4504819285310686916808793)
              ·
                refine ⟨3378614463983015187606595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4504819285310686916808793 3378614463983015187606595)
                ·
                  refine ⟨5067921695974522781409893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378614463983015187606595 5067921695974522781409893)
                  ·
                    refine ⟨950235317995223021514355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067921695974522781409893 950235317995223021514355)
                    ·
                      rfl

theorem cell23_5551730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_5551730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551730 prefixEnd_5551730 := by exact prefixLift 5551730
  have htrace : WordTrace (prefixWord ++ tailWord_5551730) baseStart_5551730 baseEnd_5551730 := by
    simpa [prefixWord, tailWord_5551730, baseEnd_5551730] using wordTrace_append hprefix tailTrace_5551730
  have hstable : (prefixWord ++ tailWord_5551730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551730).length < 2 ^ (prefixWord ++ tailWord_5551730).sum := by decide
  have hdescent : baseEnd_5551730 < baseStart_5551730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551776 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4]
def baseStart_5551776 : Nat := 118140960795 + 5551776 * 2 ^ 59
def prefixEnd_5551776 : Nat := 4983230072969 + 3 ^ 40 * 5551776 * 2
def baseEnd_5551776 : Nat := 2850729574095775884567853

theorem tailTrace_5551776 : CollatzResearch.WordTrace tailWord_5551776 prefixEnd_5551776 2850729574095775884567853 := by
  unfold tailWord_5551776
  simp only [CollatzResearch.WordTrace]
  refine ⟨101244952967435597349205591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134993270623247463132274121 101244952967435597349205591)
  ·
    refine ⟨151867429451153396023808387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101244952967435597349205591 151867429451153396023808387)
    ·
      refine ⟨227801144176730094035712581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151867429451153396023808387 227801144176730094035712581)
      ·
        refine ⟨42712714533136892631696109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227801144176730094035712581 42712714533136892631696109)
        ·
          refine ⟨16017267949926334736886041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42712714533136892631696109 16017267949926334736886041)
          ·
            refine ⟨12012950962444751052664531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16017267949926334736886041 12012950962444751052664531)
            ·
              refine ⟨18019426443667126578996797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12012950962444751052664531 18019426443667126578996797)
              ·
                refine ⟨6757284916375172467123799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18019426443667126578996797 6757284916375172467123799)
                ·
                  refine ⟨10135927374562758700685699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6757284916375172467123799 10135927374562758700685699)
                  ·
                    refine ⟨15203891061844138051028549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10135927374562758700685699 15203891061844138051028549)
                    ·
                      refine ⟨2850729574095775884567853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15203891061844138051028549 2850729574095775884567853)
                      ·
                        rfl

theorem cell23_5551776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_5551776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551776 prefixEnd_5551776 := by exact prefixLift 5551776
  have htrace : WordTrace (prefixWord ++ tailWord_5551776) baseStart_5551776 baseEnd_5551776 := by
    simpa [prefixWord, tailWord_5551776, baseEnd_5551776] using wordTrace_append hprefix tailTrace_5551776
  have hstable : (prefixWord ++ tailWord_5551776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551776).length < 2 ^ (prefixWord ++ tailWord_5551776).sum := by decide
  have hdescent : baseEnd_5551776 < baseStart_5551776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551789 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_5551789 : Nat := 118140960795 + 5551789 * 2 ^ 59
def prefixEnd_5551789 : Nat := 4983230072969 + 3 ^ 40 * 5551789 * 2
def baseEnd_5551789 : Nat := 2850736249344284333705293

theorem tailTrace_5551789 : CollatzResearch.WordTrace tailWord_5551789 prefixEnd_5551789 2850736249344284333705293 := by
  unfold tailWord_5551789
  simp only [CollatzResearch.WordTrace]
  refine ⟨202490380083824097918634421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134993586722549398612422947 202490380083824097918634421)
  ·
    refine ⟨18983473132858509179871977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202490380083824097918634421 18983473132858509179871977)
    ·
      refine ⟨14237604849643881884903983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18983473132858509179871977 14237604849643881884903983)
      ·
        refine ⟨21356407274465822827355975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14237604849643881884903983 21356407274465822827355975)
        ·
          refine ⟨32034610911698734241033963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21356407274465822827355975 32034610911698734241033963)
          ·
            refine ⟨48051916367548101361550945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32034610911698734241033963 48051916367548101361550945)
            ·
              refine ⟨36038937275661076021163209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48051916367548101361550945 36038937275661076021163209)
              ·
                refine ⟨27029202956745807015872407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36038937275661076021163209 27029202956745807015872407)
                ·
                  refine ⟨40543804435118710523808611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27029202956745807015872407 40543804435118710523808611)
                  ·
                    refine ⟨60815706652678065785712917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40543804435118710523808611 60815706652678065785712917)
                    ·
                      refine ⟨2850736249344284333705293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60815706652678065785712917 2850736249344284333705293)
                      ·
                        rfl

theorem cell23_5551789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_5551789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551789 prefixEnd_5551789 := by exact prefixLift 5551789
  have htrace : WordTrace (prefixWord ++ tailWord_5551789) baseStart_5551789 baseEnd_5551789 := by
    simpa [prefixWord, tailWord_5551789, baseEnd_5551789] using wordTrace_append hprefix tailTrace_5551789
  have hstable : (prefixWord ++ tailWord_5551789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551789).length < 2 ^ (prefixWord ++ tailWord_5551789).sum := by decide
  have hdescent : baseEnd_5551789 < baseStart_5551789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551806 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_5551806 : Nat := 118140960795 + 5551806 * 2 ^ 59
def prefixEnd_5551806 : Nat := 4983230072969 + 3 ^ 40 * 5551806 * 2
def baseEnd_5551806 : Nat := 2850744978515410767192715

theorem tailTrace_5551806 : CollatzResearch.WordTrace tailWord_5551806 prefixEnd_5551806 2850744978515410767192715 := by
  unfold tailWord_5551806
  simp only [CollatzResearch.WordTrace]
  refine ⟨25311375015595313727750409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134994000083175006548002181 25311375015595313727750409)
  ·
    refine ⟨18983531261696485295812807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25311375015595313727750409 18983531261696485295812807)
    ·
      refine ⟨28475296892544727943719211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18983531261696485295812807 28475296892544727943719211)
      ·
        refine ⟨42712945338817091915578817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28475296892544727943719211 42712945338817091915578817)
        ·
          refine ⟨32034709004112818936684113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42712945338817091915578817 32034709004112818936684113)
          ·
            refine ⟨24026031753084614202513085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32034709004112818936684113 24026031753084614202513085)
            ·
              refine ⟨9009761907406730325942407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24026031753084614202513085 9009761907406730325942407)
              ·
                refine ⟨13514642861110095488913611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009761907406730325942407 13514642861110095488913611)
                ·
                  refine ⟨20271964291665143233370417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13514642861110095488913611 20271964291665143233370417)
                  ·
                    refine ⟨15203973218748857425027813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20271964291665143233370417 15203973218748857425027813)
                    ·
                      refine ⟨2850744978515410767192715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15203973218748857425027813 2850744978515410767192715)
                      ·
                        rfl

theorem cell23_5551806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_5551806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551806 prefixEnd_5551806 := by exact prefixLift 5551806
  have htrace : WordTrace (prefixWord ++ tailWord_5551806) baseStart_5551806 baseEnd_5551806 := by
    simpa [prefixWord, tailWord_5551806, baseEnd_5551806] using wordTrace_append hprefix tailTrace_5551806
  have hstable : (prefixWord ++ tailWord_5551806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551806).length < 2 ^ (prefixWord ++ tailWord_5551806).sum := by decide
  have hdescent : baseEnd_5551806 < baseStart_5551806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551819 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 7, 2]
def baseStart_5551819 : Nat := 118140960795 + 5551819 * 2 ^ 59
def prefixEnd_5551819 : Nat := 4983230072969 + 3 ^ 40 * 5551819 * 2
def baseEnd_5551819 : Nat := 2850751653763919216330155

theorem tailTrace_5551819 : CollatzResearch.WordTrace tailWord_5551819 prefixEnd_5551819 2850751653763919216330155 := by
  unfold tailWord_5551819
  simp only [CollatzResearch.WordTrace]
  refine ⟨202491474273715413042226511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134994316182476942028151007 202491474273715413042226511)
  ·
    refine ⟨303737211410573119563339767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202491474273715413042226511 303737211410573119563339767)
    ·
      refine ⟨455605817115859679345009651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303737211410573119563339767 455605817115859679345009651)
      ·
        refine ⟨683408725673789519017514477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455605817115859679345009651 683408725673789519017514477)
        ·
          refine ⟨256278272127671069631567929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 683408725673789519017514477 256278272127671069631567929)
          ·
            refine ⟨192208704095753302223675947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256278272127671069631567929 192208704095753302223675947)
            ·
              refine ⟨288313056143629953335513921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192208704095753302223675947 288313056143629953335513921)
              ·
                refine ⟨216234792107722465001635441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288313056143629953335513921 216234792107722465001635441)
                ·
                  refine ⟨162176094080791848751226581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216234792107722465001635441 162176094080791848751226581)
                  ·
                    refine ⟨3801002205018558955106873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162176094080791848751226581 3801002205018558955106873)
                    ·
                      refine ⟨2850751653763919216330155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801002205018558955106873 2850751653763919216330155)
                      ·
                        rfl

theorem cell23_5551819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7, 2].length) (baseStart_5551819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551819 prefixEnd_5551819 := by exact prefixLift 5551819
  have htrace : WordTrace (prefixWord ++ tailWord_5551819) baseStart_5551819 baseEnd_5551819 := by
    simpa [prefixWord, tailWord_5551819, baseEnd_5551819] using wordTrace_append hprefix tailTrace_5551819
  have hstable : (prefixWord ++ tailWord_5551819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551819).length < 2 ^ (prefixWord ++ tailWord_5551819).sum := by decide
  have hdescent : baseEnd_5551819 < baseStart_5551819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551830 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_5551830 : Nat := 118140960795 + 5551830 * 2 ^ 59
def prefixEnd_5551830 : Nat := 4983230072969 + 3 ^ 40 * 5551830 * 2
def baseEnd_5551830 : Nat := 2850757302051118673292605

theorem tailTrace_5551830 : CollatzResearch.WordTrace tailWord_5551830 prefixEnd_5551830 2850757302051118673292605 := by
  unfold tailWord_5551830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655742217292222620054809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134994583651117041280584629 12655742217292222620054809)
  ·
    refine ⟨9491806662969166965041107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12655742217292222620054809 9491806662969166965041107)
    ·
      refine ⟨14237709994453750447561661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9491806662969166965041107 14237709994453750447561661)
      ·
        refine ⟨5339141247920156417835623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14237709994453750447561661 5339141247920156417835623)
        ·
          refine ⟨8008711871880234626753435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5339141247920156417835623 8008711871880234626753435)
          ·
            refine ⟨12013067807820351940130153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008711871880234626753435 12013067807820351940130153)
            ·
              refine ⟨9009800855865263955097615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12013067807820351940130153 9009800855865263955097615)
              ·
                refine ⟨13514701283797895932646423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009800855865263955097615 13514701283797895932646423)
                ·
                  refine ⟨20272051925696843898969635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13514701283797895932646423 20272051925696843898969635)
                  ·
                    refine ⟨30408077888545265848454453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20272051925696843898969635 30408077888545265848454453)
                    ·
                      refine ⟨2850757302051118673292605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30408077888545265848454453 2850757302051118673292605)
                      ·
                        rfl

theorem cell23_5551830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_5551830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551830 prefixEnd_5551830 := by exact prefixLift 5551830
  have htrace : WordTrace (prefixWord ++ tailWord_5551830) baseStart_5551830 baseEnd_5551830 := by
    simpa [prefixWord, tailWord_5551830, baseEnd_5551830] using wordTrace_append hprefix tailTrace_5551830
  have hstable : (prefixWord ++ tailWord_5551830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551830).length < 2 ^ (prefixWord ++ tailWord_5551830).sum := by decide
  have hdescent : baseEnd_5551830 < baseStart_5551830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551866 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2]
def baseStart_5551866 : Nat := 118140960795 + 5551866 * 2 ^ 59
def prefixEnd_5551866 : Nat := 4983230072969 + 3 ^ 40 * 5551866 * 2
def baseEnd_5551866 : Nat := 2850775787354680532442439

theorem tailTrace_5551866 : CollatzResearch.WordTrace tailWord_5551866 prefixEnd_5551866 2850775787354680532442439 := by
  unfold tailWord_5551866
  simp only [CollatzResearch.WordTrace]
  refine ⟨50623297126136285017296863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134995459003030093379458301 50623297126136285017296863)
  ·
    refine ⟨75934945689204427525945295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50623297126136285017296863 75934945689204427525945295)
    ·
      refine ⟨113902418533806641288917943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75934945689204427525945295 113902418533806641288917943)
      ·
        refine ⟨170853627800709961933376915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113902418533806641288917943 170853627800709961933376915)
        ·
          refine ⟨256280441701064942900065373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170853627800709961933376915 256280441701064942900065373)
          ·
            refine ⟨96105165637899353587524515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256280441701064942900065373 96105165637899353587524515)
            ·
              refine ⟨144157748456849030381286773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96105165637899353587524515 144157748456849030381286773)
              ·
                refine ⟨13514788917829596598245635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144157748456849030381286773 13514788917829596598245635)
                ·
                  refine ⟨20272183376744394897368453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13514788917829596598245635 20272183376744394897368453)
                  ·
                    refine ⟨3801034383139574043256585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20272183376744394897368453 3801034383139574043256585)
                    ·
                      refine ⟨2850775787354680532442439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801034383139574043256585 2850775787354680532442439)
                      ·
                        rfl

theorem cell23_5551866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_5551866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551866 prefixEnd_5551866 := by exact prefixLift 5551866
  have htrace : WordTrace (prefixWord ++ tailWord_5551866) baseStart_5551866 baseEnd_5551866 := by
    simpa [prefixWord, tailWord_5551866, baseEnd_5551866] using wordTrace_append hprefix tailTrace_5551866
  have hstable : (prefixWord ++ tailWord_5551866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551866).length < 2 ^ (prefixWord ++ tailWord_5551866).sum := by decide
  have hdescent : baseEnd_5551866 < baseStart_5551866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551869 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_5551869 : Nat := 118140960795 + 5551869 * 2 ^ 59
def prefixEnd_5551869 : Nat := 4983230072969 + 3 ^ 40 * 5551869 * 2
def baseEnd_5551869 : Nat := 2850777327796644020704925

theorem tailTrace_5551869 : CollatzResearch.WordTrace tailWord_5551869 prefixEnd_5551869 2850777327796644020704925 := by
  unfold tailWord_5551869
  simp only [CollatzResearch.WordTrace]
  refine ⟨202493297923534271581546661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134995531949022847721031107 202493297923534271581546661)
  ·
    refine ⟨37967493360662675921539999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202493297923534271581546661 37967493360662675921539999)
    ·
      refine ⟨56951240040994013882309999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37967493360662675921539999 56951240040994013882309999)
      ·
        refine ⟨85426860061491020823464999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56951240040994013882309999 85426860061491020823464999)
        ·
          refine ⟨128140290092236531235197499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85426860061491020823464999 128140290092236531235197499)
          ·
            refine ⟨192210435138354796852796249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128140290092236531235197499 192210435138354796852796249)
            ·
              refine ⟨144157826353766097639597187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192210435138354796852796249 144157826353766097639597187)
              ·
                refine ⟨216236739530649146459395781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144157826353766097639597187 216236739530649146459395781)
                ·
                  refine ⟨40544388661996714961136709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216236739530649146459395781 40544388661996714961136709)
                  ·
                    refine ⟨7602072874124384055213133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40544388661996714961136709 7602072874124384055213133)
                    ·
                      refine ⟨2850777327796644020704925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7602072874124384055213133 2850777327796644020704925)
                      ·
                        rfl

theorem cell23_5551869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_5551869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551869 prefixEnd_5551869 := by exact prefixLift 5551869
  have htrace : WordTrace (prefixWord ++ tailWord_5551869) baseStart_5551869 baseEnd_5551869 := by
    simpa [prefixWord, tailWord_5551869, baseEnd_5551869] using wordTrace_append hprefix tailTrace_5551869
  have hstable : (prefixWord ++ tailWord_5551869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551869).length < 2 ^ (prefixWord ++ tailWord_5551869).sum := by decide
  have hdescent : baseEnd_5551869 < baseStart_5551869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551870 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_5551870 : Nat := 118140960795 + 5551870 * 2 ^ 59
def prefixEnd_5551870 : Nat := 4983230072969 + 3 ^ 40 * 5551870 * 2
def baseEnd_5551870 : Nat := 2850777841277298516792421

theorem tailTrace_5551870 : CollatzResearch.WordTrace tailWord_5551870 prefixEnd_5551870 2850777841277298516792421 := by
  unfold tailWord_5551870
  simp only [CollatzResearch.WordTrace]
  refine ⟨25311666799566331094041633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134995556264353765834888709 25311666799566331094041633)
  ·
    refine ⟨18983750099674748320531225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25311666799566331094041633 18983750099674748320531225)
    ·
      refine ⟨14237812574756061240398419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18983750099674748320531225 14237812574756061240398419)
      ·
        refine ⟨21356718862134091860597629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14237812574756061240398419 21356718862134091860597629)
        ·
          refine ⟨8008769573300284447724111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21356718862134091860597629 8008769573300284447724111)
          ·
            refine ⟨12013154359950426671586167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008769573300284447724111 12013154359950426671586167)
            ·
              refine ⟨18019731539925640007379251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12013154359950426671586167 18019731539925640007379251)
              ·
                refine ⟨27029597309888460011068877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18019731539925640007379251 27029597309888460011068877)
                ·
                  refine ⟨10136098991208172504150829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27029597309888460011068877 10136098991208172504150829)
                  ·
                    refine ⟨3801037121703064689056561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10136098991208172504150829 3801037121703064689056561)
                    ·
                      refine ⟨2850777841277298516792421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801037121703064689056561 2850777841277298516792421)
                      ·
                        rfl

theorem cell23_5551870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_5551870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551870 prefixEnd_5551870 := by exact prefixLift 5551870
  have htrace : WordTrace (prefixWord ++ tailWord_5551870) baseStart_5551870 baseEnd_5551870 := by
    simpa [prefixWord, tailWord_5551870, baseEnd_5551870] using wordTrace_append hprefix tailTrace_5551870
  have hstable : (prefixWord ++ tailWord_5551870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551870).length < 2 ^ (prefixWord ++ tailWord_5551870).sum := by decide
  have hdescent : baseEnd_5551870 < baseStart_5551870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551899 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 3]
def baseStart_5551899 : Nat := 118140960795 + 5551899 * 2 ^ 59
def prefixEnd_5551899 : Nat := 4983230072969 + 3 ^ 40 * 5551899 * 2
def baseEnd_5551899 : Nat := 2850792732216278903329787

theorem tailTrace_5551899 : CollatzResearch.WordTrace tailWord_5551899 prefixEnd_5551899 2850792732216278903329787 := by
  unfold tailWord_5551899
  simp only [CollatzResearch.WordTrace]
  refine ⟨202494392113425586705138751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134996261408950391136759167 202494392113425586705138751)
  ·
    refine ⟨303741588170138380057708127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202494392113425586705138751 303741588170138380057708127)
    ·
      refine ⟨455612382255207570086562191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303741588170138380057708127 455612382255207570086562191)
      ·
        refine ⟨683418573382811355129843287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455612382255207570086562191 683418573382811355129843287)
        ·
          refine ⟨1025127860074217032694764931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683418573382811355129843287 1025127860074217032694764931)
          ·
            refine ⟨1537691790111325549042147397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025127860074217032694764931 1537691790111325549042147397)
            ·
              refine ⟨288317210645873540445402637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1537691790111325549042147397 288317210645873540445402637)
              ·
                refine ⟨108118953992202577667025989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288317210645873540445402637 108118953992202577667025989)
                ·
                  refine ⟨20272303873537983312567373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108118953992202577667025989 20272303873537983312567373)
                  ·
                    refine ⟨7602113952576743742212765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20272303873537983312567373 7602113952576743742212765)
                    ·
                      refine ⟨2850792732216278903329787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7602113952576743742212765 2850792732216278903329787)
                      ·
                        rfl

theorem cell23_5551899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 3].length) (baseStart_5551899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551899 prefixEnd_5551899 := by exact prefixLift 5551899
  have htrace : WordTrace (prefixWord ++ tailWord_5551899) baseStart_5551899 baseEnd_5551899 := by
    simpa [prefixWord, tailWord_5551899, baseEnd_5551899] using wordTrace_append hprefix tailTrace_5551899
  have hstable : (prefixWord ++ tailWord_5551899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551899).length < 2 ^ (prefixWord ++ tailWord_5551899).sum := by decide
  have hdescent : baseEnd_5551899 < baseStart_5551899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551900 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_5551900 : Nat := 118140960795 + 5551900 * 2 ^ 59
def prefixEnd_5551900 : Nat := 4983230072969 + 3 ^ 40 * 5551900 * 2
def baseEnd_5551900 : Nat := 2850793245696933399417283

theorem tailTrace_5551900 : CollatzResearch.WordTrace tailWord_5551900 prefixEnd_5551900 2850793245696933399417283 := by
  unfold tailWord_5551900
  simp only [CollatzResearch.WordTrace]
  refine ⟨101247214293210981937962577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134996285724281309250616769 101247214293210981937962577)
  ·
    refine ⟨75935410719908236453471933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101247214293210981937962577 75935410719908236453471933)
    ·
      refine ⟨28475779019965588670051975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75935410719908236453471933 28475779019965588670051975)
      ·
        refine ⟨42713668529948383005077963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28475779019965588670051975 42713668529948383005077963)
        ·
          refine ⟨64070502794922574507616945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42713668529948383005077963 64070502794922574507616945)
          ·
            refine ⟨48052877096191930880712709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64070502794922574507616945 48052877096191930880712709)
            ·
              refine ⟨9009914455535987040133633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48052877096191930880712709 9009914455535987040133633)
              ·
                refine ⟨6757435841651990280100225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9009914455535987040133633 6757435841651990280100225)
                ·
                  refine ⟨5068076881238992710075169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757435841651990280100225 5068076881238992710075169)
                  ·
                    refine ⟨3801057660929244532556377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5068076881238992710075169 3801057660929244532556377)
                    ·
                      refine ⟨2850793245696933399417283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801057660929244532556377 2850793245696933399417283)
                      ·
                        rfl

theorem cell23_5551900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_5551900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551900 prefixEnd_5551900 := by exact prefixLift 5551900
  have htrace : WordTrace (prefixWord ++ tailWord_5551900) baseStart_5551900 baseEnd_5551900 := by
    simpa [prefixWord, tailWord_5551900, baseEnd_5551900] using wordTrace_append hprefix tailTrace_5551900
  have hstable : (prefixWord ++ tailWord_5551900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551900).length < 2 ^ (prefixWord ++ tailWord_5551900).sum := by decide
  have hdescent : baseEnd_5551900 < baseStart_5551900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551916 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_5551916 : Nat := 118140960795 + 5551916 * 2 ^ 59
def prefixEnd_5551916 : Nat := 4983230072969 + 3 ^ 40 * 5551916 * 2
def baseEnd_5551916 : Nat := 2850801461387405336817209

theorem tailTrace_5551916 : CollatzResearch.WordTrace tailWord_5551916 prefixEnd_5551916 2850801461387405336817209 := by
  unfold tailWord_5551916
  simp only [CollatzResearch.WordTrace]
  refine ⟨101247506077181999304253801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134996674769575999072338401 101247506077181999304253801)
  ·
    refine ⟨75935629557886499478190351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101247506077181999304253801 75935629557886499478190351)
    ·
      refine ⟨113903444336829749217285527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75935629557886499478190351 113903444336829749217285527)
      ·
        refine ⟨170855166505244623825928291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113903444336829749217285527 170855166505244623825928291)
        ·
          refine ⟨256282749757866935738892437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170855166505244623825928291 256282749757866935738892437)
          ·
            refine ⟨12013253894900012612760583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 256282749757866935738892437 12013253894900012612760583)
            ·
              refine ⟨18019880842350018919140875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12013253894900012612760583 18019880842350018919140875)
              ·
                refine ⟨27029821263525028378711313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18019880842350018919140875 27029821263525028378711313)
                ·
                  refine ⟨20272365947643771284033485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27029821263525028378711313 20272365947643771284033485)
                  ·
                    refine ⟨7602137230366414231512557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20272365947643771284033485 7602137230366414231512557)
                    ·
                      refine ⟨2850801461387405336817209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7602137230366414231512557 2850801461387405336817209)
                      ·
                        rfl

theorem cell23_5551916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_5551916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551916 prefixEnd_5551916 := by exact prefixLift 5551916
  have htrace : WordTrace (prefixWord ++ tailWord_5551916) baseStart_5551916 baseEnd_5551916 := by
    simpa [prefixWord, tailWord_5551916, baseEnd_5551916] using wordTrace_append hprefix tailTrace_5551916
  have hstable : (prefixWord ++ tailWord_5551916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551916).length < 2 ^ (prefixWord ++ tailWord_5551916).sum := by decide
  have hdescent : baseEnd_5551916 < baseStart_5551916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551969 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_5551969 : Nat := 118140960795 + 5551969 * 2 ^ 59
def prefixEnd_5551969 : Nat := 4983230072969 + 3 ^ 40 * 5551969 * 2
def baseEnd_5551969 : Nat := 2850828675862093629454465

theorem tailTrace_5551969 : CollatzResearch.WordTrace tailWord_5551969 prefixEnd_5551969 2850828675862093629454465 := by
  unfold tailWord_5551969
  simp only [CollatzResearch.WordTrace]
  refine ⟨202496945223171988660186961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134997963482114659106791307 202496945223171988660186961)
  ·
    refine ⟨151872708917378991495140221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202496945223171988660186961 151872708917378991495140221)
    ·
      refine ⟨56952265844017121810677583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151872708917378991495140221 56952265844017121810677583)
      ·
        refine ⟨85428398766025682716016375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56952265844017121810677583 85428398766025682716016375)
        ·
          refine ⟨128142598149038524074024563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85428398766025682716016375 128142598149038524074024563)
          ·
            refine ⟨192213897223557786111036845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128142598149038524074024563 192213897223557786111036845)
            ·
              refine ⟨72080211458834169791638817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192213897223557786111036845 72080211458834169791638817)
              ·
                refine ⟨54060158594125627343729113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72080211458834169791638817 54060158594125627343729113)
                ·
                  refine ⟨40545118945594220507796835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54060158594125627343729113 40545118945594220507796835)
                  ·
                    refine ⟨60817678418391330761695253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40545118945594220507796835 60817678418391330761695253)
                    ·
                      refine ⟨2850828675862093629454465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60817678418391330761695253 2850828675862093629454465)
                      ·
                        rfl

theorem cell23_5551969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_5551969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551969 prefixEnd_5551969 := by exact prefixLift 5551969
  have htrace : WordTrace (prefixWord ++ tailWord_5551969) baseStart_5551969 baseEnd_5551969 := by
    simpa [prefixWord, tailWord_5551969, baseEnd_5551969] using wordTrace_append hprefix tailTrace_5551969
  have hstable : (prefixWord ++ tailWord_5551969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551969).length < 2 ^ (prefixWord ++ tailWord_5551969).sum := by decide
  have hdescent : baseEnd_5551969 < baseStart_5551969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5551976 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5551976 : Nat := 118140960795 + 5551976 * 2 ^ 59
def prefixEnd_5551976 : Nat := 4983230072969 + 3 ^ 40 * 5551976 * 2
def baseEnd_5551976 : Nat := 2850832270226675102066933

theorem tailTrace_5551976 : CollatzResearch.WordTrace tailWord_5551976 prefixEnd_5551976 2850832270226675102066933 := by
  unfold tailWord_5551976
  simp only [CollatzResearch.WordTrace]
  refine ⟨101248600267073314427845891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134998133689431085903794521 101248600267073314427845891)
  ·
    refine ⟨151872900400609971641768837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101248600267073314427845891 151872900400609971641768837)
    ·
      refine ⟨28476168825114369682831657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151872900400609971641768837 28476168825114369682831657)
      ·
        refine ⟨21357126618835777262123743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28476168825114369682831657 21357126618835777262123743)
        ·
          refine ⟨32035689928253665893185615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21357126618835777262123743 32035689928253665893185615)
          ·
            refine ⟨48053534892380498839778423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32035689928253665893185615 48053534892380498839778423)
            ·
              refine ⟨72080302338570748259667635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48053534892380498839778423 72080302338570748259667635)
              ·
                refine ⟨108120453507856122389501453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72080302338570748259667635 108120453507856122389501453)
                ·
                  refine ⟨40545170065446045896063045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108120453507856122389501453 40545170065446045896063045)
                  ·
                    refine ⟨7602219387271133605511821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40545170065446045896063045 7602219387271133605511821)
                    ·
                      refine ⟨2850832270226675102066933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7602219387271133605511821 2850832270226675102066933)
                      ·
                        rfl

theorem cell23_5551976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5551976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5551976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5551976 prefixEnd_5551976 := by exact prefixLift 5551976
  have htrace : WordTrace (prefixWord ++ tailWord_5551976) baseStart_5551976 baseEnd_5551976 := by
    simpa [prefixWord, tailWord_5551976, baseEnd_5551976] using wordTrace_append hprefix tailTrace_5551976
  have hstable : (prefixWord ++ tailWord_5551976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5551976).length < 2 ^ (prefixWord ++ tailWord_5551976).sum := by decide
  have hdescent : baseEnd_5551976 < baseStart_5551976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5551976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
