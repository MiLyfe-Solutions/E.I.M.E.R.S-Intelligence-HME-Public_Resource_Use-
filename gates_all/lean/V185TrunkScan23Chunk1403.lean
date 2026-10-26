import V185TrunkScan23Chunk1402

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8310542 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_8310542 : Nat := 118140960795 + 8310542 * 2 ^ 59
def prefixEnd_8310542 : Nat := 4983230072969 + 3 ^ 40 * 8310542 * 2
def baseEnd_8310542 : Nat := 474144727264147688878391

theorem tailTrace_8310542 : CollatzResearch.WordTrace tailWord_8310542 prefixEnd_8310542 474144727264147688878391 := by
  unfold tailWord_8310542
  simp only [CollatzResearch.WordTrace]
  refine ⟨37888796032291642052533735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202073578838888757613513253 37888796032291642052533735)
  ·
    refine ⟨56833194048437463078800603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37888796032291642052533735 56833194048437463078800603)
    ·
      refine ⟨85249791072656194618200905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56833194048437463078800603 85249791072656194618200905)
      ·
        refine ⟨63937343304492145963650679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85249791072656194618200905 63937343304492145963650679)
        ·
          refine ⟨95906014956738218945476019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63937343304492145963650679 95906014956738218945476019)
          ·
            refine ⟨143859022435107328418214029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95906014956738218945476019 143859022435107328418214029)
            ·
              refine ⟨53947133413165248156830261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143859022435107328418214029 53947133413165248156830261)
              ·
                refine ⟨5057543757484242014702837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53947133413165248156830261 5057543757484242014702837)
                ·
                  refine ⟨474144727264147688878391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5057543757484242014702837 474144727264147688878391)
                  ·
                    rfl

theorem cell23_8310542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_8310542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310542 prefixEnd_8310542 := by exact prefixLift 8310542
  have htrace : WordTrace (prefixWord ++ tailWord_8310542) baseStart_8310542 baseEnd_8310542 := by
    simpa [prefixWord, tailWord_8310542, baseEnd_8310542] using wordTrace_append hprefix tailTrace_8310542
  have hstable : (prefixWord ++ tailWord_8310542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310542).length < 2 ^ (prefixWord ++ tailWord_8310542).sum := by decide
  have hdescent : baseEnd_8310542 < baseStart_8310542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310575 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_8310575 : Nat := 118140960795 + 8310575 * 2 ^ 59
def prefixEnd_8310575 : Nat := 4983230072969 + 3 ^ 40 * 8310575 * 2
def baseEnd_8310575 : Nat := 4267319490238927570792867

theorem tailTrace_8310575 : CollatzResearch.WordTrace tailWord_8310575 prefixEnd_8310575 4267319490238927570792867 := by
  unfold tailWord_8310575
  simp only [CollatzResearch.WordTrace]
  refine ⟨303111571867213583056221179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202074381244809055370814119 303111571867213583056221179)
  ·
    refine ⟨454667357800820374584331769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303111571867213583056221179 454667357800820374584331769)
    ·
      refine ⟨341000518350615280938248827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454667357800820374584331769 341000518350615280938248827)
      ·
        refine ⟨511500777525922921407373241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341000518350615280938248827 511500777525922921407373241)
        ·
          refine ⟨383625583144442191055529931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511500777525922921407373241 383625583144442191055529931)
          ·
            refine ⟨575438374716663286583294897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383625583144442191055529931 575438374716663286583294897)
            ·
              refine ⟨431578781037497464937471173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575438374716663286583294897 431578781037497464937471173)
              ·
                refine ⟨80921021444530774675775845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431578781037497464937471173 80921021444530774675775845)
                ·
                  refine ⟨15172691520849520251707971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80921021444530774675775845 15172691520849520251707971)
                  ·
                    refine ⟨22759037281274280377561957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15172691520849520251707971 22759037281274280377561957)
                    ·
                      refine ⟨4267319490238927570792867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22759037281274280377561957 4267319490238927570792867)
                      ·
                        rfl

theorem cell23_8310575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_8310575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310575 prefixEnd_8310575 := by exact prefixLift 8310575
  have htrace : WordTrace (prefixWord ++ tailWord_8310575) baseStart_8310575 baseEnd_8310575 := by
    simpa [prefixWord, tailWord_8310575, baseEnd_8310575] using wordTrace_append hprefix tailTrace_8310575
  have hstable : (prefixWord ++ tailWord_8310575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310575).length < 2 ^ (prefixWord ++ tailWord_8310575).sum := by decide
  have hdescent : baseEnd_8310575 < baseStart_8310575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310632 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 6]
def baseStart_8310632 : Nat := 118140960795 + 8310632 * 2 ^ 59
def prefixEnd_8310632 : Nat := 4983230072969 + 3 ^ 40 * 8310632 * 2
def baseEnd_8310632 : Nat := 474149862070692649753345

theorem tailTrace_8310632 : CollatzResearch.WordTrace tailWord_8310632 prefixEnd_8310632 474149862070692649753345 := by
  unfold tailWord_8310632
  simp only [CollatzResearch.WordTrace]
  refine ⟨151556825414003540895523075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202075767218671387860697433 151556825414003540895523075)
  ·
    refine ⟨227335238121005311343284613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151556825414003540895523075 227335238121005311343284613)
    ·
      refine ⟨42625357147688495876865865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227335238121005311343284613 42625357147688495876865865)
      ·
        refine ⟨31969017860766371907649399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42625357147688495876865865 31969017860766371907649399)
        ·
          refine ⟨47953526791149557861474099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31969017860766371907649399 47953526791149557861474099)
          ·
            refine ⟨71930290186724336792211149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47953526791149557861474099 71930290186724336792211149)
            ·
              refine ⟨26973858820021626297079181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71930290186724336792211149 26973858820021626297079181)
              ·
                refine ⟨10115197057508109861404693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26973858820021626297079181 10115197057508109861404693)
                ·
                  refine ⟨474149862070692649753345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10115197057508109861404693 474149862070692649753345)
                  ·
                    rfl

theorem cell23_8310632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 6].length) (baseStart_8310632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310632 prefixEnd_8310632 := by exact prefixLift 8310632
  have htrace : WordTrace (prefixWord ++ tailWord_8310632) baseStart_8310632 baseEnd_8310632 := by
    simpa [prefixWord, tailWord_8310632, baseEnd_8310632] using wordTrace_append hprefix tailTrace_8310632
  have hstable : (prefixWord ++ tailWord_8310632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310632).length < 2 ^ (prefixWord ++ tailWord_8310632).sum := by decide
  have hdescent : baseEnd_8310632 < baseStart_8310632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310692 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_8310692 : Nat := 118140960795 + 8310692 * 2 ^ 59
def prefixEnd_8310692 : Nat := 4983230072969 + 3 ^ 40 * 8310692 * 2
def baseEnd_8310692 : Nat := 1422459855825167871009943

theorem tailTrace_8310692 : CollatzResearch.WordTrace tailWord_8310692 prefixEnd_8310692 1422459855825167871009943 := by
  unfold tailWord_8310692
  simp only [CollatzResearch.WordTrace]
  refine ⟨151557919603894856019115165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202077226138526474692153553 151557919603894856019115165)
  ·
    refine ⟨56834219851460571007168187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151557919603894856019115165 56834219851460571007168187)
    ·
      refine ⟨85251329777190856510752281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56834219851460571007168187 85251329777190856510752281)
      ·
        refine ⟨63938497332893142383064211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85251329777190856510752281 63938497332893142383064211)
        ·
          refine ⟨95907745999339713574596317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63938497332893142383064211 95907745999339713574596317)
          ·
            refine ⟨35965404749752392590473619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95907745999339713574596317 35965404749752392590473619)
            ·
              refine ⟨53948107124628588885710429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35965404749752392590473619 53948107124628588885710429)
              ·
                refine ⟨20230540171735720832141411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53948107124628588885710429 20230540171735720832141411)
                ·
                  refine ⟨30345810257603581248212117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20230540171735720832141411 30345810257603581248212117)
                  ·
                    refine ⟨1422459855825167871009943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30345810257603581248212117 1422459855825167871009943)
                    ·
                      rfl

theorem cell23_8310692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_8310692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310692 prefixEnd_8310692 := by exact prefixLift 8310692
  have htrace : WordTrace (prefixWord ++ tailWord_8310692) baseStart_8310692 baseEnd_8310692 := by
    simpa [prefixWord, tailWord_8310692, baseEnd_8310692] using wordTrace_append hprefix tailTrace_8310692
  have hstable : (prefixWord ++ tailWord_8310692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310692).length < 2 ^ (prefixWord ++ tailWord_8310692).sum := by decide
  have hdescent : baseEnd_8310692 < baseStart_8310692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310712 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_8310712 : Nat := 118140960795 + 8310712 * 2 ^ 59
def prefixEnd_8310712 : Nat := 4983230072969 + 3 ^ 40 * 8310712 * 2
def baseEnd_8310712 : Nat := 4267389837088593534779737

theorem tailTrace_8310712 : CollatzResearch.WordTrace tailWord_8310712 prefixEnd_8310712 4267389837088593534779737 := by
  unfold tailWord_8310712
  simp only [CollatzResearch.WordTrace]
  refine ⟨151558284333858627726979195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202077712445144836969305593 151558284333858627726979195)
  ·
    refine ⟨227337426500787941590468793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151558284333858627726979195 227337426500787941590468793)
    ·
      refine ⟨170503069875590956192851595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227337426500787941590468793 170503069875590956192851595)
      ·
        refine ⟨255754604813386434289277393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170503069875590956192851595 255754604813386434289277393)
        ·
          refine ⟨191815953610039825716958045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255754604813386434289277393 191815953610039825716958045)
          ·
            refine ⟨71930982603764934643859267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191815953610039825716958045 71930982603764934643859267)
            ·
              refine ⟨107896473905647401965788901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71930982603764934643859267 107896473905647401965788901)
              ·
                refine ⟨20230588857308887868585419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107896473905647401965788901 20230588857308887868585419)
                ·
                  refine ⟨30345883285963331802878129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20230588857308887868585419 30345883285963331802878129)
                  ·
                    refine ⟨22759412464472498852158597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30345883285963331802878129 22759412464472498852158597)
                    ·
                      refine ⟨4267389837088593534779737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22759412464472498852158597 4267389837088593534779737)
                      ·
                        rfl

theorem cell23_8310712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_8310712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310712 prefixEnd_8310712 := by exact prefixLift 8310712
  have htrace : WordTrace (prefixWord ++ tailWord_8310712) baseStart_8310712 baseEnd_8310712 := by
    simpa [prefixWord, tailWord_8310712, baseEnd_8310712] using wordTrace_append hprefix tailTrace_8310712
  have hstable : (prefixWord ++ tailWord_8310712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310712).length < 2 ^ (prefixWord ++ tailWord_8310712).sum := by decide
  have hdescent : baseEnd_8310712 < baseStart_8310712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310719 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 3]
def baseStart_8310719 : Nat := 118140960795 + 8310719 * 2 ^ 59
def prefixEnd_8310719 : Nat := 4983230072969 + 3 ^ 40 * 8310719 * 2
def baseEnd_8310719 : Nat := 4267393431453175007392205

theorem tailTrace_8310719 : CollatzResearch.WordTrace tailWord_8310719 prefixEnd_8310719 4267393431453175007392205 := by
  unfold tailWord_8310719
  simp only [CollatzResearch.WordTrace]
  refine ⟨303116823978691895649463211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202077882652461263766308807 303116823978691895649463211)
  ·
    refine ⟨454675235968037843474194817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303116823978691895649463211 454675235968037843474194817)
    ·
      refine ⟨341006426976028382605646113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454675235968037843474194817 341006426976028382605646113)
      ·
        refine ⟨255754820232021286954234585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341006426976028382605646113 255754820232021286954234585)
        ·
          refine ⟨191816115174015965215675939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255754820232021286954234585 191816115174015965215675939)
          ·
            refine ⟨287724172761023947823513909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191816115174015965215675939 287724172761023947823513909)
            ·
              refine ⟨26974141196345995108454429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287724172761023947823513909 26974141196345995108454429)
              ·
                refine ⟨10115302948629748165670411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26974141196345995108454429 10115302948629748165670411)
                ·
                  refine ⟨15172954422944622248505617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115302948629748165670411 15172954422944622248505617)
                  ·
                    refine ⟨11379715817208466686379213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15172954422944622248505617 11379715817208466686379213)
                    ·
                      refine ⟨4267393431453175007392205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11379715817208466686379213 4267393431453175007392205)
                      ·
                        rfl

theorem cell23_8310719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_8310719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310719 prefixEnd_8310719 := by exact prefixLift 8310719
  have htrace : WordTrace (prefixWord ++ tailWord_8310719) baseStart_8310719 baseEnd_8310719 := by
    simpa [prefixWord, tailWord_8310719, baseEnd_8310719] using wordTrace_append hprefix tailTrace_8310719
  have hstable : (prefixWord ++ tailWord_8310719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310719).length < 2 ^ (prefixWord ++ tailWord_8310719).sum := by decide
  have hdescent : baseEnd_8310719 < baseStart_8310719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310746 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_8310746 : Nat := 118140960795 + 8310746 * 2 ^ 59
def prefixEnd_8310746 : Nat := 4983230072969 + 3 ^ 40 * 8310746 * 2
def baseEnd_8310746 : Nat := 4267407295430846401754581

theorem tailTrace_8310746 : CollatzResearch.WordTrace tailWord_8310746 prefixEnd_8310746 4267407295430846401754581 := by
  unfold tailWord_8310746
  simp only [CollatzResearch.WordTrace]
  refine ⟨75779452187398519815174023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202078539166396052840464061 75779452187398519815174023)
  ·
    refine ⟨113669178281097779722761035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75779452187398519815174023 113669178281097779722761035)
    ·
      refine ⟨170503767421646669584141553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113669178281097779722761035 170503767421646669584141553)
      ·
        refine ⟨127877825566235002188106165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170503767421646669584141553 127877825566235002188106165)
        ·
          refine ⟨11988546146834531455134953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127877825566235002188106165 11988546146834531455134953)
          ·
            refine ⟨8991409610125898591351215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11988546146834531455134953 8991409610125898591351215)
            ·
              refine ⟨13487114415188847887026823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991409610125898591351215 13487114415188847887026823)
              ·
                refine ⟨20230671622783271830540235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13487114415188847887026823 20230671622783271830540235)
                ·
                  refine ⟨30346007434174907745810353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20230671622783271830540235 30346007434174907745810353)
                  ·
                    refine ⟨22759505575631180809357765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30346007434174907745810353 22759505575631180809357765)
                    ·
                      refine ⟨4267407295430846401754581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22759505575631180809357765 4267407295430846401754581)
                      ·
                        rfl

theorem cell23_8310746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_8310746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310746 prefixEnd_8310746 := by exact prefixLift 8310746
  have htrace : WordTrace (prefixWord ++ tailWord_8310746) baseStart_8310746 baseEnd_8310746 := by
    simpa [prefixWord, tailWord_8310746, baseEnd_8310746] using wordTrace_append hprefix tailTrace_8310746
  have hstable : (prefixWord ++ tailWord_8310746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310746).length < 2 ^ (prefixWord ++ tailWord_8310746).sum := by decide
  have hdescent : baseEnd_8310746 < baseStart_8310746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310762 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_8310762 : Nat := 118140960795 + 8310762 * 2 ^ 59
def prefixEnd_8310762 : Nat := 4983230072969 + 3 ^ 40 * 8310762 * 2
def baseEnd_8310762 : Nat := 4267415511121318339154507

theorem tailTrace_8310762 : CollatzResearch.WordTrace tailWord_8310762 prefixEnd_8310762 4267415511121318339154507 := by
  unfold tailWord_8310762
  simp only [CollatzResearch.WordTrace]
  refine ⟨75779598079384028498319635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202078928211690742662185693 75779598079384028498319635)
  ·
    refine ⟨113669397119076042747479453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75779598079384028498319635 113669397119076042747479453)
    ·
      refine ⟨42626023919653516030304795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113669397119076042747479453 42626023919653516030304795)
      ·
        refine ⟨63939035879480274045457193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42626023919653516030304795 63939035879480274045457193)
        ·
          refine ⟨47954276909610205534092895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63939035879480274045457193 47954276909610205534092895)
          ·
            refine ⟨71931415364415308301139343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47954276909610205534092895 71931415364415308301139343)
            ·
              refine ⟨107897123046622962451709015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71931415364415308301139343 107897123046622962451709015)
              ·
                refine ⟨161845684569934443677563523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107897123046622962451709015 161845684569934443677563523)
                ·
                  refine ⟨242768526854901665516345285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161845684569934443677563523 242768526854901665516345285)
                  ·
                    refine ⟨45519098785294062284314741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242768526854901665516345285 45519098785294062284314741)
                    ·
                      refine ⟨4267415511121318339154507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45519098785294062284314741 4267415511121318339154507)
                      ·
                        rfl

theorem cell23_8310762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_8310762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310762 prefixEnd_8310762 := by exact prefixLift 8310762
  have htrace : WordTrace (prefixWord ++ tailWord_8310762) baseStart_8310762 baseEnd_8310762 := by
    simpa [prefixWord, tailWord_8310762, baseEnd_8310762] using wordTrace_append hprefix tailTrace_8310762
  have hstable : (prefixWord ++ tailWord_8310762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310762).length < 2 ^ (prefixWord ++ tailWord_8310762).sum := by decide
  have hdescent : baseEnd_8310762 < baseStart_8310762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310766 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_8310766 : Nat := 118140960795 + 8310766 * 2 ^ 59
def prefixEnd_8310766 : Nat := 4983230072969 + 3 ^ 40 * 8310766 * 2
def baseEnd_8310766 : Nat := 4267417565043936323504489

theorem tailTrace_8310766 : CollatzResearch.WordTrace tailWord_8310766 prefixEnd_8310766 4267417565043936323504489 := by
  unfold tailWord_8310766
  simp only [CollatzResearch.WordTrace]
  refine ⟨37889817276190202834553019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202079025473014415117616101 37889817276190202834553019)
  ·
    refine ⟨56834725914285304251829529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37889817276190202834553019 56834725914285304251829529)
    ·
      refine ⟨42626044435713978188872147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56834725914285304251829529 42626044435713978188872147)
      ·
        refine ⟨63939066653570967283308221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42626044435713978188872147 63939066653570967283308221)
        ·
          refine ⟨23977149995089112731240583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63939066653570967283308221 23977149995089112731240583)
          ·
            refine ⟨35965724992633669096860875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23977149995089112731240583 35965724992633669096860875)
            ·
              refine ⟨53948587488950503645291313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35965724992633669096860875 53948587488950503645291313)
              ·
                refine ⟨40461440616712877733968485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53948587488950503645291313 40461440616712877733968485)
                ·
                  refine ⟨7586520115633664575119091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40461440616712877733968485 7586520115633664575119091)
                  ·
                    refine ⟨11379780173450496862678637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7586520115633664575119091 11379780173450496862678637)
                    ·
                      refine ⟨4267417565043936323504489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11379780173450496862678637 4267417565043936323504489)
                      ·
                        rfl

theorem cell23_8310766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_8310766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310766 prefixEnd_8310766 := by exact prefixLift 8310766
  have htrace : WordTrace (prefixWord ++ tailWord_8310766) baseStart_8310766 baseEnd_8310766 := by
    simpa [prefixWord, tailWord_8310766, baseEnd_8310766] using wordTrace_append hprefix tailTrace_8310766
  have hstable : (prefixWord ++ tailWord_8310766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310766).length < 2 ^ (prefixWord ++ tailWord_8310766).sum := by decide
  have hdescent : baseEnd_8310766 < baseStart_8310766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310776 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 1, 3, 2]
def baseStart_8310776 : Nat := 118140960795 + 8310776 * 2 ^ 59
def prefixEnd_8310776 : Nat := 4983230072969 + 3 ^ 40 * 8310776 * 2
def baseEnd_8310776 : Nat := 4267422699850481284379443

theorem tailTrace_8310776 : CollatzResearch.WordTrace tailWord_8310776 prefixEnd_8310776 4267422699850481284379443 := by
  unfold tailWord_8310776
  simp only [CollatzResearch.WordTrace]
  refine ⟨151559451469742697192144091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202079268626323596256192121 151559451469742697192144091)
  ·
    refine ⟨227339177204614045788216137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151559451469742697192144091 227339177204614045788216137)
    ·
      refine ⟨170504382903460534341162103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227339177204614045788216137 170504382903460534341162103)
      ·
        refine ⟨255756574355190801511743155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170504382903460534341162103 255756574355190801511743155)
        ·
          refine ⟨383634861532786202267614733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255756574355190801511743155 383634861532786202267614733)
          ·
            refine ⟨143863073074794825850355525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383634861532786202267614733 143863073074794825850355525)
            ·
              refine ⟨26974326201524029846941661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143863073074794825850355525 26974326201524029846941661)
              ·
                refine ⟨10115372325571511192603123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26974326201524029846941661 10115372325571511192603123)
                ·
                  refine ⟨15173058488357266788904685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115372325571511192603123 15173058488357266788904685)
                  ·
                    refine ⟨5689896933133975045839257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15173058488357266788904685 5689896933133975045839257)
                    ·
                      refine ⟨4267422699850481284379443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689896933133975045839257 4267422699850481284379443)
                      ·
                        rfl

theorem cell23_8310776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_8310776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310776 prefixEnd_8310776 := by exact prefixLift 8310776
  have htrace : WordTrace (prefixWord ++ tailWord_8310776) baseStart_8310776 baseEnd_8310776 := by
    simpa [prefixWord, tailWord_8310776, baseEnd_8310776] using wordTrace_append hprefix tailTrace_8310776
  have hstable : (prefixWord ++ tailWord_8310776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310776).length < 2 ^ (prefixWord ++ tailWord_8310776).sum := by decide
  have hdescent : baseEnd_8310776 < baseStart_8310776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310790 : List Nat := [6, 2, 1, 2, 1, 1, 2, 8]
def baseStart_8310790 : Nat := 118140960795 + 8310790 * 2 ^ 59
def prefixEnd_8310790 : Nat := 4983230072969 + 3 ^ 40 * 8310790 * 2
def baseEnd_8310790 : Nat := 158052958836283119614977

theorem tailTrace_8310790 : CollatzResearch.WordTrace tailWord_8310790 prefixEnd_8310790 158052958836283119614977 := by
  unfold tailWord_8310790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472481673794833586728057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202079609040956449850198549 9472481673794833586728057)
  ·
    refine ⟨7104361255346125190046043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9472481673794833586728057 7104361255346125190046043)
    ·
      refine ⟨10656541883019187785069065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104361255346125190046043 10656541883019187785069065)
      ·
        refine ⟨7992406412264390838801799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10656541883019187785069065 7992406412264390838801799)
        ·
          refine ⟨11988609618396586258202699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7992406412264390838801799 11988609618396586258202699)
          ·
            refine ⟨17982914427594879387304049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988609618396586258202699 17982914427594879387304049)
            ·
              refine ⟨13487185820696159540478037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17982914427594879387304049 13487185820696159540478037)
              ·
                refine ⟨158052958836283119614977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13487185820696159540478037 158052958836283119614977)
                ·
                  rfl

theorem cell23_8310790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_8310790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310790 prefixEnd_8310790 := by exact prefixLift 8310790
  have htrace : WordTrace (prefixWord ++ tailWord_8310790) baseStart_8310790 baseEnd_8310790 := by
    simpa [prefixWord, tailWord_8310790, baseEnd_8310790] using wordTrace_append hprefix tailTrace_8310790
  have hstable : (prefixWord ++ tailWord_8310790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310790).length < 2 ^ (prefixWord ++ tailWord_8310790).sum := by decide
  have hdescent : baseEnd_8310790 < baseStart_8310790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310792 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_8310792 : Nat := 118140960795 + 8310792 * 2 ^ 59
def prefixEnd_8310792 : Nat := 4983230072969 + 3 ^ 40 * 8310792 * 2
def baseEnd_8310792 : Nat := 4267430915540953221779369

theorem tailTrace_8310792 : CollatzResearch.WordTrace tailWord_8310792 prefixEnd_8310792 4267430915540953221779369 := by
  unfold tailWord_8310792
  simp only [CollatzResearch.WordTrace]
  refine ⟨151559743253713714558435315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202079657671618286077913753 151559743253713714558435315)
  ·
    refine ⟨227339614880570571837652973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151559743253713714558435315 227339614880570571837652973)
    ·
      refine ⟨85252355580213964439119865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227339614880570571837652973 85252355580213964439119865)
      ·
        refine ⟨63939266685160473329339899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85252355580213964439119865 63939266685160473329339899)
        ·
          refine ⟨95908900027740709994009849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63939266685160473329339899 95908900027740709994009849)
          ·
            refine ⟨71931675020805532495507387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95908900027740709994009849 71931675020805532495507387)
            ·
              refine ⟨107897512531208298743261081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71931675020805532495507387 107897512531208298743261081)
              ·
                refine ⟨80923134398406224057445811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107897512531208298743261081 80923134398406224057445811)
                ·
                  refine ⟨121384701597609336086168717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80923134398406224057445811 121384701597609336086168717)
                  ·
                    refine ⟨45519263099103501032313269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121384701597609336086168717 45519263099103501032313269)
                    ·
                      refine ⟨4267430915540953221779369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45519263099103501032313269 4267430915540953221779369)
                      ·
                        rfl

theorem cell23_8310792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_8310792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310792 prefixEnd_8310792 := by exact prefixLift 8310792
  have htrace : WordTrace (prefixWord ++ tailWord_8310792) baseStart_8310792 baseEnd_8310792 := by
    simpa [prefixWord, tailWord_8310792, baseEnd_8310792] using wordTrace_append hprefix tailTrace_8310792
  have hstable : (prefixWord ++ tailWord_8310792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310792).length < 2 ^ (prefixWord ++ tailWord_8310792).sum := by decide
  have hdescent : baseEnd_8310792 < baseStart_8310792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310840 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 2, 2, 2]
def baseStart_8310840 : Nat := 118140960795 + 8310840 * 2 ^ 59
def prefixEnd_8310840 : Nat := 4983230072969 + 3 ^ 40 * 8310840 * 2
def baseEnd_8310840 : Nat := 4267455562612369033979149

theorem tailTrace_8310840 : CollatzResearch.WordTrace tailWord_8310840 prefixEnd_8310840 4267455562612369033979149 := by
  unfold tailWord_8310840
  simp only [CollatzResearch.WordTrace]
  refine ⟨151560618605626766657308987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202080824807502355543078649 151560618605626766657308987)
  ·
    refine ⟨227340927908440149985963481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151560618605626766657308987 227340927908440149985963481)
    ·
      refine ⟨170505695931330112489472611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227340927908440149985963481 170505695931330112489472611)
      ·
        refine ⟨255758543896995168734208917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170505695931330112489472611 255758543896995168734208917)
        ·
          refine ⟨11988681745171648534416043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255758543896995168734208917 11988681745171648534416043)
          ·
            refine ⟨17983022617757472801624065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11988681745171648534416043 17983022617757472801624065)
            ·
              refine ⟨13487266963318104601218049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17983022617757472801624065 13487266963318104601218049)
              ·
                refine ⟨10115450222488578450913537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13487266963318104601218049 10115450222488578450913537)
                ·
                  refine ⟨7586587666866433838185153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115450222488578450913537 7586587666866433838185153)
                  ·
                    refine ⟨5689940750149825378638865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586587666866433838185153 5689940750149825378638865)
                    ·
                      refine ⟨4267455562612369033979149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689940750149825378638865 4267455562612369033979149)
                      ·
                        rfl

theorem cell23_8310840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_8310840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310840 prefixEnd_8310840 := by exact prefixLift 8310840
  have htrace : WordTrace (prefixWord ++ tailWord_8310840) baseStart_8310840 baseEnd_8310840 := by
    simpa [prefixWord, tailWord_8310840, baseEnd_8310840] using wordTrace_append hprefix tailTrace_8310840
  have hstable : (prefixWord ++ tailWord_8310840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310840).length < 2 ^ (prefixWord ++ tailWord_8310840).sum := by decide
  have hdescent : baseEnd_8310840 < baseStart_8310840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310842 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_8310842 : Nat := 118140960795 + 8310842 * 2 ^ 59
def prefixEnd_8310842 : Nat := 4983230072969 + 3 ^ 40 * 8310842 * 2
def baseEnd_8310842 : Nat := 1422485529857892675384713

theorem tailTrace_8310842 : CollatzResearch.WordTrace tailWord_8310842 prefixEnd_8310842 1422485529857892675384713 := by
  unfold tailWord_8310842
  simp only [CollatzResearch.WordTrace]
  refine ⟨75780327539311571914047695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202080873438164191770793853 75780327539311571914047695)
  ·
    refine ⟨113670491308967357871071543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75780327539311571914047695 113670491308967357871071543)
    ·
      refine ⟨170505736963451036806607315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113670491308967357871071543 170505736963451036806607315)
      ·
        refine ⟨255758605445176555209910973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170505736963451036806607315 255758605445176555209910973)
        ·
          refine ⟨95909477041941208203716615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255758605445176555209910973 95909477041941208203716615)
          ·
            refine ⟨143864215562911812305574923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95909477041941208203716615 143864215562911812305574923)
            ·
              refine ⟨215796323344367718458362385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143864215562911812305574923 215796323344367718458362385)
              ·
                refine ⟨161847242508275788843771789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215796323344367718458362385 161847242508275788843771789)
                ·
                  refine ⟨60692715940603420816414421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161847242508275788843771789 60692715940603420816414421)
                  ·
                    refine ⟨1422485529857892675384713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60692715940603420816414421 1422485529857892675384713)
                    ·
                      rfl

theorem cell23_8310842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_8310842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310842 prefixEnd_8310842 := by exact prefixLift 8310842
  have htrace : WordTrace (prefixWord ++ tailWord_8310842) baseStart_8310842 baseEnd_8310842 := by
    simpa [prefixWord, tailWord_8310842, baseEnd_8310842] using wordTrace_append hprefix tailTrace_8310842
  have hstable : (prefixWord ++ tailWord_8310842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310842).length < 2 ^ (prefixWord ++ tailWord_8310842).sum := by decide
  have hdescent : baseEnd_8310842 < baseStart_8310842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310876 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_8310876 : Nat := 118140960795 + 8310876 * 2 ^ 59
def prefixEnd_8310876 : Nat := 4983230072969 + 3 ^ 40 * 8310876 * 2
def baseEnd_8310876 : Nat := 1422491349305310297709661

theorem tailTrace_8310876 : CollatzResearch.WordTrace tailWord_8310876 prefixEnd_8310876 1422491349305310297709661 := by
  unfold tailWord_8310876
  simp only [CollatzResearch.WordTrace]
  refine ⟨151561275119561555731464241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202081700159415407641952321 151561275119561555731464241)
  ·
    refine ⟨113670956339671166798598181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151561275119561555731464241 113670956339671166798598181)
    ·
      refine ⟨21313304313688343774737159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113670956339671166798598181 21313304313688343774737159)
      ·
        refine ⟨31969956470532515662105739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21313304313688343774737159 31969956470532515662105739)
        ·
          refine ⟨47954934705798773493158609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31969956470532515662105739 47954934705798773493158609)
          ·
            refine ⟨35966201029349080119868957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47954934705798773493158609 35966201029349080119868957)
            ·
              refine ⟨13487325386005905044950859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35966201029349080119868957 13487325386005905044950859)
              ·
                refine ⟨20230988079008857567426289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13487325386005905044950859 20230988079008857567426289)
                ·
                  refine ⟨15173241059256643175569717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20230988079008857567426289 15173241059256643175569717)
                  ·
                    refine ⟨1422491349305310297709661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15173241059256643175569717 1422491349305310297709661)
                    ·
                      rfl

theorem cell23_8310876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_8310876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310876 prefixEnd_8310876 := by exact prefixLift 8310876
  have htrace : WordTrace (prefixWord ++ tailWord_8310876) baseStart_8310876 baseEnd_8310876 := by
    simpa [prefixWord, tailWord_8310876, baseEnd_8310876] using wordTrace_append hprefix tailTrace_8310876
  have hstable : (prefixWord ++ tailWord_8310876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310876).length < 2 ^ (prefixWord ++ tailWord_8310876).sum := by decide
  have hdescent : baseEnd_8310876 < baseStart_8310876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310879 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_8310879 : Nat := 118140960795 + 8310879 * 2 ^ 59
def prefixEnd_8310879 : Nat := 4983230072969 + 3 ^ 40 * 8310879 * 2
def baseEnd_8310879 : Nat := 4267475588357894381391469

theorem tailTrace_8310879 : CollatzResearch.WordTrace tailWord_8310879 prefixEnd_8310879 4267475588357894381391469 := by
  unfold tailWord_8310879
  simp only [CollatzResearch.WordTrace]
  refine ⟨303122659658112242975287691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202081773105408161983525127 303122659658112242975287691)
  ·
    refine ⟨454683989487168364462931537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303122659658112242975287691 454683989487168364462931537)
    ·
      refine ⟨341012992115376273347198653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454683989487168364462931537 341012992115376273347198653)
      ·
        refine ⟨127879872043266102505199495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341012992115376273347198653 127879872043266102505199495)
        ·
          refine ⟨191819808064899153757799243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127879872043266102505199495 191819808064899153757799243)
          ·
            refine ⟨287729712097348730636698865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191819808064899153757799243 287729712097348730636698865)
            ·
              refine ⟨215797284073011547977524149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287729712097348730636698865 215797284073011547977524149)
              ·
                refine ⟨20230995381844832622892889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215797284073011547977524149 20230995381844832622892889)
                ·
                  refine ⟨15173246536383624467169667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20230995381844832622892889 15173246536383624467169667)
                  ·
                    refine ⟨22759869804575436700754501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15173246536383624467169667 22759869804575436700754501)
                    ·
                      refine ⟨4267475588357894381391469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22759869804575436700754501 4267475588357894381391469)
                      ·
                        rfl

theorem cell23_8310879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_8310879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310879 prefixEnd_8310879 := by exact prefixLift 8310879
  have htrace : WordTrace (prefixWord ++ tailWord_8310879) baseStart_8310879 baseEnd_8310879 := by
    simpa [prefixWord, tailWord_8310879, baseEnd_8310879] using wordTrace_append hprefix tailTrace_8310879
  have hstable : (prefixWord ++ tailWord_8310879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310879).length < 2 ^ (prefixWord ++ tailWord_8310879).sum := by decide
  have hdescent : baseEnd_8310879 < baseStart_8310879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310889 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 5, 4]
def baseStart_8310889 : Nat := 118140960795 + 8310889 * 2 ^ 59
def prefixEnd_8310889 : Nat := 4983230072969 + 3 ^ 40 * 8310889 * 2
def baseEnd_8310889 : Nat := 1422493574388146447422141

theorem tailTrace_8310889 : CollatzResearch.WordTrace tailWord_8310889 prefixEnd_8310889 1422493574388146447422141 := by
  unfold tailWord_8310889
  simp only [CollatzResearch.WordTrace]
  refine ⟨303123024388076014683151721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202082016258717343122101147 303123024388076014683151721)
  ·
    refine ⟨227342268291057011012363791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303123024388076014683151721 227342268291057011012363791)
    ·
      refine ⟨341013402436585516518545687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227342268291057011012363791 341013402436585516518545687)
      ·
        refine ⟨511520103654878274777818531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341013402436585516518545687 511520103654878274777818531)
        ·
          refine ⟨767280155482317412166727797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511520103654878274777818531 767280155482317412166727797)
          ·
            refine ⟨71932514576467257390630731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 767280155482317412166727797 71932514576467257390630731)
            ·
              refine ⟨107898771864700886085946097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71932514576467257390630731 107898771864700886085946097)
              ·
                refine ⟨80924078898525664564459573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107898771864700886085946097 80924078898525664564459573)
                ·
                  refine ⟨7586632396736781052918085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80924078898525664564459573 7586632396736781052918085)
                  ·
                    refine ⟨1422493574388146447422141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586632396736781052918085 1422493574388146447422141)
                    ·
                      rfl

theorem cell23_8310889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_8310889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310889 prefixEnd_8310889 := by exact prefixLift 8310889
  have htrace : WordTrace (prefixWord ++ tailWord_8310889) baseStart_8310889 baseEnd_8310889 := by
    simpa [prefixWord, tailWord_8310889, baseEnd_8310889] using wordTrace_append hprefix tailTrace_8310889
  have hstable : (prefixWord ++ tailWord_8310889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310889).length < 2 ^ (prefixWord ++ tailWord_8310889).sum := by decide
  have hdescent : baseEnd_8310889 < baseStart_8310889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310896 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 2, 4, 2]
def baseStart_8310896 : Nat := 118140960795 + 8310896 * 2 ^ 59
def prefixEnd_8310896 : Nat := 4983230072969 + 3 ^ 40 * 8310896 * 2
def baseEnd_8310896 : Nat := 4267484317529020814878891

theorem tailTrace_8310896 : CollatzResearch.WordTrace tailWord_8310896 prefixEnd_8310896 4267484317529020814878891 := by
  unfold tailWord_8310896
  simp only [CollatzResearch.WordTrace]
  refine ⟨151561639849525327439328271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202082186466033769919104361 151561639849525327439328271)
  ·
    refine ⟨227342459774287991158992407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151561639849525327439328271 227342459774287991158992407)
    ·
      refine ⟨341013689661431986738488611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227342459774287991158992407 341013689661431986738488611)
      ·
        refine ⟨511520534492147980107732917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341013689661431986738488611 511520534492147980107732917)
        ·
          refine ⟨47955050108638873135099961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 511520534492147980107732917 47955050108638873135099961)
          ·
            refine ⟨35966287581479154851324971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47955050108638873135099961 35966287581479154851324971)
            ·
              refine ⟨53949431372218732276987457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35966287581479154851324971 53949431372218732276987457)
              ·
                refine ⟨40462073529164049207740593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53949431372218732276987457 40462073529164049207740593)
                ·
                  refine ⟨30346555146873036905805445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40462073529164049207740593 30346555146873036905805445)
                  ·
                    refine ⟨5689979090038694419838521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30346555146873036905805445 5689979090038694419838521)
                    ·
                      refine ⟨4267484317529020814878891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5689979090038694419838521 4267484317529020814878891)
                      ·
                        rfl

theorem cell23_8310896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 4, 2].length) (baseStart_8310896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310896 prefixEnd_8310896 := by exact prefixLift 8310896
  have htrace : WordTrace (prefixWord ++ tailWord_8310896) baseStart_8310896 baseEnd_8310896 := by
    simpa [prefixWord, tailWord_8310896, baseEnd_8310896] using wordTrace_append hprefix tailTrace_8310896
  have hstable : (prefixWord ++ tailWord_8310896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310896).length < 2 ^ (prefixWord ++ tailWord_8310896).sum := by decide
  have hdescent : baseEnd_8310896 < baseStart_8310896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310919 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 6]
def baseStart_8310919 : Nat := 118140960795 + 8310919 * 2 ^ 59
def prefixEnd_8310919 : Nat := 4983230072969 + 3 ^ 40 * 8310919 * 2
def baseEnd_8310919 : Nat := 474166236398230469432365

theorem tailTrace_8310919 : CollatzResearch.WordTrace tailWord_8310919 prefixEnd_8310919 474166236398230469432365 := by
  unfold tailWord_8310919
  simp only [CollatzResearch.WordTrace]
  refine ⟨303124118577967329806743811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202082745718644886537829207 303124118577967329806743811)
  ·
    refine ⟨454686177866950994710115717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303124118577967329806743811 454686177866950994710115717)
    ·
      refine ⟨85253658350053311508146697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454686177866950994710115717 85253658350053311508146697)
      ·
        refine ⟨63940243762539983631110023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85253658350053311508146697 63940243762539983631110023)
        ·
          refine ⟨95910365643809975446665035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63940243762539983631110023 95910365643809975446665035)
          ·
            refine ⟨143865548465714963169997553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95910365643809975446665035 143865548465714963169997553)
            ·
              refine ⟨107899161349286222377498165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143865548465714963169997553 107899161349286222377498165)
              ·
                refine ⟨10115546376495583347890453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107899161349286222377498165 10115546376495583347890453)
                ·
                  refine ⟨474166236398230469432365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10115546376495583347890453 474166236398230469432365)
                  ·
                    rfl

theorem cell23_8310919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 6].length) (baseStart_8310919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310919 prefixEnd_8310919 := by exact prefixLift 8310919
  have htrace : WordTrace (prefixWord ++ tailWord_8310919) baseStart_8310919 baseEnd_8310919 := by
    simpa [prefixWord, tailWord_8310919, baseEnd_8310919] using wordTrace_append hprefix tailTrace_8310919
  have hstable : (prefixWord ++ tailWord_8310919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310919).length < 2 ^ (prefixWord ++ tailWord_8310919).sum := by decide
  have hdescent : baseEnd_8310919 < baseStart_8310919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310957 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_8310957 : Nat := 118140960795 + 8310957 * 2 ^ 59
def prefixEnd_8310957 : Nat := 4983230072969 + 3 ^ 40 * 8310957 * 2
def baseEnd_8310957 : Nat := 1422505213282981692072037

theorem tailTrace_8310957 : CollatzResearch.WordTrace tailWord_8310957 prefixEnd_8310957 1422505213282981692072037 := by
  unfold tailWord_8310957
  simp only [CollatzResearch.WordTrace]
  refine ⟨303125504551829662296627125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202083669701219774864418083 303125504551829662296627125)
  ·
    refine ⟨28418016051734030840308793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303125504551829662296627125 28418016051734030840308793)
    ·
      refine ⟨21313512038800523130231595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28418016051734030840308793 21313512038800523130231595)
      ·
        refine ⟨31970268058200784695347393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21313512038800523130231595 31970268058200784695347393)
        ·
          refine ⟨23977701043650588521510545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31970268058200784695347393 23977701043650588521510545)
          ·
            refine ⟨17983275782737941391132909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23977701043650588521510545 17983275782737941391132909)
            ·
              refine ⟨6743728418526728021674841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17983275782737941391132909 6743728418526728021674841)
              ·
                refine ⟨5057796313895046016256131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743728418526728021674841 5057796313895046016256131)
                ·
                  refine ⟨7586694470842569024384197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5057796313895046016256131 7586694470842569024384197)
                  ·
                    refine ⟨1422505213282981692072037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586694470842569024384197 1422505213282981692072037)
                    ·
                      rfl

theorem cell23_8310957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_8310957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310957 prefixEnd_8310957 := by exact prefixLift 8310957
  have htrace : WordTrace (prefixWord ++ tailWord_8310957) baseStart_8310957 baseEnd_8310957 := by
    simpa [prefixWord, tailWord_8310957, baseEnd_8310957] using wordTrace_append hprefix tailTrace_8310957
  have hstable : (prefixWord ++ tailWord_8310957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310957).length < 2 ^ (prefixWord ++ tailWord_8310957).sum := by decide
  have hdescent : baseEnd_8310957 < baseStart_8310957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310986 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_8310986 : Nat := 118140960795 + 8310986 * 2 ^ 59
def prefixEnd_8310986 : Nat := 4983230072969 + 3 ^ 40 * 8310986 * 2
def baseEnd_8310986 : Nat := 4267530530787925462753477

theorem tailTrace_8310986 : CollatzResearch.WordTrace tailWord_8310986 prefixEnd_8310986 4267530530787925462753477 := by
  unfold tailWord_8310986
  simp only [CollatzResearch.WordTrace]
  refine ⟨75781640567181150062358203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202084374845816400166288541 75781640567181150062358203)
  ·
    refine ⟨113672460850771725093537305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75781640567181150062358203 113672460850771725093537305)
    ·
      refine ⟨85254345638078793820152979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113672460850771725093537305 85254345638078793820152979)
      ·
        refine ⟨127881518457118190730229469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85254345638078793820152979 127881518457118190730229469)
        ·
          refine ⟨47955569421419321523836051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127881518457118190730229469 47955569421419321523836051)
          ·
            refine ⟨71933354132128982285754077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47955569421419321523836051 71933354132128982285754077)
            ·
              refine ⟨26975007799548368357157779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71933354132128982285754077 26975007799548368357157779)
              ·
                refine ⟨40462511699322552535736669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26975007799548368357157779 40462511699322552535736669)
                ·
                  refine ⟨15173441887245957200901251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40462511699322552535736669 15173441887245957200901251)
                  ·
                    refine ⟨22760162830868935801351877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15173441887245957200901251 22760162830868935801351877)
                    ·
                      refine ⟨4267530530787925462753477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22760162830868935801351877 4267530530787925462753477)
                      ·
                        rfl

theorem cell23_8310986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_8310986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310986 prefixEnd_8310986 := by exact prefixLift 8310986
  have htrace : WordTrace (prefixWord ++ tailWord_8310986) baseStart_8310986 baseEnd_8310986 := by
    simpa [prefixWord, tailWord_8310986, baseEnd_8310986] using wordTrace_append hprefix tailTrace_8310986
  have hstable : (prefixWord ++ tailWord_8310986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310986).length < 2 ^ (prefixWord ++ tailWord_8310986).sum := by decide
  have hdescent : baseEnd_8310986 < baseStart_8310986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310990 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_8310990 : Nat := 118140960795 + 8310990 * 2 ^ 59
def prefixEnd_8310990 : Nat := 4983230072969 + 3 ^ 40 * 8310990 * 2
def baseEnd_8310990 : Nat := 4267532584710543447103459

theorem tailTrace_8310990 : CollatzResearch.WordTrace tailWord_8310990 prefixEnd_8310990 4267532584710543447103459 := by
  unfold tailWord_8310990
  simp only [CollatzResearch.WordTrace]
  refine ⟨37890838520088763616572303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202084472107140072621718949 37890838520088763616572303)
  ·
    refine ⟨56836257780133145424858455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37890838520088763616572303 56836257780133145424858455)
    ·
      refine ⟨85254386670199718137287683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56836257780133145424858455 85254386670199718137287683)
      ·
        refine ⟨127881580005299577205931525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85254386670199718137287683 127881580005299577205931525)
        ·
          refine ⟨23977796250993670726112161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127881580005299577205931525 23977796250993670726112161)
          ·
            refine ⟨17983347188245253044584121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23977796250993670726112161 17983347188245253044584121)
            ·
              refine ⟨13487510391183939783438091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17983347188245253044584121 13487510391183939783438091)
              ·
                refine ⟨20231265586775909675157137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13487510391183939783438091 20231265586775909675157137)
                ·
                  refine ⟨15173449190081932256367853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20231265586775909675157137 15173449190081932256367853)
                  ·
                    refine ⟨5690043446280724596137945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15173449190081932256367853 5690043446280724596137945)
                    ·
                      refine ⟨4267532584710543447103459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690043446280724596137945 4267532584710543447103459)
                      ·
                        rfl

theorem cell23_8310990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_8310990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310990 prefixEnd_8310990 := by exact prefixLift 8310990
  have htrace : WordTrace (prefixWord ++ tailWord_8310990) baseStart_8310990 baseEnd_8310990 := by
    simpa [prefixWord, tailWord_8310990, baseEnd_8310990] using wordTrace_append hprefix tailTrace_8310990
  have hstable : (prefixWord ++ tailWord_8310990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310990).length < 2 ^ (prefixWord ++ tailWord_8310990).sum := by decide
  have hdescent : baseEnd_8310990 < baseStart_8310990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311013 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_8311013 : Nat := 118140960795 + 8311013 * 2 ^ 59
def prefixEnd_8311013 : Nat := 4983230072969 + 3 ^ 40 * 8311013 * 2
def baseEnd_8311013 : Nat := 1422514798255198952371951

theorem tailTrace_8311013 : CollatzResearch.WordTrace tailWord_8311013 prefixEnd_8311013 1422514798255198952371951 := by
  unfold tailWord_8311013
  simp only [CollatzResearch.WordTrace]
  refine ⟨303127547039626783860665693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202085031359751189240443795 303127547039626783860665693)
  ·
    refine ⟨113672830139860043947749635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303127547039626783860665693 113672830139860043947749635)
    ·
      refine ⟨170509245209790065921624453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113672830139860043947749635 170509245209790065921624453)
      ·
        refine ⟨31970483476835637360304585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170509245209790065921624453 31970483476835637360304585)
        ·
          refine ⟨23977862607626728020228439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31970483476835637360304585 23977862607626728020228439)
          ·
            refine ⟨35966793911440092030342659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23977862607626728020228439 35966793911440092030342659)
            ·
              refine ⟨53950190867160138045513989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35966793911440092030342659 53950190867160138045513989)
              ·
                refine ⟨10115660787592525883533873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53950190867160138045513989 10115660787592525883533873)
                ·
                  refine ⟨7586745590694394412650405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115660787592525883533873 7586745590694394412650405)
                  ·
                    refine ⟨1422514798255198952371951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586745590694394412650405 1422514798255198952371951)
                    ·
                      rfl

theorem cell23_8311013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_8311013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311013 prefixEnd_8311013 := by exact prefixLift 8311013
  have htrace : WordTrace (prefixWord ++ tailWord_8311013) baseStart_8311013 baseEnd_8311013 := by
    simpa [prefixWord, tailWord_8311013, baseEnd_8311013] using wordTrace_append hprefix tailTrace_8311013
  have hstable : (prefixWord ++ tailWord_8311013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311013).length < 2 ^ (prefixWord ++ tailWord_8311013).sum := by decide
  have hdescent : baseEnd_8311013 < baseStart_8311013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311026 : List Nat := [3, 2, 1, 3, 2, 1, 3, 8]
def baseStart_8311026 : Nat := 118140960795 + 8311026 * 2 ^ 59
def prefixEnd_8311026 : Nat := 4983230072969 + 3 ^ 40 * 8311026 * 2
def baseEnd_8311026 : Nat := 158057447037559455787159

theorem tailTrace_8311026 : CollatzResearch.WordTrace tailWord_8311026 prefixEnd_8311026 158057447037559455787159 := by
  unfold tailWord_8311026
  simp only [CollatzResearch.WordTrace]
  refine ⟨75782005297144921770222233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202085347459053124720592621 75782005297144921770222233)
  ·
    refine ⟨56836503972858691327666675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75782005297144921770222233 56836503972858691327666675)
    ·
      refine ⟨85254755959288036991500013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56836503972858691327666675 85254755959288036991500013)
      ·
        refine ⟨31970533484733013871812505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85254755959288036991500013 31970533484733013871812505)
        ·
          refine ⟨23977900113549760403859379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31970533484733013871812505 23977900113549760403859379)
          ·
            refine ⟨35966850170324640605789069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23977900113549760403859379 35966850170324640605789069)
            ·
              refine ⟨13487568813871740227170901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35966850170324640605789069 13487568813871740227170901)
              ·
                refine ⟨158057447037559455787159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13487568813871740227170901 158057447037559455787159)
                ·
                  rfl

theorem cell23_8311026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_8311026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311026 prefixEnd_8311026 := by exact prefixLift 8311026
  have htrace : WordTrace (prefixWord ++ tailWord_8311026) baseStart_8311026 baseEnd_8311026 := by
    simpa [prefixWord, tailWord_8311026, baseEnd_8311026] using wordTrace_append hprefix tailTrace_8311026
  have hstable : (prefixWord ++ tailWord_8311026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311026).length < 2 ^ (prefixWord ++ tailWord_8311026).sum := by decide
  have hdescent : baseEnd_8311026 < baseStart_8311026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311039 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 2, 7]
def baseStart_8311039 : Nat := 118140960795 + 8311039 * 2 ^ 59
def prefixEnd_8311039 : Nat := 4983230072969 + 3 ^ 40 * 8311039 * 2
def baseEnd_8311039 : Nat := 1422519248420871251796911

theorem tailTrace_8311039 : CollatzResearch.WordTrace tailWord_8311039 prefixEnd_8311039 1422519248420871251796911 := by
  unfold tailWord_8311039
  simp only [CollatzResearch.WordTrace]
  refine ⟨303128495337532590301112171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202085663558355060200741447 303128495337532590301112171)
  ·
    refine ⟨454692743006298885451668257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303128495337532590301112171 454692743006298885451668257)
    ·
      refine ⟨341019557254724164088751193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454692743006298885451668257 341019557254724164088751193)
      ·
        refine ⟨255764667941043123066563395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341019557254724164088751193 255764667941043123066563395)
        ·
          refine ⟨383647001911564684599845093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255764667941043123066563395 383647001911564684599845093)
          ·
            refine ⟨71933812858418378362470955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383647001911564684599845093 71933812858418378362470955)
            ·
              refine ⟨107900719287627567543706433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71933812858418378362470955 107900719287627567543706433)
              ·
                refine ⟨80925539465720675657779825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107900719287627567543706433 80925539465720675657779825)
                ·
                  refine ⟨60694154599290506743334869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80925539465720675657779825 60694154599290506743334869)
                  ·
                    refine ⟨1422519248420871251796911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60694154599290506743334869 1422519248420871251796911)
                    ·
                      rfl

theorem cell23_8311039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_8311039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311039 prefixEnd_8311039 := by exact prefixLift 8311039
  have htrace : WordTrace (prefixWord ++ tailWord_8311039) baseStart_8311039 baseEnd_8311039 := by
    simpa [prefixWord, tailWord_8311039, baseEnd_8311039] using wordTrace_append hprefix tailTrace_8311039
  have hstable : (prefixWord ++ tailWord_8311039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311039).length < 2 ^ (prefixWord ++ tailWord_8311039).sum := by decide
  have hdescent : baseEnd_8311039 < baseStart_8311039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311096 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_8311096 : Nat := 118140960795 + 8311096 * 2 ^ 59
def prefixEnd_8311096 : Nat := 4983230072969 + 3 ^ 40 * 8311096 * 2
def baseEnd_8311096 : Nat := 4267587013659920032377971

theorem tailTrace_8311096 : CollatzResearch.WordTrace tailWord_8311096 prefixEnd_8311096 4267587013659920032377971 := by
  unfold tailWord_8311096
  simp only [CollatzResearch.WordTrace]
  refine ⟨151565287149163044517968571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202087049532217392690624761 151565287149163044517968571)
  ·
    refine ⟨227347930723744566776952857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151565287149163044517968571 227347930723744566776952857)
    ·
      refine ⟨170510948042808425082714643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227347930723744566776952857 170510948042808425082714643)
      ·
        refine ⟨255766422064212637624071965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170510948042808425082714643 255766422064212637624071965)
        ·
          refine ⟨95912408274079739109026987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255766422064212637624071965 95912408274079739109026987)
          ·
            refine ⟨143868612411119608663540481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95912408274079739109026987 143868612411119608663540481)
            ·
              refine ⟨107901459308339706497655361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143868612411119608663540481 107901459308339706497655361)
              ·
                refine ⟨80926094481254779873241521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107901459308339706497655361 80926094481254779873241521)
                ·
                  refine ⟨60694570860941084904931141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80926094481254779873241521 60694570860941084904931141)
                  ·
                    refine ⟨11380232036426453419674589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60694570860941084904931141 11380232036426453419674589)
                    ·
                      refine ⟨4267587013659920032377971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11380232036426453419674589 4267587013659920032377971)
                      ·
                        rfl

theorem cell23_8311096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_8311096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311096 prefixEnd_8311096 := by exact prefixLift 8311096
  have htrace : WordTrace (prefixWord ++ tailWord_8311096) baseStart_8311096 baseEnd_8311096 := by
    simpa [prefixWord, tailWord_8311096, baseEnd_8311096] using wordTrace_append hprefix tailTrace_8311096
  have hstable : (prefixWord ++ tailWord_8311096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311096).length < 2 ^ (prefixWord ++ tailWord_8311096).sum := by decide
  have hdescent : baseEnd_8311096 < baseStart_8311096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311097 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 1, 3, 2]
def baseStart_8311097 : Nat := 118140960795 + 8311097 * 2 ^ 59
def prefixEnd_8311097 : Nat := 4983230072969 + 3 ^ 40 * 8311097 * 2
def baseEnd_8311097 : Nat := 4267587527140574528465467

theorem tailTrace_8311097 : CollatzResearch.WordTrace tailWord_8311097 prefixEnd_8311097 4267587527140574528465467 := by
  unfold tailWord_8311097
  simp only [CollatzResearch.WordTrace]
  refine ⟨303130610771322466206723545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202087073847548310804482363 303130610771322466206723545)
  ·
    refine ⟨227347958078491849655042659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303130610771322466206723545 227347958078491849655042659)
    ·
      refine ⟨341021937117737774482563989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227347958078491849655042659 341021937117737774482563989)
      ·
        refine ⟨15985403302393958178870187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 341021937117737774482563989 15985403302393958178870187)
        ·
          refine ⟨23978104953590937268305281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15985403302393958178870187 23978104953590937268305281)
          ·
            refine ⟨17983578715193202951228961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23978104953590937268305281 17983578715193202951228961)
            ·
              refine ⟨13487684036394902213421721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17983578715193202951228961 13487684036394902213421721)
              ·
                refine ⟨10115763027296176660066291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13487684036394902213421721 10115763027296176660066291)
                ·
                  refine ⟨15173644540944264990099437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115763027296176660066291 15173644540944264990099437)
                  ·
                    refine ⟨5690116702854099371287289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15173644540944264990099437 5690116702854099371287289)
                    ·
                      refine ⟨4267587527140574528465467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690116702854099371287289 4267587527140574528465467)
                      ·
                        rfl

theorem cell23_8311097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_8311097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311097 prefixEnd_8311097 := by exact prefixLift 8311097
  have htrace : WordTrace (prefixWord ++ tailWord_8311097) baseStart_8311097 baseEnd_8311097 := by
    simpa [prefixWord, tailWord_8311097, baseEnd_8311097] using wordTrace_append hprefix tailTrace_8311097
  have hstable : (prefixWord ++ tailWord_8311097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311097).length < 2 ^ (prefixWord ++ tailWord_8311097).sum := by decide
  have hdescent : baseEnd_8311097 < baseStart_8311097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311144 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_8311144 : Nat := 118140960795 + 8311144 * 2 ^ 59
def prefixEnd_8311144 : Nat := 4983230072969 + 3 ^ 40 * 8311144 * 2
def baseEnd_8311144 : Nat := 4267611660731335844577751

theorem tailTrace_8311144 : CollatzResearch.WordTrace tailWord_8311144 prefixEnd_8311144 4267611660731335844577751 := by
  unfold tailWord_8311144
  simp only [CollatzResearch.WordTrace]
  refine ⟨151566162501076096616842243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202088216668101462155789657 151566162501076096616842243)
  ·
    refine ⟨227349243751614144925263365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151566162501076096616842243 227349243751614144925263365)
    ·
      refine ⟨42627983203427652173486881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227349243751614144925263365 42627983203427652173486881)
      ·
        refine ⟨31970987402570739130115161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42627983203427652173486881 31970987402570739130115161)
        ·
          refine ⟨23978240551928054347586371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31970987402570739130115161 23978240551928054347586371)
          ·
            refine ⟨35967360827892081521379557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23978240551928054347586371 35967360827892081521379557)
            ·
              refine ⟨6743880155229765285258667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35967360827892081521379557 6743880155229765285258667)
              ·
                refine ⟨10115820232844647927888001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743880155229765285258667 10115820232844647927888001)
                ·
                  refine ⟨7586865174633485945916001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10115820232844647927888001 7586865174633485945916001)
                  ·
                    refine ⟨5690148880975114459437001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7586865174633485945916001 5690148880975114459437001)
                    ·
                      refine ⟨4267611660731335844577751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690148880975114459437001 4267611660731335844577751)
                      ·
                        rfl

theorem cell23_8311144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_8311144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311144 prefixEnd_8311144 := by exact prefixLift 8311144
  have htrace : WordTrace (prefixWord ++ tailWord_8311144) baseStart_8311144 baseEnd_8311144 := by
    simpa [prefixWord, tailWord_8311144, baseEnd_8311144] using wordTrace_append hprefix tailTrace_8311144
  have hstable : (prefixWord ++ tailWord_8311144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311144).length < 2 ^ (prefixWord ++ tailWord_8311144).sum := by decide
  have hdescent : baseEnd_8311144 < baseStart_8311144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311163 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 2, 5]
def baseStart_8311163 : Nat := 118140960795 + 8311163 * 2 ^ 59
def prefixEnd_8311163 : Nat := 4983230072969 + 3 ^ 40 * 8311163 * 2
def baseEnd_8311163 : Nat := 1422540472287923756746721

theorem tailTrace_8311163 : CollatzResearch.WordTrace tailWord_8311163 prefixEnd_8311163 1422540472287923756746721 := by
  unfold tailWord_8311163
  simp only [CollatzResearch.WordTrace]
  refine ⟨303133017989083359478626143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202088678659388906319084095 303133017989083359478626143)
  ·
    refine ⟨454699526983625039217939215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303133017989083359478626143 454699526983625039217939215)
    ·
      refine ⟨682049290475437558826908823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454699526983625039217939215 682049290475437558826908823)
      ·
        refine ⟨1023073935713156338240363235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682049290475437558826908823 1023073935713156338240363235)
        ·
          refine ⟨1534610903569734507360544853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023073935713156338240363235 1534610903569734507360544853)
          ·
            refine ⟨17983721526207826258131385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1534610903569734507360544853 17983721526207826258131385)
            ·
              refine ⟨13487791144655869693598539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17983721526207826258131385 13487791144655869693598539)
              ·
                refine ⟨20231686716983804540397809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13487791144655869693598539 20231686716983804540397809)
                ·
                  refine ⟨15173765037737853405298357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20231686716983804540397809 15173765037737853405298357)
                  ·
                    refine ⟨1422540472287923756746721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15173765037737853405298357 1422540472287923756746721)
                    ·
                      rfl

theorem cell23_8311163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 5].length) (baseStart_8311163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311163 prefixEnd_8311163 := by exact prefixLift 8311163
  have htrace : WordTrace (prefixWord ++ tailWord_8311163) baseStart_8311163 baseEnd_8311163 := by
    simpa [prefixWord, tailWord_8311163, baseEnd_8311163] using wordTrace_append hprefix tailTrace_8311163
  have hstable : (prefixWord ++ tailWord_8311163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311163).length < 2 ^ (prefixWord ++ tailWord_8311163).sum := by decide
  have hdescent : baseEnd_8311163 < baseStart_8311163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311193 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 3, 4]
def baseStart_8311193 : Nat := 118140960795 + 8311193 * 2 ^ 59
def prefixEnd_8311193 : Nat := 4983230072969 + 3 ^ 40 * 8311193 * 2
def baseEnd_8311193 : Nat := 1422545607094468717621675

theorem tailTrace_8311193 : CollatzResearch.WordTrace tailWord_8311193 prefixEnd_8311193 1422545607094468717621675 := by
  unfold tailWord_8311193
  simp only [CollatzResearch.WordTrace]
  refine ⟨303134112178974674602218233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202089408119316449734812155 303134112178974674602218233)
  ·
    refine ⟨227350584134231005951663675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303134112178974674602218233 227350584134231005951663675)
    ·
      refine ⟨341025876201346508927495513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227350584134231005951663675 341025876201346508927495513)
      ·
        refine ⟨255769407151009881695621635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341025876201346508927495513 255769407151009881695621635)
        ·
          refine ⟨383654110726514822543432453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255769407151009881695621635 383654110726514822543432453)
          ·
            refine ⟨71935145761221529226893585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383654110726514822543432453 71935145761221529226893585)
            ·
              refine ⟨53951359320916146920170189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71935145761221529226893585 53951359320916146920170189)
              ·
                refine ⟨20231759745343555095063821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53951359320916146920170189 20231759745343555095063821)
                ·
                  refine ⟨7586909904503833160648933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20231759745343555095063821 7586909904503833160648933)
                  ·
                    refine ⟨1422545607094468717621675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586909904503833160648933 1422545607094468717621675)
                    ·
                      rfl

theorem cell23_8311193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_8311193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311193 prefixEnd_8311193 := by exact prefixLift 8311193
  have htrace : WordTrace (prefixWord ++ tailWord_8311193) baseStart_8311193 baseEnd_8311193 := by
    simpa [prefixWord, tailWord_8311193, baseEnd_8311193] using wordTrace_append hprefix tailTrace_8311193
  have hstable : (prefixWord ++ tailWord_8311193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311193).length < 2 ^ (prefixWord ++ tailWord_8311193).sum := by decide
  have hdescent : baseEnd_8311193 < baseStart_8311193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311200 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 2, 4, 2]
def baseStart_8311200 : Nat := 118140960795 + 8311200 * 2 ^ 59
def prefixEnd_8311200 : Nat := 4983230072969 + 3 ^ 40 * 8311200 * 2
def baseEnd_8311200 : Nat := 4267640415647987625477493

theorem tailTrace_8311200 : CollatzResearch.WordTrace tailWord_8311200 prefixEnd_8311200 4267640415647987625477493 := by
  unfold tailWord_8311200
  simp only [CollatzResearch.WordTrace]
  refine ⟨151567183744974657398861527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202089578326632876531815369 151567183744974657398861527)
  ·
    refine ⟨227350775617461986098292291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151567183744974657398861527 227350775617461986098292291)
    ·
      refine ⟨341026163426192979147438437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227350775617461986098292291 341026163426192979147438437)
      ·
        refine ⟨63942405642411183590144707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341026163426192979147438437 63942405642411183590144707)
        ·
          refine ⟨95913608463616775385217061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63942405642411183590144707 95913608463616775385217061)
          ·
            refine ⟨17983801586928145384728199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95913608463616775385217061 17983801586928145384728199)
            ·
              refine ⟨26975702380392218077092299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17983801586928145384728199 26975702380392218077092299)
              ·
                refine ⟨40463553570588327115638449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26975702380392218077092299 40463553570588327115638449)
                ·
                  refine ⟨30347665177941245336728837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40463553570588327115638449 30347665177941245336728837)
                  ·
                    refine ⟨5690187220863983500636657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30347665177941245336728837 5690187220863983500636657)
                    ·
                      refine ⟨4267640415647987625477493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690187220863983500636657 4267640415647987625477493)
                      ·
                        rfl

theorem cell23_8311200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_8311200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311200 prefixEnd_8311200 := by exact prefixLift 8311200
  have htrace : WordTrace (prefixWord ++ tailWord_8311200) baseStart_8311200 baseEnd_8311200 := by
    simpa [prefixWord, tailWord_8311200, baseEnd_8311200] using wordTrace_append hprefix tailTrace_8311200
  have hstable : (prefixWord ++ tailWord_8311200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311200).length < 2 ^ (prefixWord ++ tailWord_8311200).sum := by decide
  have hdescent : baseEnd_8311200 < baseStart_8311200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311226 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_8311226 : Nat := 118140960795 + 8311226 * 2 ^ 59
def prefixEnd_8311226 : Nat := 4983230072969 + 3 ^ 40 * 8311226 * 2
def baseEnd_8311226 : Nat := 4267653766145004523752373

theorem tailTrace_8311226 : CollatzResearch.WordTrace tailWord_8311226 prefixEnd_8311226 4267653766145004523752373 := by
  unfold tailWord_8311226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75783828946963780309542383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202090210525236747492113021 75783828946963780309542383)
  ·
    refine ⟨113675743420445670464313575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75783828946963780309542383 113675743420445670464313575)
    ·
      refine ⟨170513615130668505696470363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113675743420445670464313575 170513615130668505696470363)
      ·
        refine ⟨255770422696002758544705545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170513615130668505696470363 255770422696002758544705545)
        ·
          refine ⟨191827817022002068908529159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255770422696002758544705545 191827817022002068908529159)
          ·
            refine ⟨287741725533003103362793739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191827817022002068908529159 287741725533003103362793739)
            ·
              refine ⟨431612588299504655044190609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287741725533003103362793739 431612588299504655044190609)
              ·
                refine ⟨323709441224628491283142957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431612588299504655044190609 323709441224628491283142957)
                ·
                  refine ⟨121391040459235684231178609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323709441224628491283142957 121391040459235684231178609)
                  ·
                    refine ⟨91043280344426763173383957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121391040459235684231178609 91043280344426763173383957)
                    ·
                      refine ⟨4267653766145004523752373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91043280344426763173383957 4267653766145004523752373)
                      ·
                        rfl

theorem cell23_8311226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_8311226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311226 prefixEnd_8311226 := by exact prefixLift 8311226
  have htrace : WordTrace (prefixWord ++ tailWord_8311226) baseStart_8311226 baseEnd_8311226 := by
    simpa [prefixWord, tailWord_8311226, baseEnd_8311226] using wordTrace_append hprefix tailTrace_8311226
  have hstable : (prefixWord ++ tailWord_8311226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311226).length < 2 ^ (prefixWord ++ tailWord_8311226).sum := by decide
  have hdescent : baseEnd_8311226 < baseStart_8311226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311240 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 6]
def baseStart_8311240 : Nat := 118140960795 + 8311240 * 2 ^ 59
def prefixEnd_8311240 : Nat := 4983230072969 + 3 ^ 40 * 8311240 * 2
def baseEnd_8311240 : Nat := 474184550541574163219701

theorem tailTrace_8311240 : CollatzResearch.WordTrace tailWord_8311240 prefixEnd_8311240 474184550541574163219701 := by
  unfold tailWord_8311240
  simp only [CollatzResearch.WordTrace]
  refine ⟨151567913204902200814589587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202090550939869601086119449 151567913204902200814589587)
  ·
    refine ⟨227351869807353301221884381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151567913204902200814589587 227351869807353301221884381)
    ·
      refine ⟨85256951177757487958206643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227351869807353301221884381 85256951177757487958206643)
      ·
        refine ⟨127885426766636231937309965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85256951177757487958206643 127885426766636231937309965)
        ·
          refine ⟨47957035037488586976491237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127885426766636231937309965 47957035037488586976491237)
          ·
            refine ⟨8991944069529110058092107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47957035037488586976491237 8991944069529110058092107)
            ·
              refine ⟨13487916104293665087138161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991944069529110058092107 13487916104293665087138161)
              ·
                refine ⟨10115937078220248815353621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13487916104293665087138161 10115937078220248815353621)
                ·
                  refine ⟨474184550541574163219701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10115937078220248815353621 474184550541574163219701)
                  ·
                    rfl

theorem cell23_8311240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 6].length) (baseStart_8311240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311240 prefixEnd_8311240 := by exact prefixLift 8311240
  have htrace : WordTrace (prefixWord ++ tailWord_8311240) baseStart_8311240 baseEnd_8311240 := by
    simpa [prefixWord, tailWord_8311240, baseEnd_8311240] using wordTrace_append hprefix tailTrace_8311240
  have hstable : (prefixWord ++ tailWord_8311240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311240).length < 2 ^ (prefixWord ++ tailWord_8311240).sum := by decide
  have hdescent : baseEnd_8311240 < baseStart_8311240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311277 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_8311277 : Nat := 118140960795 + 8311277 * 2 ^ 59
def prefixEnd_8311277 : Nat := 4983230072969 + 3 ^ 40 * 8311277 * 2
def baseEnd_8311277 : Nat := 4267679953658383824214639

theorem tailTrace_8311277 : CollatzResearch.WordTrace tailWord_8311277 prefixEnd_8311277 4267679953658383824214639 := by
  unfold tailWord_8311277
  simp only [CollatzResearch.WordTrace]
  refine ⟨303137175910670356948276085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202091450607113571298850723 303137175910670356948276085)
  ·
    refine ⟨28419110241625345963900883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303137175910670356948276085 28419110241625345963900883)
    ·
      refine ⟨42628665362438018945851325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28419110241625345963900883 42628665362438018945851325)
      ·
        refine ⟨15985749510914257104694247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42628665362438018945851325 15985749510914257104694247)
        ·
          refine ⟨23978624266371385657041371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15985749510914257104694247 23978624266371385657041371)
          ·
            refine ⟨35967936399557078485562057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23978624266371385657041371 35967936399557078485562057)
            ·
              refine ⟨26975952299667808864171543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35967936399557078485562057 26975952299667808864171543)
              ·
                refine ⟨40463928449501713296257315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26975952299667808864171543 40463928449501713296257315)
                ·
                  refine ⟨60695892674252569944385973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40463928449501713296257315 60695892674252569944385973)
                  ·
                    refine ⟨5690239938211178432286185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60695892674252569944385973 5690239938211178432286185)
                    ·
                      refine ⟨4267679953658383824214639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690239938211178432286185 4267679953658383824214639)
                      ·
                        rfl

theorem cell23_8311277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_8311277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311277 prefixEnd_8311277 := by exact prefixLift 8311277
  have htrace : WordTrace (prefixWord ++ tailWord_8311277) baseStart_8311277 baseEnd_8311277 := by
    simpa [prefixWord, tailWord_8311277, baseEnd_8311277] using wordTrace_append hprefix tailTrace_8311277
  have hstable : (prefixWord ++ tailWord_8311277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311277).length < 2 ^ (prefixWord ++ tailWord_8311277).sum := by decide
  have hdescent : baseEnd_8311277 < baseStart_8311277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311283 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 6, 4]
def baseStart_8311283 : Nat := 118140960795 + 8311283 * 2 ^ 59
def prefixEnd_8311283 : Nat := 4983230072969 + 3 ^ 40 * 8311283 * 2
def baseEnd_8311283 : Nat := 1422561011514103600246537

theorem tailTrace_8311283 : CollatzResearch.WordTrace tailWord_8311283 prefixEnd_8311283 1422561011514103600246537 := by
  unfold tailWord_8311283
  simp only [CollatzResearch.WordTrace]
  refine ⟨303137394748648619972994503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202091596499099079981996335 303137394748648619972994503)
  ·
    refine ⟨454706092122972929959491755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303137394748648619972994503 454706092122972929959491755)
    ·
      refine ⟨682059138184459394939237633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454706092122972929959491755 682059138184459394939237633)
      ·
        refine ⟨511544353638344546204428225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682059138184459394939237633 511544353638344546204428225)
        ·
          refine ⟨383658265228758409653321169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511544353638344546204428225 383658265228758409653321169)
          ·
            refine ⟨287743698921568807239990877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383658265228758409653321169 287743698921568807239990877)
            ·
              refine ⟨107903887095588302714996579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287743698921568807239990877 107903887095588302714996579)
              ·
                refine ⟨161855830643382454072494869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107903887095588302714996579 161855830643382454072494869)
                ·
                  refine ⟨7586992061408552534648197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161855830643382454072494869 7586992061408552534648197)
                  ·
                    refine ⟨1422561011514103600246537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7586992061408552534648197 1422561011514103600246537)
                    ·
                      rfl

theorem cell23_8311283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 4].length) (baseStart_8311283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311283 prefixEnd_8311283 := by exact prefixLift 8311283
  have htrace : WordTrace (prefixWord ++ tailWord_8311283) baseStart_8311283 baseEnd_8311283 := by
    simpa [prefixWord, tailWord_8311283, baseEnd_8311283] using wordTrace_append hprefix tailTrace_8311283
  have hstable : (prefixWord ++ tailWord_8311283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311283).length < 2 ^ (prefixWord ++ tailWord_8311283).sum := by decide
  have hdescent : baseEnd_8311283 < baseStart_8311283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311310 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_8311310 : Nat := 118140960795 + 8311310 * 2 ^ 59
def prefixEnd_8311310 : Nat := 4983230072969 + 3 ^ 40 * 8311310 * 2
def baseEnd_8311310 : Nat := 4267696898519982195101987

theorem tailTrace_8311310 : CollatzResearch.WordTrace tailWord_8311310 prefixEnd_8311310 4267696898519982195101987 := by
  unfold tailWord_8311310
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892297439943850448028423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202092253013033869056151589 37892297439943850448028423)
  ·
    refine ⟨56838446159915775672042635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37892297439943850448028423 56838446159915775672042635)
    ·
      refine ⟨85257669239873663508063953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56838446159915775672042635 85257669239873663508063953)
      ·
        refine ⟨63943251929905247631047965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85257669239873663508063953 63943251929905247631047965)
        ·
          refine ⟨23978719473714467861642987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63943251929905247631047965 23978719473714467861642987)
          ·
            refine ⟨35968079210571701792464481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23978719473714467861642987 35968079210571701792464481)
            ·
              refine ⟨26976059407928776344348361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35968079210571701792464481 26976059407928776344348361)
              ·
                refine ⟨20232044555946582258261271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26976059407928776344348361 20232044555946582258261271)
                ·
                  refine ⟨30348066833919873387391907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20232044555946582258261271 30348066833919873387391907)
                  ·
                    refine ⟨45522100250879810081087861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30348066833919873387391907 45522100250879810081087861)
                    ·
                      refine ⟨4267696898519982195101987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45522100250879810081087861 4267696898519982195101987)
                      ·
                        rfl

theorem cell23_8311310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_8311310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311310 prefixEnd_8311310 := by exact prefixLift 8311310
  have htrace : WordTrace (prefixWord ++ tailWord_8311310) baseStart_8311310 baseEnd_8311310 := by
    simpa [prefixWord, tailWord_8311310, baseEnd_8311310] using wordTrace_append hprefix tailTrace_8311310
  have hstable : (prefixWord ++ tailWord_8311310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311310).length < 2 ^ (prefixWord ++ tailWord_8311310).sum := by decide
  have hdescent : baseEnd_8311310 < baseStart_8311310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311323 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 3]
def baseStart_8311323 : Nat := 118140960795 + 8311323 * 2 ^ 59
def prefixEnd_8311323 : Nat := 4983230072969 + 3 ^ 40 * 8311323 * 2
def baseEnd_8311323 : Nat := 4267703573768490644239427

theorem tailTrace_8311323 : CollatzResearch.WordTrace tailWord_8311323 prefixEnd_8311323 4267703573768490644239427 := by
  unfold tailWord_8311323
  simp only [CollatzResearch.WordTrace]
  refine ⟨303138853668503706804450623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202092569112335804536300415 303138853668503706804450623)
  ·
    refine ⟨454708280502755560206675935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303138853668503706804450623 454708280502755560206675935)
    ·
      refine ⟨682062420754133340310013903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454708280502755560206675935 682062420754133340310013903)
      ·
        refine ⟨1023093631131200010465020855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682062420754133340310013903 1023093631131200010465020855)
        ·
          refine ⟨1534640446696800015697531283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023093631131200010465020855 1534640446696800015697531283)
          ·
            refine ⟨2301960670045200023546296925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534640446696800015697531283 2301960670045200023546296925)
            ·
              refine ⟨863235251266950008829861347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2301960670045200023546296925 863235251266950008829861347)
              ·
                refine ⟨1294852876900425013244792021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863235251266950008829861347 1294852876900425013244792021)
                ·
                  refine ⟨30348114302353711247924813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1294852876900425013244792021 30348114302353711247924813)
                  ·
                    refine ⟨11380542863382641717971805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30348114302353711247924813 11380542863382641717971805)
                    ·
                      refine ⟨4267703573768490644239427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11380542863382641717971805 4267703573768490644239427)
                      ·
                        rfl

theorem cell23_8311323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 3].length) (baseStart_8311323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311323 prefixEnd_8311323 := by exact prefixLift 8311323
  have htrace : WordTrace (prefixWord ++ tailWord_8311323) baseStart_8311323 baseEnd_8311323 := by
    simpa [prefixWord, tailWord_8311323, baseEnd_8311323] using wordTrace_append hprefix tailTrace_8311323
  have hstable : (prefixWord ++ tailWord_8311323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311323).length < 2 ^ (prefixWord ++ tailWord_8311323).sum := by decide
  have hdescent : baseEnd_8311323 < baseStart_8311323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311340 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_8311340 : Nat := 118140960795 + 8311340 * 2 ^ 59
def prefixEnd_8311340 : Nat := 4983230072969 + 3 ^ 40 * 8311340 * 2
def baseEnd_8311340 : Nat := 4267712302939617077726849

theorem tailTrace_8311340 : CollatzResearch.WordTrace tailWord_8311340 prefixEnd_8311340 4267712302939617077726849 := by
  unfold tailWord_8311340
  simp only [CollatzResearch.WordTrace]
  refine ⟨151569736854721059353909737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202092982472961412471879649 151569736854721059353909737)
  ·
    refine ⟨113677302641040794515432303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151569736854721059353909737 113677302641040794515432303)
    ·
      refine ⟨170515953961561191773148455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113677302641040794515432303 170515953961561191773148455)
      ·
        refine ⟨255773930942341787659722683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170515953961561191773148455 255773930942341787659722683)
        ·
          refine ⟨383660896413512681489584025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255773930942341787659722683 383660896413512681489584025)
          ·
            refine ⟨287745672310134511117188019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383660896413512681489584025 287745672310134511117188019)
            ·
              refine ⟨431618508465201766675782029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287745672310134511117188019 431618508465201766675782029)
              ·
                refine ⟨161856940674450662503418261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431618508465201766675782029 161856940674450662503418261)
                ·
                  refine ⟨7587044094114874804847731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161856940674450662503418261 7587044094114874804847731)
                  ·
                    refine ⟨11380566141172312207271597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7587044094114874804847731 11380566141172312207271597)
                    ·
                      refine ⟨4267712302939617077726849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11380566141172312207271597 4267712302939617077726849)
                      ·
                        rfl

theorem cell23_8311340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_8311340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311340 prefixEnd_8311340 := by exact prefixLift 8311340
  have htrace : WordTrace (prefixWord ++ tailWord_8311340) baseStart_8311340 baseEnd_8311340 := by
    simpa [prefixWord, tailWord_8311340, baseEnd_8311340] using wordTrace_append hprefix tailTrace_8311340
  have hstable : (prefixWord ++ tailWord_8311340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311340).length < 2 ^ (prefixWord ++ tailWord_8311340).sum := by decide
  have hdescent : baseEnd_8311340 < baseStart_8311340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311367 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_8311367 : Nat := 118140960795 + 8311367 * 2 ^ 59
def prefixEnd_8311367 : Nat := 4983230072969 + 3 ^ 40 * 8311367 * 2
def baseEnd_8311367 : Nat := 4267726166917288472089225

theorem tailTrace_8311367 : CollatzResearch.WordTrace tailWord_8311367 prefixEnd_8311367 4267726166917288472089225 := by
  unfold tailWord_8311367
  simp only [CollatzResearch.WordTrace]
  refine ⟨303140458480344302319052355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202093638986896201546034903 303140458480344302319052355)
  ·
    refine ⟨454710687720516453478578533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303140458480344302319052355 454710687720516453478578533)
    ·
      refine ⟨85258253947596835027233475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454710687720516453478578533 85258253947596835027233475)
      ·
        refine ⟨127887380921395252540850213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85258253947596835027233475 127887380921395252540850213)
        ·
          refine ⟨23978883922761609851409415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127887380921395252540850213 23978883922761609851409415)
          ·
            refine ⟨35968325884142414777114123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23978883922761609851409415 35968325884142414777114123)
            ·
              refine ⟨53952488826213622165671185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35968325884142414777114123 53952488826213622165671185)
              ·
                refine ⟨40464366619660216624253389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53952488826213622165671185 40464366619660216624253389)
                ·
                  refine ⟨15174137482372581234095021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40464366619660216624253389 15174137482372581234095021)
                  ·
                    refine ⟨5690301555889717962785633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15174137482372581234095021 5690301555889717962785633)
                    ·
                      refine ⟨4267726166917288472089225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690301555889717962785633 4267726166917288472089225)
                      ·
                        rfl

theorem cell23_8311367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_8311367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311367 prefixEnd_8311367 := by exact prefixLift 8311367
  have htrace : WordTrace (prefixWord ++ tailWord_8311367) baseStart_8311367 baseEnd_8311367 := by
    simpa [prefixWord, tailWord_8311367, baseEnd_8311367] using wordTrace_append hprefix tailTrace_8311367
  have hstable : (prefixWord ++ tailWord_8311367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311367).length < 2 ^ (prefixWord ++ tailWord_8311367).sum := by decide
  have hdescent : baseEnd_8311367 < baseStart_8311367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311431 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_8311431 : Nat := 118140960795 + 8311431 * 2 ^ 59
def prefixEnd_8311431 : Nat := 4983230072969 + 3 ^ 40 * 8311431 * 2
def baseEnd_8311431 : Nat := 4267759029679176221688931

theorem tailTrace_8311431 : CollatzResearch.WordTrace tailWord_8311431 prefixEnd_8311431 4267759029679176221688931 := by
  unfold tailWord_8311431
  simp only [CollatzResearch.WordTrace]
  refine ⟨303142792752112441249382147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202095195168074960832921431 303142792752112441249382147)
  ·
    refine ⟨454714189128168661874073221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303142792752112441249382147 454714189128168661874073221)
    ·
      refine ⟨85258910461531624101388729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454714189128168661874073221 85258910461531624101388729)
      ·
        refine ⟨63944182846148718076041547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85258910461531624101388729 63944182846148718076041547)
        ·
          refine ⟨95916274269223077114062321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63944182846148718076041547 95916274269223077114062321)
          ·
            refine ⟨71937205701917307835546741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95916274269223077114062321 71937205701917307835546741)
            ·
              refine ⟨6744113034554747609582507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71937205701917307835546741 6744113034554747609582507)
              ·
                refine ⟨10116169551832121414373761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6744113034554747609582507 10116169551832121414373761)
                ·
                  refine ⟨7587127163874091060780321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10116169551832121414373761 7587127163874091060780321)
                  ·
                    refine ⟨5690345372905568295585241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7587127163874091060780321 5690345372905568295585241)
                    ·
                      refine ⟨4267759029679176221688931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690345372905568295585241 4267759029679176221688931)
                      ·
                        rfl

theorem cell23_8311431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_8311431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311431 prefixEnd_8311431 := by exact prefixLift 8311431
  have htrace : WordTrace (prefixWord ++ tailWord_8311431) baseStart_8311431 baseEnd_8311431 := by
    simpa [prefixWord, tailWord_8311431, baseEnd_8311431] using wordTrace_append hprefix tailTrace_8311431
  have hstable : (prefixWord ++ tailWord_8311431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311431).length < 2 ^ (prefixWord ++ tailWord_8311431).sum := by decide
  have hdescent : baseEnd_8311431 < baseStart_8311431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311443 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_8311443 : Nat := 118140960795 + 8311443 * 2 ^ 59
def prefixEnd_8311443 : Nat := 4983230072969 + 3 ^ 40 * 8311443 * 2
def baseEnd_8311443 : Nat := 4267765191447030174738875

theorem tailTrace_8311443 : CollatzResearch.WordTrace tailWord_8311443 prefixEnd_8311443 4267765191447030174738875 := by
  unfold tailWord_8311443
  simp only [CollatzResearch.WordTrace]
  refine ⟨303143230428068967298818983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202095486952045978199212655 303143230428068967298818983)
  ·
    refine ⟨454714845642103450948228475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303143230428068967298818983 454714845642103450948228475)
    ·
      refine ⟨682072268463155176422342713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454714845642103450948228475 682072268463155176422342713)
      ·
        refine ⟨511554201347366382316757035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682072268463155176422342713 511554201347366382316757035)
        ·
          refine ⟨767331302021049573475135553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511554201347366382316757035 767331302021049573475135553)
          ·
            refine ⟨575498476515787180106351665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767331302021049573475135553 575498476515787180106351665)
            ·
              refine ⟨431623857386840385079763749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575498476515787180106351665 431623857386840385079763749)
              ·
                refine ⟨80929473260032572202455703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431623857386840385079763749 80929473260032572202455703)
                ·
                  refine ⟨121394209890048858303683555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80929473260032572202455703 121394209890048858303683555)
                  ·
                    refine ⟨182091314835073287455525333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121394209890048858303683555 182091314835073287455525333)
                    ·
                      refine ⟨4267765191447030174738875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182091314835073287455525333 4267765191447030174738875)
                      ·
                        rfl

theorem cell23_8311443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_8311443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311443 prefixEnd_8311443 := by exact prefixLift 8311443
  have htrace : WordTrace (prefixWord ++ tailWord_8311443) baseStart_8311443 baseEnd_8311443 := by
    simpa [prefixWord, tailWord_8311443, baseEnd_8311443] using wordTrace_append hprefix tailTrace_8311443
  have hstable : (prefixWord ++ tailWord_8311443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311443).length < 2 ^ (prefixWord ++ tailWord_8311443).sum := by decide
  have hdescent : baseEnd_8311443 < baseStart_8311443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311460 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_8311460 : Nat := 118140960795 + 8311460 * 2 ^ 59
def prefixEnd_8311460 : Nat := 4983230072969 + 3 ^ 40 * 8311460 * 2
def baseEnd_8311460 : Nat := 4267773920618156608226297

theorem tailTrace_8311460 : CollatzResearch.WordTrace tailWord_8311460 prefixEnd_8311460 4267773920618156608226297 := by
  unfold tailWord_8311460
  simp only [CollatzResearch.WordTrace]
  refine ⟨151571925234503689601093917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202095900312671586134791889 151571925234503689601093917)
  ·
    refine ⟨56839471962938883600410219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151571925234503689601093917 56839471962938883600410219)
    ·
      refine ⟨85259207944408325400615329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56839471962938883600410219 85259207944408325400615329)
      ·
        refine ⟨63944405958306244050461497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85259207944408325400615329 63944405958306244050461497)
        ·
          refine ⟨47958304468729683037846123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63944405958306244050461497 47958304468729683037846123)
          ·
            refine ⟨71937456703094524556769185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47958304468729683037846123 71937456703094524556769185)
            ·
              refine ⟨53953092527320893417576889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71937456703094524556769185 53953092527320893417576889)
              ·
                refine ⟨40464819395490670063182667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53953092527320893417576889 40464819395490670063182667)
                ·
                  refine ⟨60697229093236005094774001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40464819395490670063182667 60697229093236005094774001)
                  ·
                    refine ⟨45522921819927003821080501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60697229093236005094774001 45522921819927003821080501)
                    ·
                      refine ⟨4267773920618156608226297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45522921819927003821080501 4267773920618156608226297)
                      ·
                        rfl

theorem cell23_8311460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_8311460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311460 prefixEnd_8311460 := by exact prefixLift 8311460
  have htrace : WordTrace (prefixWord ++ tailWord_8311460) baseStart_8311460 baseEnd_8311460 := by
    simpa [prefixWord, tailWord_8311460, baseEnd_8311460] using wordTrace_append hprefix tailTrace_8311460
  have hstable : (prefixWord ++ tailWord_8311460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311460).length < 2 ^ (prefixWord ++ tailWord_8311460).sum := by decide
  have hdescent : baseEnd_8311460 < baseStart_8311460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311477 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_8311477 : Nat := 118140960795 + 8311477 * 2 ^ 59
def prefixEnd_8311477 : Nat := 4983230072969 + 3 ^ 40 * 8311477 * 2
def baseEnd_8311477 : Nat := 4267782649789283041713719

theorem tailTrace_8311477 : CollatzResearch.WordTrace tailWord_8311477 prefixEnd_8311477 4267782649789283041713719 := by
  unfold tailWord_8311477
  simp only [CollatzResearch.WordTrace]
  refine ⟨303144470509945791105556685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202096313673297194070371123 303144470509945791105556685)
  ·
    refine ⟨113679176441229671664583757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303144470509945791105556685 113679176441229671664583757)
    ·
      refine ⟨42629691165461126874218909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113679176441229671664583757 42629691165461126874218909)
      ·
        refine ⟨15986134187047922577832091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42629691165461126874218909 15986134187047922577832091)
        ·
          refine ⟨23979201280571883866748137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986134187047922577832091 23979201280571883866748137)
          ·
            refine ⟨17984400960428912900061103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23979201280571883866748137 17984400960428912900061103)
            ·
              refine ⟨26976601440643369350091655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17984400960428912900061103 26976601440643369350091655)
              ·
                refine ⟨40464902160965054025137483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26976601440643369350091655 40464902160965054025137483)
                ·
                  refine ⟨60697353241447581037706225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40464902160965054025137483 60697353241447581037706225)
                  ·
                    refine ⟨45523014931085685778279669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60697353241447581037706225 45523014931085685778279669)
                    ·
                      refine ⟨4267782649789283041713719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45523014931085685778279669 4267782649789283041713719)
                      ·
                        rfl

theorem cell23_8311477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_8311477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311477 prefixEnd_8311477 := by exact prefixLift 8311477
  have htrace : WordTrace (prefixWord ++ tailWord_8311477) baseStart_8311477 baseEnd_8311477 := by
    simpa [prefixWord, tailWord_8311477, baseEnd_8311477] using wordTrace_append hprefix tailTrace_8311477
  have hstable : (prefixWord ++ tailWord_8311477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311477).length < 2 ^ (prefixWord ++ tailWord_8311477).sum := by decide
  have hdescent : baseEnd_8311477 < baseStart_8311477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311501 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_8311501 : Nat := 118140960795 + 8311501 * 2 ^ 59
def prefixEnd_8311501 : Nat := 4983230072969 + 3 ^ 40 * 8311501 * 2
def baseEnd_8311501 : Nat := 1422598324441663649271203

theorem tailTrace_8311501 : CollatzResearch.WordTrace tailWord_8311501 prefixEnd_8311501 1422598324441663649271203 := by
  unfold tailWord_8311501
  simp only [CollatzResearch.WordTrace]
  refine ⟨303145345861858843204430357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202096897241239228802953571 303145345861858843204430357)
  ·
    refine ⟨14209938087274633275207673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303145345861858843204430357 14209938087274633275207673)
    ·
      refine ⟨10657453565455974956405755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14209938087274633275207673 10657453565455974956405755)
      ·
        refine ⟨15986180348183962434608633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657453565455974956405755 15986180348183962434608633)
        ·
          refine ⟨11989635261137971825956475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15986180348183962434608633 11989635261137971825956475)
          ·
            refine ⟨17984452891706957738934713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11989635261137971825956475 17984452891706957738934713)
            ·
              refine ⟨13488339668780218304201035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17984452891706957738934713 13488339668780218304201035)
              ·
                refine ⟨20232509503170327456301553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13488339668780218304201035 20232509503170327456301553)
                ·
                  refine ⟨15174382127377745592226165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20232509503170327456301553 15174382127377745592226165)
                  ·
                    refine ⟨1422598324441663649271203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15174382127377745592226165 1422598324441663649271203)
                    ·
                      rfl

theorem cell23_8311501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_8311501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311501 prefixEnd_8311501 := by exact prefixLift 8311501
  have htrace : WordTrace (prefixWord ++ tailWord_8311501) baseStart_8311501 baseEnd_8311501 := by
    simpa [prefixWord, tailWord_8311501, baseEnd_8311501] using wordTrace_append hprefix tailTrace_8311501
  have hstable : (prefixWord ++ tailWord_8311501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311501).length < 2 ^ (prefixWord ++ tailWord_8311501).sum := by decide
  have hdescent : baseEnd_8311501 < baseStart_8311501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311514 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_8311514 : Nat := 118140960795 + 8311514 * 2 ^ 59
def prefixEnd_8311514 : Nat := 4983230072969 + 3 ^ 40 * 8311514 * 2
def baseEnd_8311514 : Nat := 1422600549524499798983683

theorem tailTrace_8311514 : CollatzResearch.WordTrace tailWord_8311514 prefixEnd_8311514 1422600549524499798983683 := by
  unfold tailWord_8311514
  simp only [CollatzResearch.WordTrace]
  refine ⟨75786455002702936606163399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202097213340541164283102397 75786455002702936606163399)
  ·
    refine ⟨113679682504054404909245099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75786455002702936606163399 113679682504054404909245099)
    ·
      refine ⟨170519523756081607363867649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113679682504054404909245099 170519523756081607363867649)
      ·
        refine ⟨127889642817061205522900737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170519523756081607363867649 127889642817061205522900737)
        ·
          refine ⟨95917232112795904142175553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127889642817061205522900737 95917232112795904142175553)
          ·
            refine ⟨71937924084596928106631665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95917232112795904142175553 71937924084596928106631665)
            ·
              refine ⟨53953443063447696079973749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71937924084596928106631665 53953443063447696079973749)
              ·
                refine ⟨5058135287198221507497539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53953443063447696079973749 5058135287198221507497539)
                ·
                  refine ⟨7587202930797332261246309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058135287198221507497539 7587202930797332261246309)
                  ·
                    refine ⟨1422600549524499798983683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7587202930797332261246309 1422600549524499798983683)
                    ·
                      rfl

theorem cell23_8311514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_8311514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311514 prefixEnd_8311514 := by exact prefixLift 8311514
  have htrace : WordTrace (prefixWord ++ tailWord_8311514) baseStart_8311514 baseEnd_8311514 := by
    simpa [prefixWord, tailWord_8311514, baseEnd_8311514] using wordTrace_append hprefix tailTrace_8311514
  have hstable : (prefixWord ++ tailWord_8311514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311514).length < 2 ^ (prefixWord ++ tailWord_8311514).sum := by decide
  have hdescent : baseEnd_8311514 < baseStart_8311514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311530 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_8311530 : Nat := 118140960795 + 8311530 * 2 ^ 59
def prefixEnd_8311530 : Nat := 4983230072969 + 3 ^ 40 * 8311530 * 2
def baseEnd_8311530 : Nat := 4267809864263971334350975

theorem tailTrace_8311530 : CollatzResearch.WordTrace tailWord_8311530 prefixEnd_8311530 4267809864263971334350975 := by
  unfold tailWord_8311530
  simp only [CollatzResearch.WordTrace]
  refine ⟨75786600894688445289309011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202097602385835854104824029 75786600894688445289309011)
  ·
    refine ⟨113679901342032667933963517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75786600894688445289309011 113679901342032667933963517)
    ·
      refine ⟨42629963003262250475236319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113679901342032667933963517 42629963003262250475236319)
      ·
        refine ⟨63944944504893375712854479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42629963003262250475236319 63944944504893375712854479)
        ·
          refine ⟨95917416757340063569281719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63944944504893375712854479 95917416757340063569281719)
          ·
            refine ⟨143876125136010095353922579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95917416757340063569281719 143876125136010095353922579)
            ·
              refine ⟨215814187704015143030883869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143876125136010095353922579 215814187704015143030883869)
              ·
                refine ⟨80930320389005678636581451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215814187704015143030883869 80930320389005678636581451)
                ·
                  refine ⟨121395480583508517954872177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80930320389005678636581451 121395480583508517954872177)
                  ·
                    refine ⟨91046610437631388466154133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121395480583508517954872177 91046610437631388466154133)
                    ·
                      refine ⟨4267809864263971334350975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91046610437631388466154133 4267809864263971334350975)
                      ·
                        rfl

theorem cell23_8311530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_8311530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311530 prefixEnd_8311530 := by exact prefixLift 8311530
  have htrace : WordTrace (prefixWord ++ tailWord_8311530) baseStart_8311530 baseEnd_8311530 := by
    simpa [prefixWord, tailWord_8311530, baseEnd_8311530] using wordTrace_append hprefix tailTrace_8311530
  have hstable : (prefixWord ++ tailWord_8311530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311530).length < 2 ^ (prefixWord ++ tailWord_8311530).sum := by decide
  have hdescent : baseEnd_8311530 < baseStart_8311530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311571 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 1, 1, 3]
def baseStart_8311571 : Nat := 118140960795 + 8311571 * 2 ^ 59
def prefixEnd_8311571 : Nat := 4983230072969 + 3 ^ 40 * 8311571 * 2
def baseEnd_8311571 : Nat := 4267830916970805673938287

theorem tailTrace_8311571 : CollatzResearch.WordTrace tailWord_8311571 prefixEnd_8311571 4267830916970805673938287 := by
  unfold tailWord_8311571
  simp only [CollatzResearch.WordTrace]
  refine ⟨303147898971605245159478567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202098599314403496772985711 303147898971605245159478567)
  ·
    refine ⟨454721848457407867739217851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303147898971605245159478567 454721848457407867739217851)
    ·
      refine ⟨682082772686111801608826777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454721848457407867739217851 682082772686111801608826777)
      ·
        refine ⟨511562079514583851206620083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682082772686111801608826777 511562079514583851206620083)
        ·
          refine ⟨767343119271875776809930125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511562079514583851206620083 767343119271875776809930125)
          ·
            refine ⟨287753669726953416303723797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 767343119271875776809930125 287753669726953416303723797)
            ·
              refine ⟨13488453268450941389237053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287753669726953416303723797 13488453268450941389237053)
              ·
                refine ⟨5058169975669103020963895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13488453268450941389237053 5058169975669103020963895)
                ·
                  refine ⟨7587254963503654531445843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058169975669103020963895 7587254963503654531445843)
                  ·
                    refine ⟨11380882445255481797168765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7587254963503654531445843 11380882445255481797168765)
                    ·
                      refine ⟨4267830916970805673938287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11380882445255481797168765 4267830916970805673938287)
                      ·
                        rfl

theorem cell23_8311571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 1, 3].length) (baseStart_8311571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311571 prefixEnd_8311571 := by exact prefixLift 8311571
  have htrace : WordTrace (prefixWord ++ tailWord_8311571) baseStart_8311571 baseEnd_8311571 := by
    simpa [prefixWord, tailWord_8311571, baseEnd_8311571] using wordTrace_append hprefix tailTrace_8311571
  have hstable : (prefixWord ++ tailWord_8311571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311571).length < 2 ^ (prefixWord ++ tailWord_8311571).sum := by decide
  have hdescent : baseEnd_8311571 < baseStart_8311571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311678 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_8311678 : Nat := 118140960795 + 8311678 * 2 ^ 59
def prefixEnd_8311678 : Nat := 4983230072969 + 3 ^ 40 * 8311678 * 2
def baseEnd_8311678 : Nat := 4267885859400836755300295

theorem tailTrace_8311678 : CollatzResearch.WordTrace tailWord_8311678 prefixEnd_8311678 4267885859400836755300295 := by
  unfold tailWord_8311678
  simp only [CollatzResearch.WordTrace]
  refine ⟨37893975197777200304202961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202101201054811734955749125 37893975197777200304202961)
  ·
    refine ⟨28420481398332900228152221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37893975197777200304202961 28420481398332900228152221)
    ·
      refine ⟨10657680524374837585557083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28420481398332900228152221 10657680524374837585557083)
      ·
        refine ⟨15986520786562256378335625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657680524374837585557083 15986520786562256378335625)
        ·
          refine ⟨11989890589921692283751719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15986520786562256378335625 11989890589921692283751719)
          ·
            refine ⟨17984835884882538425627579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11989890589921692283751719 17984835884882538425627579)
            ·
              refine ⟨26977253827323807638441369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17984835884882538425627579 26977253827323807638441369)
              ·
                refine ⟨20232940370492855728831027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26977253827323807638441369 20232940370492855728831027)
                ·
                  refine ⟨30349410555739283593246541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20232940370492855728831027 30349410555739283593246541)
                  ·
                    refine ⟨11381028958402231347467453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30349410555739283593246541 11381028958402231347467453)
                    ·
                      refine ⟨4267885859400836755300295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11381028958402231347467453 4267885859400836755300295)
                      ·
                        rfl

theorem cell23_8311678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_8311678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311678 prefixEnd_8311678 := by exact prefixLift 8311678
  have htrace : WordTrace (prefixWord ++ tailWord_8311678) baseStart_8311678 baseEnd_8311678 := by
    simpa [prefixWord, tailWord_8311678, baseEnd_8311678] using wordTrace_append hprefix tailTrace_8311678
  have hstable : (prefixWord ++ tailWord_8311678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311678).length < 2 ^ (prefixWord ++ tailWord_8311678).sum := by decide
  have hdescent : baseEnd_8311678 < baseStart_8311678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311682 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_8311682 : Nat := 118140960795 + 8311682 * 2 ^ 59
def prefixEnd_8311682 : Nat := 4983230072969 + 3 ^ 40 * 8311682 * 2
def baseEnd_8311682 : Nat := 4267887913323454739650277

theorem tailTrace_8311682 : CollatzResearch.WordTrace tailWord_8311682 prefixEnd_8311682 4267887913323454739650277 := by
  unfold tailWord_8311682
  simp only [CollatzResearch.WordTrace]
  refine ⟨75787986868550777779192325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202101298316135407411179533 75787986868550777779192325)
  ·
    refine ⟨14210247537853270833598561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75787986868550777779192325 14210247537853270833598561)
    ·
      refine ⟨10657685653389953125198921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14210247537853270833598561 10657685653389953125198921)
      ·
        refine ⟨7993264240042464843899191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10657685653389953125198921 7993264240042464843899191)
        ·
          refine ⟨11989896360063697265848787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993264240042464843899191 11989896360063697265848787)
          ·
            refine ⟨17984844540095545898773181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11989896360063697265848787 17984844540095545898773181)
            ·
              refine ⟨6744316702535829712039943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17984844540095545898773181 6744316702535829712039943)
              ·
                refine ⟨10116475053803744568059915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6744316702535829712039943 10116475053803744568059915)
                ·
                  refine ⟨15174712580705616852089873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10116475053803744568059915 15174712580705616852089873)
                  ·
                    refine ⟨11381034435529212639067405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15174712580705616852089873 11381034435529212639067405)
                    ·
                      refine ⟨4267887913323454739650277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11381034435529212639067405 4267887913323454739650277)
                      ·
                        rfl

theorem cell23_8311682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_8311682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311682 prefixEnd_8311682 := by exact prefixLift 8311682
  have htrace : WordTrace (prefixWord ++ tailWord_8311682) baseStart_8311682 baseEnd_8311682 := by
    simpa [prefixWord, tailWord_8311682, baseEnd_8311682] using wordTrace_append hprefix tailTrace_8311682
  have hstable : (prefixWord ++ tailWord_8311682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311682).length < 2 ^ (prefixWord ++ tailWord_8311682).sum := by decide
  have hdescent : baseEnd_8311682 < baseStart_8311682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311697 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_8311697 : Nat := 118140960795 + 8311697 * 2 ^ 59
def prefixEnd_8311697 : Nat := 4983230072969 + 3 ^ 40 * 8311697 * 2
def baseEnd_8311697 : Nat := 4267895615533272180962707

theorem tailTrace_8311697 : CollatzResearch.WordTrace tailWord_8311697 prefixEnd_8311697 4267895615533272180962707 := by
  unfold tailWord_8311697
  simp only [CollatzResearch.WordTrace]
  refine ⟨303152494569148768678565345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202101663046099179119043563 303152494569148768678565345)
  ·
    refine ⟨227364370926861576508924009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303152494569148768678565345 227364370926861576508924009)
    ·
      refine ⟨170523278195146182381693007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227364370926861576508924009 170523278195146182381693007)
      ·
        refine ⟨255784917292719273572539511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170523278195146182381693007 255784917292719273572539511)
        ·
          refine ⟨383677375939078910358809267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255784917292719273572539511 383677375939078910358809267)
          ·
            refine ⟨575516063908618365538213901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383677375939078910358809267 575516063908618365538213901)
            ·
              refine ⟨215818523965731887076830213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575516063908618365538213901 215818523965731887076830213)
              ·
                refine ⟨40465973243574728826905665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215818523965731887076830213 40465973243574728826905665)
                ·
                  refine ⟨30349479932681046620179249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40465973243574728826905665 30349479932681046620179249)
                  ·
                    refine ⟨22762109949510784965134437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30349479932681046620179249 22762109949510784965134437)
                    ·
                      refine ⟨4267895615533272180962707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22762109949510784965134437 4267895615533272180962707)
                      ·
                        rfl

theorem cell23_8311697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_8311697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311697 prefixEnd_8311697 := by exact prefixLift 8311697
  have htrace : WordTrace (prefixWord ++ tailWord_8311697) baseStart_8311697 baseEnd_8311697 := by
    simpa [prefixWord, tailWord_8311697, baseEnd_8311697] using wordTrace_append hprefix tailTrace_8311697
  have hstable : (prefixWord ++ tailWord_8311697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311697).length < 2 ^ (prefixWord ++ tailWord_8311697).sum := by decide
  have hdescent : baseEnd_8311697 < baseStart_8311697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311714 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_8311714 : Nat := 118140960795 + 8311714 * 2 ^ 59
def prefixEnd_8311714 : Nat := 4983230072969 + 3 ^ 40 * 8311714 * 2
def baseEnd_8311714 : Nat := 4267904344704398614450129

theorem tailTrace_8311714 : CollatzResearch.WordTrace tailWord_8311714 prefixEnd_8311714 4267904344704398614450129 := by
  unfold tailWord_8311714
  simp only [CollatzResearch.WordTrace]
  refine ⟨75788278652521795145483549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202102076406724787054622797 75788278652521795145483549)
  ·
    refine ⟨28420604494695673179556331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75788278652521795145483549 28420604494695673179556331)
    ·
      refine ⟨42630906742043509769334497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28420604494695673179556331 42630906742043509769334497)
      ·
        refine ⟨31973180056532632327000873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42630906742043509769334497 31973180056532632327000873)
        ·
          refine ⟨23979885042399474245250655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31973180056532632327000873 23979885042399474245250655)
          ·
            refine ⟨35969827563599211367875983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23979885042399474245250655 35969827563599211367875983)
            ·
              refine ⟨53954741345398817051813975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35969827563599211367875983 53954741345398817051813975)
              ·
                refine ⟨80932112018098225577720963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53954741345398817051813975 80932112018098225577720963)
                ·
                  refine ⟨121398168027147338366581445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80932112018098225577720963 121398168027147338366581445)
                  ·
                    refine ⟨22762156505090125943734021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121398168027147338366581445 22762156505090125943734021)
                    ·
                      refine ⟨4267904344704398614450129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22762156505090125943734021 4267904344704398614450129)
                      ·
                        rfl

theorem cell23_8311714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_8311714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311714 prefixEnd_8311714 := by exact prefixLift 8311714
  have htrace : WordTrace (prefixWord ++ tailWord_8311714) baseStart_8311714 baseEnd_8311714 := by
    simpa [prefixWord, tailWord_8311714, baseEnd_8311714] using wordTrace_append hprefix tailTrace_8311714
  have hstable : (prefixWord ++ tailWord_8311714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311714).length < 2 ^ (prefixWord ++ tailWord_8311714).sum := by decide
  have hdescent : baseEnd_8311714 < baseStart_8311714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311752 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_8311752 : Nat := 118140960795 + 8311752 * 2 ^ 59
def prefixEnd_8311752 : Nat := 4983230072969 + 3 ^ 40 * 8311752 * 2
def baseEnd_8311752 : Nat := 4267923856969269465774955

theorem tailTrace_8311752 : CollatzResearch.WordTrace tailWord_8311752 prefixEnd_8311752 4267923856969269465774955 := by
  unfold tailWord_8311752
  simp only [CollatzResearch.WordTrace]
  refine ⟨151577250291974756535908755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202103000389299675381211673 151577250291974756535908755)
  ·
    refine ⟨227365875437962134803863133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151577250291974756535908755 227365875437962134803863133)
    ·
      refine ⟨85262203289235800551448675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227365875437962134803863133 85262203289235800551448675)
      ·
        refine ⟨127893304933853700827173013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85262203289235800551448675 127893304933853700827173013)
        ·
          refine ⟨5994998668774392226273735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127893304933853700827173013 5994998668774392226273735)
          ·
            refine ⟨8992498003161588339410603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994998668774392226273735 8992498003161588339410603)
            ·
              refine ⟨13488747004742382509115905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992498003161588339410603 13488747004742382509115905)
              ·
                refine ⟨10116560253556786881836929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13488747004742382509115905 10116560253556786881836929)
                ·
                  refine ⟨7587420190167590161377697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10116560253556786881836929 7587420190167590161377697)
                  ·
                    refine ⟨5690565142625692621033273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7587420190167590161377697 5690565142625692621033273)
                    ·
                      refine ⟨4267923856969269465774955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690565142625692621033273 4267923856969269465774955)
                      ·
                        rfl

theorem cell23_8311752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_8311752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311752 prefixEnd_8311752 := by exact prefixLift 8311752
  have htrace : WordTrace (prefixWord ++ tailWord_8311752) baseStart_8311752 baseEnd_8311752 := by
    simpa [prefixWord, tailWord_8311752, baseEnd_8311752] using wordTrace_append hprefix tailTrace_8311752
  have hstable : (prefixWord ++ tailWord_8311752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311752).length < 2 ^ (prefixWord ++ tailWord_8311752).sum := by decide
  have hdescent : baseEnd_8311752 < baseStart_8311752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311817 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_8311817 : Nat := 118140960795 + 8311817 * 2 ^ 59
def prefixEnd_8311817 : Nat := 4983230072969 + 3 ^ 40 * 8311817 * 2
def baseEnd_8311817 : Nat := 4267957233211811711462155

theorem tailTrace_8311817 : CollatzResearch.WordTrace tailWord_8311817 prefixEnd_8311817 4267957233211811711462155 := by
  unfold tailWord_8311817
  simp only [CollatzResearch.WordTrace]
  refine ⟨303156871328714029172933705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202104580885809352781955803 303156871328714029172933705)
  ·
    refine ⟨227367653496535521879700279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303156871328714029172933705 227367653496535521879700279)
    ·
      refine ⟨341051480244803282819550419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227367653496535521879700279 341051480244803282819550419)
      ·
        refine ⟨511577220367204924229325629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341051480244803282819550419 511577220367204924229325629)
        ·
          refine ⟨191841457637701846585997111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511577220367204924229325629 191841457637701846585997111)
          ·
            refine ⟨287762186456552769878995667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191841457637701846585997111 287762186456552769878995667)
            ·
              refine ⟨431643279684829154818493501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287762186456552769878995667 431643279684829154818493501)
              ·
                refine ⟨161866229881810933056935063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431643279684829154818493501 161866229881810933056935063)
                ·
                  refine ⟨242799344822716399585402595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161866229881810933056935063 242799344822716399585402595)
                  ·
                    refine ⟨364199017234074599378103893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242799344822716399585402595 364199017234074599378103893)
                    ·
                      refine ⟨4267957233211811711462155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 364199017234074599378103893 4267957233211811711462155)
                      ·
                        rfl

theorem cell23_8311817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_8311817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311817 prefixEnd_8311817 := by exact prefixLift 8311817
  have htrace : WordTrace (prefixWord ++ tailWord_8311817) baseStart_8311817 baseEnd_8311817 := by
    simpa [prefixWord, tailWord_8311817, baseEnd_8311817] using wordTrace_append hprefix tailTrace_8311817
  have hstable : (prefixWord ++ tailWord_8311817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311817).length < 2 ^ (prefixWord ++ tailWord_8311817).sum := by decide
  have hdescent : baseEnd_8311817 < baseStart_8311817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311818 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_8311818 : Nat := 118140960795 + 8311818 * 2 ^ 59
def prefixEnd_8311818 : Nat := 4983230072969 + 3 ^ 40 * 8311818 * 2
def baseEnd_8311818 : Nat := 1422652582230822069183217

theorem tailTrace_8311818 : CollatzResearch.WordTrace tailWord_8311818 prefixEnd_8311818 1422652582230822069183217 := by
  unfold tailWord_8311818
  simp only [CollatzResearch.WordTrace]
  refine ⟨75789226950427601585930027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202104605201140270895813405 75789226950427601585930027)
  ·
    refine ⟨113683840425641402378895041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75789226950427601585930027 113683840425641402378895041)
    ·
      refine ⟨85262880319231051784171281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113683840425641402378895041 85262880319231051784171281)
      ·
        refine ⟨63947160239423288838128461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85262880319231051784171281 63947160239423288838128461)
        ·
          refine ⟨23980185089783733314298173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63947160239423288838128461 23980185089783733314298173)
          ·
            refine ⟨8992569408668899992861815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23980185089783733314298173 8992569408668899992861815)
            ·
              refine ⟨13488854113003349989292723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992569408668899992861815 13488854113003349989292723)
              ·
                refine ⟨20233281169505024983939085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13488854113003349989292723 20233281169505024983939085)
                ·
                  refine ⟨7587480438564384368977157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20233281169505024983939085 7587480438564384368977157)
                  ·
                    refine ⟨1422652582230822069183217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7587480438564384368977157 1422652582230822069183217)
                    ·
                      rfl

theorem cell23_8311818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_8311818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311818 prefixEnd_8311818 := by exact prefixLift 8311818
  have htrace : WordTrace (prefixWord ++ tailWord_8311818) baseStart_8311818 baseEnd_8311818 := by
    simpa [prefixWord, tailWord_8311818, baseEnd_8311818] using wordTrace_append hprefix tailTrace_8311818
  have hstable : (prefixWord ++ tailWord_8311818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311818).length < 2 ^ (prefixWord ++ tailWord_8311818).sum := by decide
  have hdescent : baseEnd_8311818 < baseStart_8311818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311827 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 9]
def baseStart_8311827 : Nat := 118140960795 + 8311827 * 2 ^ 59
def prefixEnd_8311827 : Nat := 4983230072969 + 3 ^ 40 * 8311827 * 2
def baseEnd_8311827 : Nat := 1422654122672785557445703

theorem tailTrace_8311827 : CollatzResearch.WordTrace tailWord_8311827 prefixEnd_8311827 1422654122672785557445703 := by
  unfold tailWord_8311827
  simp only [CollatzResearch.WordTrace]
  refine ⟨303157236058677800880797735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202104824039118533920531823 303157236058677800880797735)
  ·
    refine ⟨454735854088016701321196603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303157236058677800880797735 454735854088016701321196603)
    ·
      refine ⟨682103781132025051981794905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454735854088016701321196603 682103781132025051981794905)
      ·
        refine ⟨511577835849018788986346179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682103781132025051981794905 511577835849018788986346179)
        ·
          refine ⟨767366753773528183479519269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511577835849018788986346179 767366753773528183479519269)
          ·
            refine ⟨143881266332536534402409863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 767366753773528183479519269 143881266332536534402409863)
            ·
              refine ⟨215821899498804801603614795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143881266332536534402409863 215821899498804801603614795)
              ·
                refine ⟨323732849248207202405422193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215821899498804801603614795 323732849248207202405422193)
                ·
                  refine ⟨242799636936155401804066645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323732849248207202405422193 242799636936155401804066645)
                  ·
                    refine ⟨1422654122672785557445703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 242799636936155401804066645 1422654122672785557445703)
                    ·
                      rfl

theorem cell23_8311827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_8311827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311827 prefixEnd_8311827 := by exact prefixLift 8311827
  have htrace : WordTrace (prefixWord ++ tailWord_8311827) baseStart_8311827 baseEnd_8311827 := by
    simpa [prefixWord, tailWord_8311827, baseEnd_8311827] using wordTrace_append hprefix tailTrace_8311827
  have hstable : (prefixWord ++ tailWord_8311827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311827).length < 2 ^ (prefixWord ++ tailWord_8311827).sum := by decide
  have hdescent : baseEnd_8311827 < baseStart_8311827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311831 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 6]
def baseStart_8311831 : Nat := 118140960795 + 8311831 * 2 ^ 59
def prefixEnd_8311831 : Nat := 4983230072969 + 3 ^ 40 * 8311831 * 2
def baseEnd_8311831 : Nat := 474218269104552739631899

theorem tailTrace_8311831 : CollatzResearch.WordTrace tailWord_8311831 prefixEnd_8311831 474218269104552739631899 := by
  unfold tailWord_8311831
  simp only [CollatzResearch.WordTrace]
  refine ⟨303157381950663309563943347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202104921300442206375962231 303157381950663309563943347)
  ·
    refine ⟨454736072925994964345915021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303157381950663309563943347 454736072925994964345915021)
    ·
      refine ⟨170526027347248111629718133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454736072925994964345915021 170526027347248111629718133)
      ·
        refine ⟨15986815063804510465286075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170526027347248111629718133 15986815063804510465286075)
        ·
          refine ⟨23980222595706765697929113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986815063804510465286075 23980222595706765697929113)
          ·
            refine ⟨17985166946780074273446835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23980222595706765697929113 17985166946780074273446835)
            ·
              refine ⟨26977750420170111410170253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17985166946780074273446835 26977750420170111410170253)
              ·
                refine ⟨10116656407563791778813845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26977750420170111410170253 10116656407563791778813845)
                ·
                  refine ⟨474218269104552739631899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10116656407563791778813845 474218269104552739631899)
                  ·
                    rfl

theorem cell23_8311831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 6].length) (baseStart_8311831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311831 prefixEnd_8311831 := by exact prefixLift 8311831
  have htrace : WordTrace (prefixWord ++ tailWord_8311831) baseStart_8311831 baseEnd_8311831 := by
    simpa [prefixWord, tailWord_8311831, baseEnd_8311831] using wordTrace_append hprefix tailTrace_8311831
  have hstable : (prefixWord ++ tailWord_8311831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311831).length < 2 ^ (prefixWord ++ tailWord_8311831).sum := by decide
  have hdescent : baseEnd_8311831 < baseStart_8311831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311868 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_8311868 : Nat := 118140960795 + 8311868 * 2 ^ 59
def prefixEnd_8311868 : Nat := 4983230072969 + 3 ^ 40 * 8311868 * 2
def baseEnd_8311868 : Nat := 4267983420725191011924421

theorem tailTrace_8311868 : CollatzResearch.WordTrace tailWord_8311868 prefixEnd_8311868 4267983420725191011924421 := by
  unfold tailWord_8311868
  simp only [CollatzResearch.WordTrace]
  refine ⟨151579365725764632441520129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202105820967686176588693505 151579365725764632441520129)
  ·
    refine ⟨113684524294323474331140097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151579365725764632441520129 113684524294323474331140097)
    ·
      refine ⟨85263393220742605748355073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113684524294323474331140097 85263393220742605748355073)
      ·
        refine ⟨63947544915556954311266305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85263393220742605748355073 63947544915556954311266305)
        ·
          refine ⟨47960658686667715733449729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63947544915556954311266305 47960658686667715733449729)
          ·
            refine ⟨35970494015000786800087297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47960658686667715733449729 35970494015000786800087297)
            ·
              refine ⟨26977870511250590100065473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35970494015000786800087297 26977870511250590100065473)
              ·
                refine ⟨20233402883437942575049105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26977870511250590100065473 20233402883437942575049105)
                ·
                  refine ⟨15175052162578456931286829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20233402883437942575049105 15175052162578456931286829)
                  ·
                    refine ⟨5690644560966921349232561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15175052162578456931286829 5690644560966921349232561)
                    ·
                      refine ⟨4267983420725191011924421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690644560966921349232561 4267983420725191011924421)
                      ·
                        rfl

theorem cell23_8311868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_8311868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311868 prefixEnd_8311868 := by exact prefixLift 8311868
  have htrace : WordTrace (prefixWord ++ tailWord_8311868) baseStart_8311868 baseEnd_8311868 := by
    simpa [prefixWord, tailWord_8311868, baseEnd_8311868] using wordTrace_append hprefix tailTrace_8311868
  have hstable : (prefixWord ++ tailWord_8311868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311868).length < 2 ^ (prefixWord ++ tailWord_8311868).sum := by decide
  have hdescent : baseEnd_8311868 < baseStart_8311868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311878 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_8311878 : Nat := 118140960795 + 8311878 * 2 ^ 59
def prefixEnd_8311878 : Nat := 4983230072969 + 3 ^ 40 * 8311878 * 2
def baseEnd_8311878 : Nat := 1422662851843911990933125

theorem tailTrace_8311878 : CollatzResearch.WordTrace tailWord_8311878 prefixEnd_8311878 1422662851843911990933125 := by
  unfold tailWord_8311878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9473721755671657393465759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202106064120995357727269525 9473721755671657393465759)
  ·
    refine ⟨14210582633507486090198639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9473721755671657393465759 14210582633507486090198639)
    ·
      refine ⟨21315873950261229135297959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210582633507486090198639 21315873950261229135297959)
      ·
        refine ⟨31973810925391843702946939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21315873950261229135297959 31973810925391843702946939)
        ·
          refine ⟨47960716388087765554420409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31973810925391843702946939 47960716388087765554420409)
          ·
            refine ⟨35970537291065824165815307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47960716388087765554420409 35970537291065824165815307)
            ·
              refine ⟨53955805936598736248722961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35970537291065824165815307 53955805936598736248722961)
              ·
                refine ⟨40466854452449052186542221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53955805936598736248722961 40466854452449052186542221)
                ·
                  refine ⟨15175070419668394569953333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40466854452449052186542221 15175070419668394569953333)
                  ·
                    refine ⟨1422662851843911990933125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15175070419668394569953333 1422662851843911990933125)
                    ·
                      rfl

theorem cell23_8311878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_8311878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311878 prefixEnd_8311878 := by exact prefixLift 8311878
  have htrace : WordTrace (prefixWord ++ tailWord_8311878) baseStart_8311878 baseEnd_8311878 := by
    simpa [prefixWord, tailWord_8311878, baseEnd_8311878] using wordTrace_append hprefix tailTrace_8311878
  have hstable : (prefixWord ++ tailWord_8311878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311878).length < 2 ^ (prefixWord ++ tailWord_8311878).sum := by decide
  have hdescent : baseEnd_8311878 < baseStart_8311878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311884 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_8311884 : Nat := 118140960795 + 8311884 * 2 ^ 59
def prefixEnd_8311884 : Nat := 4983230072969 + 3 ^ 40 * 8311884 * 2
def baseEnd_8311884 : Nat := 4267991636415662949324347

theorem tailTrace_8311884 : CollatzResearch.WordTrace tailWord_8311884 prefixEnd_8311884 4267991636415662949324347 := by
  unfold tailWord_8311884
  simp only [CollatzResearch.WordTrace]
  refine ⟨151579657509735649807811353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202106210012980866410415137 151579657509735649807811353)
  ·
    refine ⟨113684743132301737355858515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151579657509735649807811353 113684743132301737355858515)
    ·
      refine ⟨170527114698452606033787773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113684743132301737355858515 170527114698452606033787773)
      ·
        refine ⟨63947668011919727262670415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170527114698452606033787773 63947668011919727262670415)
        ·
          refine ⟨95921502017879590894005623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63947668011919727262670415 95921502017879590894005623)
          ·
            refine ⟨143882253026819386341008435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95921502017879590894005623 143882253026819386341008435)
            ·
              refine ⟨215823379540229079511512653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143882253026819386341008435 215823379540229079511512653)
              ·
                refine ⟨80933767327585904816817245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215823379540229079511512653 80933767327585904816817245)
                ·
                  refine ⟨30350162747844714306306467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80933767327585904816817245 30350162747844714306306467)
                  ·
                    refine ⟨45525244121767071459459701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30350162747844714306306467 45525244121767071459459701)
                    ·
                      refine ⟨4267991636415662949324347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45525244121767071459459701 4267991636415662949324347)
                      ·
                        rfl

theorem cell23_8311884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_8311884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311884 prefixEnd_8311884 := by exact prefixLift 8311884
  have htrace : WordTrace (prefixWord ++ tailWord_8311884) baseStart_8311884 baseEnd_8311884 := by
    simpa [prefixWord, tailWord_8311884, baseEnd_8311884] using wordTrace_append hprefix tailTrace_8311884
  have hstable : (prefixWord ++ tailWord_8311884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311884).length < 2 ^ (prefixWord ++ tailWord_8311884).sum := by decide
  have hdescent : baseEnd_8311884 < baseStart_8311884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311902 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_8311902 : Nat := 118140960795 + 8311902 * 2 ^ 59
def prefixEnd_8311902 : Nat := 4983230072969 + 3 ^ 40 * 8311902 * 2
def baseEnd_8311902 : Nat := 4268000879067443878899265

theorem tailTrace_8311902 : CollatzResearch.WordTrace tailWord_8311902 prefixEnd_8311902 4268000879067443878899265 := by
  unfold tailWord_8311902
  simp only [CollatzResearch.WordTrace]
  refine ⟨37894996441675761086222245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202106647688937392459851973 37894996441675761086222245)
  ·
    refine ⟨7105311832814205203666671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37894996441675761086222245 7105311832814205203666671)
    ·
      refine ⟨10657967749221307805500007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7105311832814205203666671 10657967749221307805500007)
      ·
        refine ⟨15986951623831961708250011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657967749221307805500007 15986951623831961708250011)
        ·
          refine ⟨23980427435747942562375017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986951623831961708250011 23980427435747942562375017)
          ·
            refine ⟨17985320576810956921781263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23980427435747942562375017 17985320576810956921781263)
            ·
              refine ⟨26977980865216435382671895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17985320576810956921781263 26977980865216435382671895)
              ·
                refine ⟨40466971297824653074007843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26977980865216435382671895 40466971297824653074007843)
                ·
                  refine ⟨60700456946736979611011765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40466971297824653074007843 60700456946736979611011765)
                  ·
                    refine ⟨5690667838756591838532353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60700456946736979611011765 5690667838756591838532353)
                    ·
                      refine ⟨4268000879067443878899265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690667838756591838532353 4268000879067443878899265)
                      ·
                        rfl

theorem cell23_8311902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_8311902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311902 prefixEnd_8311902 := by exact prefixLift 8311902
  have htrace : WordTrace (prefixWord ++ tailWord_8311902) baseStart_8311902 baseEnd_8311902 := by
    simpa [prefixWord, tailWord_8311902, baseEnd_8311902] using wordTrace_append hprefix tailTrace_8311902
  have hstable : (prefixWord ++ tailWord_8311902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311902).length < 2 ^ (prefixWord ++ tailWord_8311902).sum := by decide
  have hdescent : baseEnd_8311902 < baseStart_8311902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311911 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_8311911 : Nat := 118140960795 + 8311911 * 2 ^ 59
def prefixEnd_8311911 : Nat := 4983230072969 + 3 ^ 40 * 8311911 * 2
def baseEnd_8311911 : Nat := 4268005500393334343686723

theorem tailTrace_8311911 : CollatzResearch.WordTrace tailWord_8311911 prefixEnd_8311911 4268005500393334343686723 := by
  unfold tailWord_8311911
  simp only [CollatzResearch.WordTrace]
  refine ⟨303160299790373483226855587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202106866526915655484570391 303160299790373483226855587)
  ·
    refine ⟨454740449685560224840283381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303160299790373483226855587 454740449685560224840283381)
    ·
      refine ⟨42631917158021271078776567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454740449685560224840283381 42631917158021271078776567)
      ·
        refine ⟨63947875737031906618164851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42631917158021271078776567 63947875737031906618164851)
        ·
          refine ⟨95921813605547859927247277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63947875737031906618164851 95921813605547859927247277)
          ·
            refine ⟨35970680102080447472717729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95921813605547859927247277 35970680102080447472717729)
            ·
              refine ⟨26978010076560335604538297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35970680102080447472717729 26978010076560335604538297)
              ·
                refine ⟨20233507557420251703403723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26978010076560335604538297 20233507557420251703403723)
                ·
                  refine ⟨30350261336130377555105585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20233507557420251703403723 30350261336130377555105585)
                  ·
                    refine ⟨22762696002097783166329189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30350261336130377555105585 22762696002097783166329189)
                    ·
                      refine ⟨4268005500393334343686723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22762696002097783166329189 4268005500393334343686723)
                      ·
                        rfl

theorem cell23_8311911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_8311911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311911 prefixEnd_8311911 := by exact prefixLift 8311911
  have htrace : WordTrace (prefixWord ++ tailWord_8311911) baseStart_8311911 baseEnd_8311911 := by
    simpa [prefixWord, tailWord_8311911, baseEnd_8311911] using wordTrace_append hprefix tailTrace_8311911
  have hstable : (prefixWord ++ tailWord_8311911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311911).length < 2 ^ (prefixWord ++ tailWord_8311911).sum := by decide
  have hdescent : baseEnd_8311911 < baseStart_8311911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311912 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 1, 5]
def baseStart_8311912 : Nat := 118140960795 + 8311912 * 2 ^ 59
def prefixEnd_8311912 : Nat := 4983230072969 + 3 ^ 40 * 8311912 * 2
def baseEnd_8311912 : Nat := 1422668671291329613258073

theorem tailTrace_8311912 : CollatzResearch.WordTrace tailWord_8311912 prefixEnd_8311912 1422668671291329613258073 := by
  unfold tailWord_8311912
  simp only [CollatzResearch.WordTrace]
  refine ⟨151580168131684930198820995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202106890842246573598427993 151580168131684930198820995)
  ·
    refine ⟨227370252197527395298231493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151580168131684930198820995 227370252197527395298231493)
    ·
      refine ⟨42631922287036386618418405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227370252197527395298231493 42631922287036386618418405)
      ·
        refine ⟨7993485428819322490953451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42631922287036386618418405 7993485428819322490953451)
        ·
          refine ⟨11990228143228983736430177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993485428819322490953451 11990228143228983736430177)
          ·
            refine ⟨8992671107421737802322633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11990228143228983736430177 8992671107421737802322633)
            ·
              refine ⟨6744503330566303351741975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992671107421737802322633 6744503330566303351741975)
              ·
                refine ⟨10116754995849455027612963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6744503330566303351741975 10116754995849455027612963)
                ·
                  refine ⟨15175132493774182541419445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10116754995849455027612963 15175132493774182541419445)
                  ·
                    refine ⟨1422668671291329613258073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15175132493774182541419445 1422668671291329613258073)
                    ·
                      rfl

theorem cell23_8311912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_8311912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311912 prefixEnd_8311912 := by exact prefixLift 8311912
  have htrace : WordTrace (prefixWord ++ tailWord_8311912) baseStart_8311912 baseEnd_8311912 := by
    simpa [prefixWord, tailWord_8311912, baseEnd_8311912] using wordTrace_append hprefix tailTrace_8311912
  have hstable : (prefixWord ++ tailWord_8311912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311912).length < 2 ^ (prefixWord ++ tailWord_8311912).sum := by decide
  have hdescent : baseEnd_8311912 < baseStart_8311912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311925 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_8311925 : Nat := 118140960795 + 8311925 * 2 ^ 59
def prefixEnd_8311925 : Nat := 4983230072969 + 3 ^ 40 * 8311925 * 2
def baseEnd_8311925 : Nat := 1422670896374165762970553

theorem tailTrace_8311925 : CollatzResearch.WordTrace tailWord_8311925 prefixEnd_8311925 1422670896374165762970553 := by
  unfold tailWord_8311925
  simp only [CollatzResearch.WordTrace]
  refine ⟨303160810412322763617865229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202107206941548509078576819 303160810412322763617865229)
  ·
    refine ⟨113685303904621036356699461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303160810412322763617865229 113685303904621036356699461)
    ·
      refine ⟨21315994482116444316881149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113685303904621036356699461 21315994482116444316881149)
      ·
        refine ⟨7993497930793666618830431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21315994482116444316881149 7993497930793666618830431)
        ·
          refine ⟨11990246896190499928245647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993497930793666618830431 11990246896190499928245647)
          ·
            refine ⟨17985370344285749892368471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990246896190499928245647 17985370344285749892368471)
            ·
              refine ⟨26978055516428624838552707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17985370344285749892368471 26978055516428624838552707)
              ·
                refine ⟨40467083274642937257829061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26978055516428624838552707 40467083274642937257829061)
                ·
                  refine ⟨7587578113995550735842949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40467083274642937257829061 7587578113995550735842949)
                  ·
                    refine ⟨1422670896374165762970553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7587578113995550735842949 1422670896374165762970553)
                    ·
                      rfl

theorem cell23_8311925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_8311925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311925 prefixEnd_8311925 := by exact prefixLift 8311925
  have htrace : WordTrace (prefixWord ++ tailWord_8311925) baseStart_8311925 baseEnd_8311925 := by
    simpa [prefixWord, tailWord_8311925, baseEnd_8311925] using wordTrace_append hprefix tailTrace_8311925
  have hstable : (prefixWord ++ tailWord_8311925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311925).length < 2 ^ (prefixWord ++ tailWord_8311925).sum := by decide
  have hdescent : baseEnd_8311925 < baseStart_8311925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311948 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_8311948 : Nat := 118140960795 + 8311948 * 2 ^ 59
def prefixEnd_8311948 : Nat := 4983230072969 + 3 ^ 40 * 8311948 * 2
def baseEnd_8311948 : Nat := 4268024499177550698924053

theorem tailTrace_8311948 : CollatzResearch.WordTrace tailWord_8311948 prefixEnd_8311948 4268024499177550698924053 := by
  unfold tailWord_8311948
  simp only [CollatzResearch.WordTrace]
  refine ⟨151580824645619719272976249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202107766194159625697301665 151580824645619719272976249)
  ·
    refine ⟨113685618484214789454732187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151580824645619719272976249 113685618484214789454732187)
    ·
      refine ⟨170528427726322184182098281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113685618484214789454732187 170528427726322184182098281)
      ·
        refine ⟨127896320794741638136573711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170528427726322184182098281 127896320794741638136573711)
        ·
          refine ⟨191844481192112457204860567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127896320794741638136573711 191844481192112457204860567)
          ·
            refine ⟨287766721788168685807290851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191844481192112457204860567 287766721788168685807290851)
            ·
              refine ⟨431650082682253028710936277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287766721788168685807290851 431650082682253028710936277)
              ·
                refine ⟨10116798812865305360412569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431650082682253028710936277 10116798812865305360412569)
                ·
                  refine ⟨7587599109648979020309427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10116798812865305360412569 7587599109648979020309427)
                  ·
                    refine ⟨11381398664473468530464141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7587599109648979020309427 11381398664473468530464141)
                    ·
                      refine ⟨4268024499177550698924053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11381398664473468530464141 4268024499177550698924053)
                      ·
                        rfl

theorem cell23_8311948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_8311948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311948 prefixEnd_8311948 := by exact prefixLift 8311948
  have htrace : WordTrace (prefixWord ++ tailWord_8311948) baseStart_8311948 baseEnd_8311948 := by
    simpa [prefixWord, tailWord_8311948, baseEnd_8311948] using wordTrace_append hprefix tailTrace_8311948
  have hstable : (prefixWord ++ tailWord_8311948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311948).length < 2 ^ (prefixWord ++ tailWord_8311948).sum := by decide
  have hdescent : baseEnd_8311948 < baseStart_8311948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311966 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_8311966 : Nat := 118140960795 + 8311966 * 2 ^ 59
def prefixEnd_8311966 : Nat := 4983230072969 + 3 ^ 40 * 8311966 * 2
def baseEnd_8311966 : Nat := 4268033741829331628498971

theorem tailTrace_8311966 : CollatzResearch.WordTrace tailWord_8311966 prefixEnd_8311966 4268033741829331628498971 := by
  unfold tailWord_8311966
  simp only [CollatzResearch.WordTrace]
  refine ⟨37895288225646778452513469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202108203870116151746738501 37895288225646778452513469)
  ·
    refine ⟨14210733084617541919692551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37895288225646778452513469 14210733084617541919692551)
    ·
      refine ⟨21316099626926312879538827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210733084617541919692551 21316099626926312879538827)
      ·
        refine ⟨31974149440389469319308241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21316099626926312879538827 31974149440389469319308241)
        ·
          refine ⟨23980612080292101989481181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31974149440389469319308241 23980612080292101989481181)
          ·
            refine ⟨8992729530109538246055443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23980612080292101989481181 8992729530109538246055443)
            ·
              refine ⟨13489094295164307369083165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992729530109538246055443 13489094295164307369083165)
              ·
                refine ⟨5058410360686615263406187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13489094295164307369083165 5058410360686615263406187)
                ·
                  refine ⟨7587615541029922895109281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058410360686615263406187 7587615541029922895109281)
                  ·
                    refine ⟨5690711655772442171331961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7587615541029922895109281 5690711655772442171331961)
                    ·
                      refine ⟨4268033741829331628498971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690711655772442171331961 4268033741829331628498971)
                      ·
                        rfl

theorem cell23_8311966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_8311966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311966 prefixEnd_8311966 := by exact prefixLift 8311966
  have htrace : WordTrace (prefixWord ++ tailWord_8311966) baseStart_8311966 baseEnd_8311966 := by
    simpa [prefixWord, tailWord_8311966, baseEnd_8311966] using wordTrace_append hprefix tailTrace_8311966
  have hstable : (prefixWord ++ tailWord_8311966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311966).length < 2 ^ (prefixWord ++ tailWord_8311966).sum := by decide
  have hdescent : baseEnd_8311966 < baseStart_8311966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8311991 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_8311991 : Nat := 118140960795 + 8311991 * 2 ^ 59
def prefixEnd_8311991 : Nat := 4983230072969 + 3 ^ 40 * 8311991 * 2
def baseEnd_8311991 : Nat := 4268046578845694030686355

theorem tailTrace_8311991 : CollatzResearch.WordTrace tailWord_8311991 prefixEnd_8311991 4268046578845694030686355 := by
  unfold tailWord_8311991
  simp only [CollatzResearch.WordTrace]
  refine ⟨303163217630083656889767827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202108811753389104593178551 303163217630083656889767827)
  ·
    refine ⟨454744826445125485334651741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303163217630083656889767827 454744826445125485334651741)
    ·
      refine ⟨170529309916922057000494403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454744826445125485334651741 170529309916922057000494403)
      ·
        refine ⟨255793964875383085500741605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170529309916922057000494403 255793964875383085500741605)
        ·
          refine ⟨47961368414134328531389051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255793964875383085500741605 47961368414134328531389051)
          ·
            refine ⟨71942052621201492797083577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47961368414134328531389051 71942052621201492797083577)
            ·
              refine ⟨53956539465901119597812683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71942052621201492797083577 53956539465901119597812683)
              ·
                refine ⟨80934809198851679396719025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53956539465901119597812683 80934809198851679396719025)
                ·
                  refine ⟨60701106899138759547539269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80934809198851679396719025 60701106899138759547539269)
                  ·
                    refine ⟨11381457543588517415163613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60701106899138759547539269 11381457543588517415163613)
                    ·
                      refine ⟨4268046578845694030686355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11381457543588517415163613 4268046578845694030686355)
                      ·
                        rfl

theorem cell23_8311991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_8311991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8311991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8311991 prefixEnd_8311991 := by exact prefixLift 8311991
  have htrace : WordTrace (prefixWord ++ tailWord_8311991) baseStart_8311991 baseEnd_8311991 := by
    simpa [prefixWord, tailWord_8311991, baseEnd_8311991] using wordTrace_append hprefix tailTrace_8311991
  have hstable : (prefixWord ++ tailWord_8311991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8311991).length < 2 ^ (prefixWord ++ tailWord_8311991).sum := by decide
  have hdescent : baseEnd_8311991 < baseStart_8311991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8311991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312039 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8312039 : Nat := 118140960795 + 8312039 * 2 ^ 59
def prefixEnd_8312039 : Nat := 4983230072969 + 3 ^ 40 * 8312039 * 2
def baseEnd_8312039 : Nat := 4268071225917109842886135

theorem tailTrace_8312039 : CollatzResearch.WordTrace tailWord_8312039 prefixEnd_8312039 4268071225917109842886135 := by
  unfold tailWord_8312039
  simp only [CollatzResearch.WordTrace]
  refine ⟨303164968333909761087515171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202109978889273174058343447 303164968333909761087515171)
  ·
    refine ⟨454747452500864641631272757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303164968333909761087515171 454747452500864641631272757)
    ·
      refine ⟨42632573671956060152931821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454747452500864641631272757 42632573671956060152931821)
      ·
        refine ⟨15987215126983522557349433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42632573671956060152931821 15987215126983522557349433)
        ·
          refine ⟨11990411345237641918012075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15987215126983522557349433 11990411345237641918012075)
          ·
            refine ⟨17985617017856462877018113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990411345237641918012075 17985617017856462877018113)
            ·
              refine ⟨13489212763392347157763585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17985617017856462877018113 13489212763392347157763585)
              ·
                refine ⟨10116909572544260368322689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13489212763392347157763585 10116909572544260368322689)
                ·
                  refine ⟨7587682179408195276242017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10116909572544260368322689 7587682179408195276242017)
                  ·
                    refine ⟨5690761634556146457181513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7587682179408195276242017 5690761634556146457181513)
                    ·
                      refine ⟨4268071225917109842886135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5690761634556146457181513 4268071225917109842886135)
                      ·
                        rfl

theorem cell23_8312039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8312039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312039 prefixEnd_8312039 := by exact prefixLift 8312039
  have htrace : WordTrace (prefixWord ++ tailWord_8312039) baseStart_8312039 baseEnd_8312039 := by
    simpa [prefixWord, tailWord_8312039, baseEnd_8312039] using wordTrace_append hprefix tailTrace_8312039
  have hstable : (prefixWord ++ tailWord_8312039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312039).length < 2 ^ (prefixWord ++ tailWord_8312039).sum := by decide
  have hdescent : baseEnd_8312039 < baseStart_8312039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312045 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 5]
def baseStart_8312045 : Nat := 118140960795 + 8312045 * 2 ^ 59
def prefixEnd_8312045 : Nat := 4983230072969 + 3 ^ 40 * 8312045 * 2
def baseEnd_8312045 : Nat := 474230478533448535490123

theorem tailTrace_8312045 : CollatzResearch.WordTrace tailWord_8312045 prefixEnd_8312045 474230478533448535490123 := by
  unfold tailWord_8312045
  simp only [CollatzResearch.WordTrace]
  refine ⟨303165187171888024112233589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202110124781258682741489059 303165187171888024112233589)
  ·
    refine ⟨28421736297364502260521899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303165187171888024112233589 28421736297364502260521899)
    ·
      refine ⟨42632604446046753390782849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28421736297364502260521899 42632604446046753390782849)
      ·
        refine ⟨31974453334535065043087137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42632604446046753390782849 31974453334535065043087137)
        ·
          refine ⟨23980840000901298782315353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31974453334535065043087137 23980840000901298782315353)
          ·
            refine ⟨17985630000675974086736515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23980840000901298782315353 17985630000675974086736515)
            ·
              refine ⟨26978445001013961130104773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17985630000675974086736515 26978445001013961130104773)
              ·
                refine ⟨5058458437690117711894645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26978445001013961130104773 5058458437690117711894645)
                ·
                  refine ⟨474230478533448535490123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058458437690117711894645 474230478533448535490123)
                  ·
                    rfl

theorem cell23_8312045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_8312045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312045 prefixEnd_8312045 := by exact prefixLift 8312045
  have htrace : WordTrace (prefixWord ++ tailWord_8312045) baseStart_8312045 baseEnd_8312045 := by
    simpa [prefixWord, tailWord_8312045, baseEnd_8312045] using wordTrace_append hprefix tailTrace_8312045
  have hstable : (prefixWord ++ tailWord_8312045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312045).length < 2 ^ (prefixWord ++ tailWord_8312045).sum := by decide
  have hdescent : baseEnd_8312045 < baseStart_8312045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312051 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5]
def baseStart_8312051 : Nat := 118140960795 + 8312051 * 2 ^ 59
def prefixEnd_8312051 : Nat := 4983230072969 + 3 ^ 40 * 8312051 * 2
def baseEnd_8312051 : Nat := 4268077387684963795936079

theorem tailTrace_8312051 : CollatzResearch.WordTrace tailWord_8312051 prefixEnd_8312051 4268077387684963795936079 := by
  unfold tailWord_8312051
  simp only [CollatzResearch.WordTrace]
  refine ⟨303165406009866287136952007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202110270673244191424634671 303165406009866287136952007)
  ·
    refine ⟨454748109014799430705428011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303165406009866287136952007 454748109014799430705428011)
    ·
      refine ⟨682122163522199146058142017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454748109014799430705428011 682122163522199146058142017)
      ·
        refine ⟨511591622641649359543606513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682122163522199146058142017 511591622641649359543606513)
        ·
          refine ⟨383693716981237019657704885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511591622641649359543606513 383693716981237019657704885)
          ·
            refine ⟨35971285966990970592909833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383693716981237019657704885 35971285966990970592909833)
            ·
              refine ⟨26978464475243227944682375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35971285966990970592909833 26978464475243227944682375)
              ·
                refine ⟨40467696712864841917023563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26978464475243227944682375 40467696712864841917023563)
                ·
                  refine ⟨60701545069297262875535345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40467696712864841917023563 60701545069297262875535345)
                  ·
                    refine ⟨45526158801972947156651509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60701545069297262875535345 45526158801972947156651509)
                    ·
                      refine ⟨4268077387684963795936079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45526158801972947156651509 4268077387684963795936079)
                      ·
                        rfl

theorem cell23_8312051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_8312051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312051 prefixEnd_8312051 := by exact prefixLift 8312051
  have htrace : WordTrace (prefixWord ++ tailWord_8312051) baseStart_8312051 baseEnd_8312051 := by
    simpa [prefixWord, tailWord_8312051, baseEnd_8312051] using wordTrace_append hprefix tailTrace_8312051
  have hstable : (prefixWord ++ tailWord_8312051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312051).length < 2 ^ (prefixWord ++ tailWord_8312051).sum := by decide
  have hdescent : baseEnd_8312051 < baseStart_8312051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312078 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_8312078 : Nat := 118140960795 + 8312078 * 2 ^ 59
def prefixEnd_8312078 : Nat := 4983230072969 + 3 ^ 40 * 8312078 * 2
def baseEnd_8312078 : Nat := 4268091251662635190298455

theorem tailTrace_8312078 : CollatzResearch.WordTrace tailWord_8312078 prefixEnd_8312078 4268091251662635190298455 := by
  unfold tailWord_8312078
  simp only [CollatzResearch.WordTrace]
  refine ⟨37895798847596058843523111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202110927187178980498789925 37895798847596058843523111)
  ·
    refine ⟨56843698271394088265284667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37895798847596058843523111 56843698271394088265284667)
    ·
      refine ⟨85265547407091132397927001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56843698271394088265284667 85265547407091132397927001)
      ·
        refine ⟨63949160555318349298445251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85265547407091132397927001 63949160555318349298445251)
        ·
          refine ⟨95923740832977523947667877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63949160555318349298445251 95923740832977523947667877)
          ·
            refine ⟨17985701406183285740187727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95923740832977523947667877 17985701406183285740187727)
            ·
              refine ⟨26978552109274928610281591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17985701406183285740187727 26978552109274928610281591)
              ·
                refine ⟨40467828163912392915422387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26978552109274928610281591 40467828163912392915422387)
                ·
                  refine ⟨60701742245868589373133581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40467828163912392915422387 60701742245868589373133581)
                  ·
                    refine ⟨22763153342200721014925093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60701742245868589373133581 22763153342200721014925093)
                    ·
                      refine ⟨4268091251662635190298455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22763153342200721014925093 4268091251662635190298455)
                      ·
                        rfl

theorem cell23_8312078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_8312078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312078 prefixEnd_8312078 := by exact prefixLift 8312078
  have htrace : WordTrace (prefixWord ++ tailWord_8312078) baseStart_8312078 baseEnd_8312078 := by
    simpa [prefixWord, tailWord_8312078, baseEnd_8312078] using wordTrace_append hprefix tailTrace_8312078
  have hstable : (prefixWord ++ tailWord_8312078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312078).length < 2 ^ (prefixWord ++ tailWord_8312078).sum := by decide
  have hdescent : baseEnd_8312078 < baseStart_8312078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312178 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_8312178 : Nat := 118140960795 + 8312178 * 2 ^ 59
def prefixEnd_8312178 : Nat := 4983230072969 + 3 ^ 40 * 8312178 * 2
def baseEnd_8312178 : Nat := 1422714199909361599682665

theorem tailTrace_8312178 : CollatzResearch.WordTrace tailWord_8312178 prefixEnd_8312178 1422714199909361599682665 := by
  unfold tailWord_8312178
  simp only [CollatzResearch.WordTrace]
  refine ⟨75792509520101546956706297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202113358720270791884550125 75792509520101546956706297)
  ·
    refine ⟨56844382140076160217529723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75792509520101546956706297 56844382140076160217529723)
    ·
      refine ⟨85266573210114240326294585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56844382140076160217529723 85266573210114240326294585)
      ·
        refine ⟨63949929907585680244720939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85266573210114240326294585 63949929907585680244720939)
        ·
          refine ⟨95924894861378520367081409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63949929907585680244720939 95924894861378520367081409)
          ·
            refine ⟨71943671146033890275311057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95924894861378520367081409 71943671146033890275311057)
            ·
              refine ⟨53957753359525417706483293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71943671146033890275311057 53957753359525417706483293)
              ·
                refine ⟨20234157509822031639931235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53957753359525417706483293 20234157509822031639931235)
                ·
                  refine ⟨30351236264733047459896853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20234157509822031639931235 30351236264733047459896853)
                  ·
                    refine ⟨1422714199909361599682665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30351236264733047459896853 1422714199909361599682665)
                    ·
                      rfl

theorem cell23_8312178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_8312178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312178 prefixEnd_8312178 := by exact prefixLift 8312178
  have htrace : WordTrace (prefixWord ++ tailWord_8312178) baseStart_8312178 baseEnd_8312178 := by
    simpa [prefixWord, tailWord_8312178, baseEnd_8312178] using wordTrace_append hprefix tailTrace_8312178
  have hstable : (prefixWord ++ tailWord_8312178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312178).length < 2 ^ (prefixWord ++ tailWord_8312178).sum := by decide
  have hdescent : baseEnd_8312178 < baseStart_8312178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312185 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 4]
def baseStart_8312185 : Nat := 118140960795 + 8312185 * 2 ^ 59
def prefixEnd_8312185 : Nat := 4983230072969 + 3 ^ 40 * 8312185 * 2
def baseEnd_8312185 : Nat := 4268146194092666271660463

theorem tailTrace_8312185 : CollatzResearch.WordTrace tailWord_8312185 prefixEnd_8312185 4268146194092666271660463 := by
  unfold tailWord_8312185
  simp only [CollatzResearch.WordTrace]
  refine ⟨303170293391380828022330009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202113528927587218681553339 303170293391380828022330009)
  ·
    refine ⟨227377720043535621016747507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303170293391380828022330009 227377720043535621016747507)
    ·
      refine ⟨341066580065303431525121261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227377720043535621016747507 341066580065303431525121261)
      ·
        refine ⟨127899967524488786821920473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341066580065303431525121261 127899967524488786821920473)
        ·
          refine ⟨95924975643366590116440355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127899967524488786821920473 95924975643366590116440355)
          ·
            refine ⟨143887463465049885174660533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95924975643366590116440355 143887463465049885174660533)
            ·
              refine ⟨13489449699848426735124425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143887463465049885174660533 13489449699848426735124425)
              ·
                refine ⟨10117087274886320051343319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13489449699848426735124425 10117087274886320051343319)
                ·
                  refine ⟨15175630912329480077014979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10117087274886320051343319 15175630912329480077014979)
                  ·
                    refine ⟨22763446368494220115522469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15175630912329480077014979 22763446368494220115522469)
                    ·
                      refine ⟨4268146194092666271660463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22763446368494220115522469 4268146194092666271660463)
                      ·
                        rfl

theorem cell23_8312185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_8312185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312185 prefixEnd_8312185 := by exact prefixLift 8312185
  have htrace : WordTrace (prefixWord ++ tailWord_8312185) baseStart_8312185 baseEnd_8312185 := by
    simpa [prefixWord, tailWord_8312185, baseEnd_8312185] using wordTrace_append hprefix tailTrace_8312185
  have hstable : (prefixWord ++ tailWord_8312185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312185).length < 2 ^ (prefixWord ++ tailWord_8312185).sum := by decide
  have hdescent : baseEnd_8312185 < baseStart_8312185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312211 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_8312211 : Nat := 118140960795 + 8312211 * 2 ^ 59
def prefixEnd_8312211 : Nat := 4983230072969 + 3 ^ 40 * 8312211 * 2
def baseEnd_8312211 : Nat := 4268159544589683169935343

theorem tailTrace_8312211 : CollatzResearch.WordTrace tailWord_8312211 prefixEnd_8312211 4268159544589683169935343 := by
  unfold tailWord_8312211
  simp only [CollatzResearch.WordTrace]
  refine ⟨303171241689286634462776487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202114161126191089641850991 303171241689286634462776487)
  ·
    refine ⟨454756862533929951694164731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303171241689286634462776487 454756862533929951694164731)
    ·
      refine ⟨682135293800894927541247097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454756862533929951694164731 682135293800894927541247097)
      ·
        refine ⟨511601470350671195655935323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682135293800894927541247097 511601470350671195655935323)
        ·
          refine ⟨767402205526006793483902985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511601470350671195655935323 767402205526006793483902985)
          ·
            refine ⟨575551654144505095112927239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767402205526006793483902985 575551654144505095112927239)
            ·
              refine ⟨863327481216757642669390859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575551654144505095112927239 863327481216757642669390859)
              ·
                refine ⟨1294991221825136464004086289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863327481216757642669390859 1294991221825136464004086289)
                ·
                  refine ⟨971243416368852348003064717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1294991221825136464004086289 971243416368852348003064717)
                  ·
                    refine ⟨364216281138319630501149269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 971243416368852348003064717 364216281138319630501149269)
                    ·
                      refine ⟨4268159544589683169935343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 364216281138319630501149269 4268159544589683169935343)
                      ·
                        rfl

theorem cell23_8312211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_8312211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312211 prefixEnd_8312211 := by exact prefixLift 8312211
  have htrace : WordTrace (prefixWord ++ tailWord_8312211) baseStart_8312211 baseEnd_8312211 := by
    simpa [prefixWord, tailWord_8312211, baseEnd_8312211] using wordTrace_append hprefix tailTrace_8312211
  have hstable : (prefixWord ++ tailWord_8312211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312211).length < 2 ^ (prefixWord ++ tailWord_8312211).sum := by decide
  have hdescent : baseEnd_8312211 < baseStart_8312211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312212 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_8312212 : Nat := 118140960795 + 8312212 * 2 ^ 59
def prefixEnd_8312212 : Nat := 4983230072969 + 3 ^ 40 * 8312212 * 2
def baseEnd_8312212 : Nat := 1422720019356779222007613

theorem tailTrace_8312212 : CollatzResearch.WordTrace tailWord_8312212 prefixEnd_8312212 1422720019356779222007613 := by
  unfold tailWord_8312212
  simp only [CollatzResearch.WordTrace]
  refine ⟨151585639081141505816781445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202114185441522007755708593 151585639081141505816781445)
  ·
    refine ⟨28422307327714032340646521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151585639081141505816781445 28422307327714032340646521)
    ·
      refine ⟨21316730495785524255484891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28422307327714032340646521 21316730495785524255484891)
      ·
        refine ⟨31975095743678286383227337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21316730495785524255484891 31975095743678286383227337)
        ·
          refine ⟨23981321807758714787420503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31975095743678286383227337 23981321807758714787420503)
          ·
            refine ⟨35971982711638072181130755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23981321807758714787420503 35971982711638072181130755)
            ·
              refine ⟨53957974067457108271696133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35971982711638072181130755 53957974067457108271696133)
              ·
                refine ⟨10117120137648207800943025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53957974067457108271696133 10117120137648207800943025)
                ·
                  refine ⟨7587840103236155850707269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10117120137648207800943025 7587840103236155850707269)
                  ·
                    refine ⟨1422720019356779222007613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7587840103236155850707269 1422720019356779222007613)
                    ·
                      rfl

theorem cell23_8312212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_8312212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312212 prefixEnd_8312212 := by exact prefixLift 8312212
  have htrace : WordTrace (prefixWord ++ tailWord_8312212) baseStart_8312212 baseEnd_8312212 := by
    simpa [prefixWord, tailWord_8312212, baseEnd_8312212] using wordTrace_append hprefix tailTrace_8312212
  have hstable : (prefixWord ++ tailWord_8312212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312212).length < 2 ^ (prefixWord ++ tailWord_8312212).sum := by decide
  have hdescent : baseEnd_8312212 < baseStart_8312212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312285 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_8312285 : Nat := 118140960795 + 8312285 * 2 ^ 59
def prefixEnd_8312285 : Nat := 4983230072969 + 3 ^ 40 * 8312285 * 2
def baseEnd_8312285 : Nat := 1422732514052705293470001

theorem tailTrace_8312285 : CollatzResearch.WordTrace tailWord_8312285 prefixEnd_8312285 1422732514052705293470001 := by
  unfold tailWord_8312285
  simp only [CollatzResearch.WordTrace]
  refine ⟨303173940691018545100970309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202115960460679030067313539 303173940691018545100970309)
  ·
    refine ⟨56845113879565977206431933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303173940691018545100970309 56845113879565977206431933)
    ·
      refine ⟨21316917704837241452411975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56845113879565977206431933 21316917704837241452411975)
      ·
        refine ⟨31975376557255862178617963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21316917704837241452411975 31975376557255862178617963)
        ·
          refine ⟨47963064835883793267926945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31975376557255862178617963 47963064835883793267926945)
          ·
            refine ⟨35972298626912844950945209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47963064835883793267926945 35972298626912844950945209)
            ·
              refine ⟨26979223970184633713208907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35972298626912844950945209 26979223970184633713208907)
              ·
                refine ⟨40468835955276950569813361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26979223970184633713208907 40468835955276950569813361)
                ·
                  refine ⟨30351626966457712927360021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40468835955276950569813361 30351626966457712927360021)
                  ·
                    refine ⟨1422732514052705293470001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30351626966457712927360021 1422732514052705293470001)
                    ·
                      rfl

theorem cell23_8312285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_8312285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312285 prefixEnd_8312285 := by exact prefixLift 8312285
  have htrace : WordTrace (prefixWord ++ tailWord_8312285) baseStart_8312285 baseEnd_8312285 := by
    simpa [prefixWord, tailWord_8312285, baseEnd_8312285] using wordTrace_append hprefix tailTrace_8312285
  have hstable : (prefixWord ++ tailWord_8312285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312285).length < 2 ^ (prefixWord ++ tailWord_8312285).sum := by decide
  have hdescent : baseEnd_8312285 < baseStart_8312285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312288 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_8312288 : Nat := 118140960795 + 8312288 * 2 ^ 59
def prefixEnd_8312288 : Nat := 4983230072969 + 3 ^ 40 * 8312288 * 2
def baseEnd_8312288 : Nat := 4268199082600079368672489

theorem tailTrace_8312288 : CollatzResearch.WordTrace tailWord_8312288 prefixEnd_8312288 4268199082600079368672489 := by
  unfold tailWord_8312288
  simp only [CollatzResearch.WordTrace]
  refine ⟨151587025055003838306664759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202116033406671784408886345 151587025055003838306664759)
  ·
    refine ⟨227380537582505757459997139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151587025055003838306664759 227380537582505757459997139)
    ·
      refine ⟨341070806373758636189995709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227380537582505757459997139 341070806373758636189995709)
      ·
        refine ⟨127901552390159488571248391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341070806373758636189995709 127901552390159488571248391)
        ·
          refine ⟨191852328585239232856872587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127901552390159488571248391 191852328585239232856872587)
          ·
            refine ⟨287778492877858849285308881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191852328585239232856872587 287778492877858849285308881)
            ·
              refine ⟨215833869658394136963981661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287778492877858849285308881 215833869658394136963981661)
              ·
                refine ⟨80937701121897801361493123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215833869658394136963981661 80937701121897801361493123)
                ·
                  refine ⟨121406551682846702042239685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80937701121897801361493123 121406551682846702042239685)
                  ·
                    refine ⟨22763728440533756632919941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121406551682846702042239685 22763728440533756632919941)
                    ·
                      refine ⟨4268199082600079368672489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22763728440533756632919941 4268199082600079368672489)
                      ·
                        rfl

theorem cell23_8312288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_8312288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312288 prefixEnd_8312288 := by exact prefixLift 8312288
  have htrace : WordTrace (prefixWord ++ tailWord_8312288) baseStart_8312288 baseEnd_8312288 := by
    simpa [prefixWord, tailWord_8312288, baseEnd_8312288] using wordTrace_append hprefix tailTrace_8312288
  have hstable : (prefixWord ++ tailWord_8312288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312288).length < 2 ^ (prefixWord ++ tailWord_8312288).sum := by decide
  have hdescent : baseEnd_8312288 < baseStart_8312288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312332 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 7]
def baseStart_8312332 : Nat := 118140960795 + 8312332 * 2 ^ 59
def prefixEnd_8312332 : Nat := 4983230072969 + 3 ^ 40 * 8312332 * 2
def baseEnd_8312332 : Nat := 474246852860986355169143

theorem tailTrace_8312332 : CollatzResearch.WordTrace tailWord_8312332 prefixEnd_8312332 474246852860986355169143 := by
  unfold tailWord_8312332
  simp only [CollatzResearch.WordTrace]
  refine ⟨151587827460924136063965625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202117103281232181418620833 151587827460924136063965625)
  ·
    refine ⟨113690870595693102047974219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151587827460924136063965625 113690870595693102047974219)
    ·
      refine ⟨170536305893539653071961329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113690870595693102047974219 170536305893539653071961329)
      ·
        refine ⟨127902229420154739803970997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170536305893539653071961329 127902229420154739803970997)
        ·
          refine ⟨11990834008139506856622281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127902229420154739803970997 11990834008139506856622281)
          ·
            refine ⟨8993125506104630142466711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11990834008139506856622281 8993125506104630142466711)
            ·
              refine ⟨13489688259156945213700067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993125506104630142466711 13489688259156945213700067)
              ·
                refine ⟨20234532388735417820550101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13489688259156945213700067 20234532388735417820550101)
                ·
                  refine ⟨474246852860986355169143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20234532388735417820550101 474246852860986355169143)
                  ·
                    rfl

theorem cell23_8312332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_8312332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312332 prefixEnd_8312332 := by exact prefixLift 8312332
  have htrace : WordTrace (prefixWord ++ tailWord_8312332) baseStart_8312332 baseEnd_8312332 := by
    simpa [prefixWord, tailWord_8312332, baseEnd_8312332] using wordTrace_append hprefix tailTrace_8312332
  have hstable : (prefixWord ++ tailWord_8312332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312332).length < 2 ^ (prefixWord ++ tailWord_8312332).sum := by decide
  have hdescent : baseEnd_8312332 < baseStart_8312332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312362 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_8312362 : Nat := 118140960795 + 8312362 * 2 ^ 59
def prefixEnd_8312362 : Nat := 4983230072969 + 3 ^ 40 * 8312362 * 2
def baseEnd_8312362 : Nat := 1422745693389504026382383

theorem tailTrace_8312362 : CollatzResearch.WordTrace tailWord_8312362 prefixEnd_8312362 1422745693389504026382383 := by
  unfold tailWord_8312362
  simp only [CollatzResearch.WordTrace]
  refine ⟨75794187277934896812880835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202117832741159724834348893 75794187277934896812880835)
  ·
    refine ⟨113691280916902345219321253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75794187277934896812880835 113691280916902345219321253)
    ·
      refine ⟨21317115171919189728622735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113691280916902345219321253 21317115171919189728622735)
      ·
        refine ⟨31975672757878784592934103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21317115171919189728622735 31975672757878784592934103)
        ·
          refine ⟨47963509136818176889401155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31975672757878784592934103 47963509136818176889401155)
          ·
            refine ⟨71945263705227265334101733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47963509136818176889401155 71945263705227265334101733)
            ·
              refine ⟨13489736944730112250144075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71945263705227265334101733 13489736944730112250144075)
              ·
                refine ⟨20234605417095168375216113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13489736944730112250144075 20234605417095168375216113)
                ·
                  refine ⟨15175954062821376281412085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20234605417095168375216113 15175954062821376281412085)
                  ·
                    refine ⟨1422745693389504026382383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15175954062821376281412085 1422745693389504026382383)
                    ·
                      rfl

theorem cell23_8312362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_8312362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312362 prefixEnd_8312362 := by exact prefixLift 8312362
  have htrace : WordTrace (prefixWord ++ tailWord_8312362) baseStart_8312362 baseEnd_8312362 := by
    simpa [prefixWord, tailWord_8312362, baseEnd_8312362] using wordTrace_append hprefix tailTrace_8312362
  have hstable : (prefixWord ++ tailWord_8312362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312362).length < 2 ^ (prefixWord ++ tailWord_8312362).sum := by decide
  have hdescent : baseEnd_8312362 < baseStart_8312362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312385 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_8312385 : Nat := 118140960795 + 8312385 * 2 ^ 59
def prefixEnd_8312385 : Nat := 4983230072969 + 3 ^ 40 * 8312385 * 2
def baseEnd_8312385 : Nat := 4268248890223565489159543

theorem tailTrace_8312385 : CollatzResearch.WordTrace tailWord_8312385 prefixEnd_8312385 4268248890223565489159543 := by
  unfold tailWord_8312385
  simp only [CollatzResearch.WordTrace]
  refine ⟨303177587990656262179610609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202118391993770841453073739 303177587990656262179610609)
  ·
    refine ⟨227383190992992196634707957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303177587990656262179610609 227383190992992196634707957)
    ·
      refine ⟨21317174155593018434503871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227383190992992196634707957 21317174155593018434503871)
      ·
        refine ⟨31975761233389527651755807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21317174155593018434503871 31975761233389527651755807)
        ·
          refine ⟨47963641850084291477633711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31975761233389527651755807 47963641850084291477633711)
          ·
            refine ⟨71945462775126437216450567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47963641850084291477633711 71945462775126437216450567)
            ·
              refine ⟨107918194162689655824675851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71945462775126437216450567 107918194162689655824675851)
              ·
                refine ⟨161877291244034483737013777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107918194162689655824675851 161877291244034483737013777)
                ·
                  refine ⟨121407968433025862802760333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161877291244034483737013777 121407968433025862802760333)
                  ·
                    refine ⟨45527988162384698551035125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121407968433025862802760333 45527988162384698551035125)
                    ·
                      refine ⟨4268248890223565489159543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45527988162384698551035125 4268248890223565489159543)
                      ·
                        rfl

theorem cell23_8312385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_8312385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312385 prefixEnd_8312385 := by exact prefixLift 8312385
  have htrace : WordTrace (prefixWord ++ tailWord_8312385) baseStart_8312385 baseEnd_8312385 := by
    simpa [prefixWord, tailWord_8312385, baseEnd_8312385] using wordTrace_append hprefix tailTrace_8312385
  have hstable : (prefixWord ++ tailWord_8312385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312385).length < 2 ^ (prefixWord ++ tailWord_8312385).sum := by decide
  have hdescent : baseEnd_8312385 < baseStart_8312385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312413 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_8312413 : Nat := 118140960795 + 8312413 * 2 ^ 59
def prefixEnd_8312413 : Nat := 4983230072969 + 3 ^ 40 * 8312413 * 2
def baseEnd_8312413 : Nat := 1422754422560630459869805

theorem tailTrace_8312413 : CollatzResearch.WordTrace tailWord_8312413 prefixEnd_8312413 1422754422560630459869805 := by
  unfold tailWord_8312413
  simp only [CollatzResearch.WordTrace]
  refine ⟨303178609234554822961629893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202119072823036548641086595 303178609234554822961629893)
  ·
    refine ⟨56845989231479029305305605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303178609234554822961629893 56845989231479029305305605)
    ·
      refine ⟨10658622980902317994744801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56845989231479029305305605 10658622980902317994744801)
      ·
        refine ⟨7993967235676738496058601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10658622980902317994744801 7993967235676738496058601)
        ·
          refine ⟨5995475426757553872043951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7993967235676738496058601 5995475426757553872043951)
          ·
            refine ⟨8993213140136330808065927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995475426757553872043951 8993213140136330808065927)
            ·
              refine ⟨13489819710204496212098891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993213140136330808065927 13489819710204496212098891)
              ·
                refine ⟨20234729565306744318148337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13489819710204496212098891 20234729565306744318148337)
                ·
                  refine ⟨15176047173980058238611253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20234729565306744318148337 15176047173980058238611253)
                  ·
                    refine ⟨1422754422560630459869805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15176047173980058238611253 1422754422560630459869805)
                    ·
                      rfl

theorem cell23_8312413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_8312413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312413 prefixEnd_8312413 := by exact prefixLift 8312413
  have htrace : WordTrace (prefixWord ++ tailWord_8312413) baseStart_8312413 baseEnd_8312413 := by
    simpa [prefixWord, tailWord_8312413, baseEnd_8312413] using wordTrace_append hprefix tailTrace_8312413
  have hstable : (prefixWord ++ tailWord_8312413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312413).length < 2 ^ (prefixWord ++ tailWord_8312413).sum := by decide
  have hdescent : baseEnd_8312413 < baseStart_8312413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312419 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 3]
def baseStart_8312419 : Nat := 118140960795 + 8312419 * 2 ^ 59
def prefixEnd_8312419 : Nat := 4983230072969 + 3 ^ 40 * 8312419 * 2
def baseEnd_8312419 : Nat := 4268266348565818356134387

theorem tailTrace_8312419 : CollatzResearch.WordTrace tailWord_8312419 prefixEnd_8312419 4268266348565818356134387 := by
  unfold tailWord_8312419
  simp only [CollatzResearch.WordTrace]
  refine ⟨303178828072533085986348311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202119218715022057324232207 303178828072533085986348311)
  ·
    refine ⟨454768242108799628979522467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303178828072533085986348311 454768242108799628979522467)
    ·
      refine ⟨682152363163199443469283701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454768242108799628979522467 682152363163199443469283701)
      ·
        refine ⟨63951784046549947825245347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 682152363163199443469283701 63951784046549947825245347)
        ·
          refine ⟨95927676069824921737868021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63951784046549947825245347 95927676069824921737868021)
          ·
            refine ⟨8993219631546086412925127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95927676069824921737868021 8993219631546086412925127)
            ·
              refine ⟨13489829447319129619387691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993219631546086412925127 13489829447319129619387691)
              ·
                refine ⟨20234744170978694429081537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13489829447319129619387691 20234744170978694429081537)
                ·
                  refine ⟨15176058128234020821811153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20234744170978694429081537 15176058128234020821811153)
                  ·
                    refine ⟨11382043596175515616358365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15176058128234020821811153 11382043596175515616358365)
                    ·
                      refine ⟨4268266348565818356134387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382043596175515616358365 4268266348565818356134387)
                      ·
                        rfl

theorem cell23_8312419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_8312419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312419 prefixEnd_8312419 := by exact prefixLift 8312419
  have htrace : WordTrace (prefixWord ++ tailWord_8312419) baseStart_8312419 baseEnd_8312419 := by
    simpa [prefixWord, tailWord_8312419, baseEnd_8312419] using wordTrace_append hprefix tailTrace_8312419
  have hstable : (prefixWord ++ tailWord_8312419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312419).length < 2 ^ (prefixWord ++ tailWord_8312419).sum := by decide
  have hdescent : baseEnd_8312419 < baseStart_8312419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312426 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_8312426 : Nat := 118140960795 + 8312426 * 2 ^ 59
def prefixEnd_8312426 : Nat := 4983230072969 + 3 ^ 40 * 8312426 * 2
def baseEnd_8312426 : Nat := 1422756647643466609582285

theorem tailTrace_8312426 : CollatzResearch.WordTrace tailWord_8312426 prefixEnd_8312426 1422756647643466609582285 := by
  unfold tailWord_8312426
  simp only [CollatzResearch.WordTrace]
  refine ⟨75794770845876931545463283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202119388922338484121235421 75794770845876931545463283)
  ·
    refine ⟨113692156268815397318194925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75794770845876931545463283 113692156268815397318194925)
    ·
      refine ⟨42634558600805773994323097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113692156268815397318194925 42634558600805773994323097)
      ·
        refine ⟨31975918950604330495742323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42634558600805773994323097 31975918950604330495742323)
        ·
          refine ⟨47963878425906495743613485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31975918950604330495742323 47963878425906495743613485)
          ·
            refine ⟨17986454409714935903855057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47963878425906495743613485 17986454409714935903855057)
            ·
              refine ⟨13489840807286201927891293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17986454409714935903855057 13489840807286201927891293)
              ·
                refine ⟨5058690302732325722959235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13489840807286201927891293 5058690302732325722959235)
                ·
                  refine ⟨7588035454098488584438853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058690302732325722959235 7588035454098488584438853)
                  ·
                    refine ⟨1422756647643466609582285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7588035454098488584438853 1422756647643466609582285)
                    ·
                      rfl

theorem cell23_8312426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_8312426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312426 prefixEnd_8312426 := by exact prefixLift 8312426
  have htrace : WordTrace (prefixWord ++ tailWord_8312426) baseStart_8312426 baseEnd_8312426 := by
    simpa [prefixWord, tailWord_8312426, baseEnd_8312426] using wordTrace_append hprefix tailTrace_8312426
  have hstable : (prefixWord ++ tailWord_8312426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312426).length < 2 ^ (prefixWord ++ tailWord_8312426).sum := by decide
  have hdescent : baseEnd_8312426 < baseStart_8312426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312449 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_8312449 : Nat := 118140960795 + 8312449 * 2 ^ 59
def prefixEnd_8312449 : Nat := 4983230072969 + 3 ^ 40 * 8312449 * 2
def baseEnd_8312449 : Nat := 4268281752985453238759249

theorem tailTrace_8312449 : CollatzResearch.WordTrace tailWord_8312449 prefixEnd_8312449 4268281752985453238759249 := by
  unfold tailWord_8312449
  simp only [CollatzResearch.WordTrace]
  refine ⟨303179922262424401109940401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202119948174949600739960267 303179922262424401109940401)
  ·
    refine ⟨227384941696818300832455301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303179922262424401109940401 227384941696818300832455301)
    ·
      refine ⟨42634676568153431406085369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227384941696818300832455301 42634676568153431406085369)
      ·
        refine ⟨31976007426115073554564027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42634676568153431406085369 31976007426115073554564027)
        ·
          refine ⟨47964011139172610331846041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31976007426115073554564027 47964011139172610331846041)
          ·
            refine ⟨35973008354379457748884531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47964011139172610331846041 35973008354379457748884531)
            ·
              refine ⟨53959512531569186623326797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35973008354379457748884531 53959512531569186623326797)
              ·
                refine ⟨20234817199338444983747549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53959512531569186623326797 20234817199338444983747549)
                ·
                  refine ⟨7588056449751916868905331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20234817199338444983747549 7588056449751916868905331)
                  ·
                    refine ⟨11382084674627875303357997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588056449751916868905331 11382084674627875303357997)
                    ·
                      refine ⟨4268281752985453238759249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382084674627875303357997 4268281752985453238759249)
                      ·
                        rfl

theorem cell23_8312449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_8312449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312449 prefixEnd_8312449 := by exact prefixLift 8312449
  have htrace : WordTrace (prefixWord ++ tailWord_8312449) baseStart_8312449 baseEnd_8312449 := by
    simpa [prefixWord, tailWord_8312449, baseEnd_8312449] using wordTrace_append hprefix tailTrace_8312449
  have hstable : (prefixWord ++ tailWord_8312449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312449).length < 2 ^ (prefixWord ++ tailWord_8312449).sum := by decide
  have hdescent : baseEnd_8312449 < baseStart_8312449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312456 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 6]
def baseStart_8312456 : Nat := 118140960795 + 8312456 * 2 ^ 59
def prefixEnd_8312456 : Nat := 4983230072969 + 3 ^ 40 * 8312456 * 2
def baseEnd_8312456 : Nat := 474253927483337190152413

theorem tailTrace_8312456 : CollatzResearch.WordTrace tailWord_8312456 prefixEnd_8312456 474253927483337190152413 := by
  unfold tailWord_8312456
  simp only [CollatzResearch.WordTrace]
  refine ⟨151590088786699520652722611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202120118382266027536963481 151590088786699520652722611)
  ·
    refine ⟨227385133180049280979083917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151590088786699520652722611 227385133180049280979083917)
    ·
      refine ⟨85269424942518480367156469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227385133180049280979083917 85269424942518480367156469)
      ·
        refine ⟨7994008588361107534420919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85269424942518480367156469 7994008588361107534420919)
        ·
          refine ⟨11991012882541661301631379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994008588361107534420919 11991012882541661301631379)
          ·
            refine ⟨17986519323812491952447069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991012882541661301631379 17986519323812491952447069)
            ·
              refine ⟨6744944746429684482167651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17986519323812491952447069 6744944746429684482167651)
              ·
                refine ⟨10117417119644526723251477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6744944746429684482167651 10117417119644526723251477)
                ·
                  refine ⟨474253927483337190152413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10117417119644526723251477 474253927483337190152413)
                  ·
                    rfl

theorem cell23_8312456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 6].length) (baseStart_8312456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312456 prefixEnd_8312456 := by exact prefixLift 8312456
  have htrace : WordTrace (prefixWord ++ tailWord_8312456) baseStart_8312456 baseEnd_8312456 := by
    simpa [prefixWord, tailWord_8312456, baseEnd_8312456] using wordTrace_append hprefix tailTrace_8312456
  have hstable : (prefixWord ++ tailWord_8312456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312456).length < 2 ^ (prefixWord ++ tailWord_8312456).sum := by decide
  have hdescent : baseEnd_8312456 < baseStart_8312456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312465 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_8312465 : Nat := 118140960795 + 8312465 * 2 ^ 59
def prefixEnd_8312465 : Nat := 4983230072969 + 3 ^ 40 * 8312465 * 2
def baseEnd_8312465 : Nat := 1422763322891975058719725

theorem tailTrace_8312465 : CollatzResearch.WordTrace tailWord_8312465 prefixEnd_8312465 1422763322891975058719725 := by
  unfold tailWord_8312465
  simp only [CollatzResearch.WordTrace]
  refine ⟨303180505830366435842522849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202120337220244290561681899 303180505830366435842522849)
  ·
    refine ⟨227385379372774826881892137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303180505830366435842522849 227385379372774826881892137)
    ·
      refine ⟨170539034529581120161419103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227385379372774826881892137 170539034529581120161419103)
      ·
        refine ⟨255808551794371680242128655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170539034529581120161419103 255808551794371680242128655)
        ·
          refine ⟨383712827691557520363192983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255808551794371680242128655 383712827691557520363192983)
          ·
            refine ⟨575569241537336280544789475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383712827691557520363192983 575569241537336280544789475)
            ·
              refine ⟨863353862306004420817184213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575569241537336280544789475 863353862306004420817184213)
              ·
                refine ⟨20234856147796978612902755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 863353862306004420817184213 20234856147796978612902755)
                ·
                  refine ⟨30352284221695467919354133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20234856147796978612902755 30352284221695467919354133)
                  ·
                    refine ⟨1422763322891975058719725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30352284221695467919354133 1422763322891975058719725)
                    ·
                      rfl

theorem cell23_8312465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_8312465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312465 prefixEnd_8312465 := by exact prefixLift 8312465
  have htrace : WordTrace (prefixWord ++ tailWord_8312465) baseStart_8312465 baseEnd_8312465 := by
    simpa [prefixWord, tailWord_8312465, baseEnd_8312465] using wordTrace_append hprefix tailTrace_8312465
  have hstable : (prefixWord ++ tailWord_8312465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312465).length < 2 ^ (prefixWord ++ tailWord_8312465).sum := by decide
  have hdescent : baseEnd_8312465 < baseStart_8312465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312506 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2]
def baseStart_8312506 : Nat := 118140960795 + 8312506 * 2 ^ 59
def prefixEnd_8312506 : Nat := 4983230072969 + 3 ^ 40 * 8312506 * 2
def baseEnd_8312506 : Nat := 4268311021382759515746487

theorem tailTrace_8312506 : CollatzResearch.WordTrace tailWord_8312506 prefixEnd_8312506 4268311021382759515746487 := by
  unfold tailWord_8312506
  simp only [CollatzResearch.WordTrace]
  refine ⟨75795500305804474961191343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202121334148811933229843581 75795500305804474961191343)
  ·
    refine ⟨113693250458706712441787015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75795500305804474961191343 113693250458706712441787015)
    ·
      refine ⟨170539875688060068662680523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113693250458706712441787015 170539875688060068662680523)
      ·
        refine ⟨255809813532090102994020785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170539875688060068662680523 255809813532090102994020785)
        ·
          refine ⟨191857360149067577245515589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255809813532090102994020785 191857360149067577245515589)
          ·
            refine ⟨35973255027950170733534173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191857360149067577245515589 35973255027950170733534173)
            ·
              refine ⟨13489970635481314025075315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35973255027950170733534173 13489970635481314025075315)
              ·
                refine ⟨20234955953221971037612973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13489970635481314025075315 20234955953221971037612973)
                ·
                  refine ⟨7588108482458239139104865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20234955953221971037612973 7588108482458239139104865)
                  ·
                    refine ⟨5691081361843679354328649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588108482458239139104865 5691081361843679354328649)
                    ·
                      refine ⟨4268311021382759515746487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691081361843679354328649 4268311021382759515746487)
                      ·
                        rfl

theorem cell23_8312506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_8312506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312506 prefixEnd_8312506 := by exact prefixLift 8312506
  have htrace : WordTrace (prefixWord ++ tailWord_8312506) baseStart_8312506 baseEnd_8312506 := by
    simpa [prefixWord, tailWord_8312506, baseEnd_8312506] using wordTrace_append hprefix tailTrace_8312506
  have hstable : (prefixWord ++ tailWord_8312506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312506).length < 2 ^ (prefixWord ++ tailWord_8312506).sum := by decide
  have hdescent : baseEnd_8312506 < baseStart_8312506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312557 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_8312557 : Nat := 118140960795 + 8312557 * 2 ^ 59
def prefixEnd_8312557 : Nat := 4983230072969 + 3 ^ 40 * 8312557 * 2
def baseEnd_8312557 : Nat := 4268337208896138816208753

theorem tailTrace_8312557 : CollatzResearch.WordTrace tailWord_8312557 prefixEnd_8312557 4268337208896138816208753 := by
  unfold tailWord_8312557
  simp only [CollatzResearch.WordTrace]
  refine ⟨303183861346033135554871925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202122574230688757036581283 303183861346033135554871925)
  ·
    refine ⟨28423487001190606458269243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303183861346033135554871925 28423487001190606458269243)
    ·
      refine ⟨42635230501785909687403865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28423487001190606458269243 42635230501785909687403865)
      ·
        refine ⟨31976422876339432265552899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42635230501785909687403865 31976422876339432265552899)
        ·
          refine ⟨47964634314509148398329349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31976422876339432265552899 47964634314509148398329349)
          ·
            refine ⟨8993368933970465324686753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47964634314509148398329349 8993368933970465324686753)
            ·
              refine ⟨6745026700477848993515065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993368933970465324686753 6745026700477848993515065)
              ·
                refine ⟨5058770025358386745136299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745026700477848993515065 5058770025358386745136299)
                ·
                  refine ⟨7588155038037580117704449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058770025358386745136299 7588155038037580117704449)
                  ·
                    refine ⟨5691116278528185088278337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588155038037580117704449 5691116278528185088278337)
                    ·
                      refine ⟨4268337208896138816208753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691116278528185088278337 4268337208896138816208753)
                      ·
                        rfl

theorem cell23_8312557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_8312557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312557 prefixEnd_8312557 := by exact prefixLift 8312557
  have htrace : WordTrace (prefixWord ++ tailWord_8312557) baseStart_8312557 baseEnd_8312557 := by
    simpa [prefixWord, tailWord_8312557, baseEnd_8312557] using wordTrace_append hprefix tailTrace_8312557
  have hstable : (prefixWord ++ tailWord_8312557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312557).length < 2 ^ (prefixWord ++ tailWord_8312557).sum := by decide
  have hdescent : baseEnd_8312557 < baseStart_8312557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312562 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_8312562 : Nat := 118140960795 + 8312562 * 2 ^ 59
def prefixEnd_8312562 : Nat := 4983230072969 + 3 ^ 40 * 8312562 * 2
def baseEnd_8312562 : Nat := 4268339776299411296646229

theorem tailTrace_8312562 : CollatzResearch.WordTrace tailWord_8312562 prefixEnd_8312562 4268339776299411296646229 := by
  unfold tailWord_8312562
  simp only [CollatzResearch.WordTrace]
  refine ⟨75796010927753755352200985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202122695807343347605869293 75796010927753755352200985)
  ·
    refine ⟨56847008195815316514150739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75796010927753755352200985 56847008195815316514150739)
    ·
      refine ⟨85270512293722974771226109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56847008195815316514150739 85270512293722974771226109)
      ·
        refine ⟨31976442110146115539209791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85270512293722974771226109 31976442110146115539209791)
        ·
          refine ⟨47964663165219173308814687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31976442110146115539209791 47964663165219173308814687)
          ·
            refine ⟨71946994747828759963222031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47964663165219173308814687 71946994747828759963222031)
            ·
              refine ⟨107920492121743139944833047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71946994747828759963222031 107920492121743139944833047)
              ·
                refine ⟨161880738182614709917249571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107920492121743139944833047 161880738182614709917249571)
                ·
                  refine ⟨242821107273922064875874357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161880738182614709917249571 242821107273922064875874357)
                  ·
                    refine ⟨22764478806930193582113221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 242821107273922064875874357 22764478806930193582113221)
                    ·
                      refine ⟨4268339776299411296646229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22764478806930193582113221 4268339776299411296646229)
                      ·
                        rfl

theorem cell23_8312562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_8312562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312562 prefixEnd_8312562 := by exact prefixLift 8312562
  have htrace : WordTrace (prefixWord ++ tailWord_8312562) baseStart_8312562 baseEnd_8312562 := by
    simpa [prefixWord, tailWord_8312562, baseEnd_8312562] using wordTrace_append hprefix tailTrace_8312562
  have hstable : (prefixWord ++ tailWord_8312562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312562).length < 2 ^ (prefixWord ++ tailWord_8312562).sum := by decide
  have hdescent : baseEnd_8312562 < baseStart_8312562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312566 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_8312566 : Nat := 118140960795 + 8312566 * 2 ^ 59
def prefixEnd_8312566 : Nat := 4983230072969 + 3 ^ 40 * 8312566 * 2
def baseEnd_8312566 : Nat := 4268341830222029280996211

theorem tailTrace_8312566 : CollatzResearch.WordTrace tailWord_8312566 prefixEnd_8312566 4268341830222029280996211 := by
  unfold tailWord_8312566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949011850187533130746847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202122793068667020061299701 18949011850187533130746847)
  ·
    refine ⟨28423517775281299696120271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949011850187533130746847 28423517775281299696120271)
    ·
      refine ⟨42635276662921949544180407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28423517775281299696120271 42635276662921949544180407)
      ·
        refine ⟨63952914994382924316270611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42635276662921949544180407 63952914994382924316270611)
        ·
          refine ⟨95929372491574386474405917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63952914994382924316270611 95929372491574386474405917)
          ·
            refine ⟨35973514684340394927902219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95929372491574386474405917 35973514684340394927902219)
            ·
              refine ⟨53960272026510592391853329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35973514684340394927902219 53960272026510592391853329)
              ·
                refine ⟨40470204019882944293889997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53960272026510592391853329 40470204019882944293889997)
                ·
                  refine ⟨15176326507456104110208749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40470204019882944293889997 15176326507456104110208749)
                  ·
                    refine ⟨5691122440296039041328281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15176326507456104110208749 5691122440296039041328281)
                    ·
                      refine ⟨4268341830222029280996211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691122440296039041328281 4268341830222029280996211)
                      ·
                        rfl

theorem cell23_8312566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_8312566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312566 prefixEnd_8312566 := by exact prefixLift 8312566
  have htrace : WordTrace (prefixWord ++ tailWord_8312566) baseStart_8312566 baseEnd_8312566 := by
    simpa [prefixWord, tailWord_8312566, baseEnd_8312566] using wordTrace_append hprefix tailTrace_8312566
  have hstable : (prefixWord ++ tailWord_8312566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312566).length < 2 ^ (prefixWord ++ tailWord_8312566).sum := by decide
  have hdescent : baseEnd_8312566 < baseStart_8312566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312572 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_8312572 : Nat := 118140960795 + 8312572 * 2 ^ 59
def prefixEnd_8312572 : Nat := 4983230072969 + 3 ^ 40 * 8312572 * 2
def baseEnd_8312572 : Nat := 1422781637035318752507061

theorem tailTrace_8312572 : CollatzResearch.WordTrace tailWord_8312572 prefixEnd_8312572 1422781637035318752507061 := by
  unfold tailWord_8312572
  simp only [CollatzResearch.WordTrace]
  refine ⟨151592204220489396558333985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202122938960652528744445313 151592204220489396558333985)
  ·
    refine ⟨113694153165367047418750489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151592204220489396558333985 113694153165367047418750489)
    ·
      refine ⟨85270614874025285564062867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113694153165367047418750489 85270614874025285564062867)
      ·
        refine ⟨127905922311037928346094301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85270614874025285564062867 127905922311037928346094301)
        ·
          refine ⟨47964720866639223129785363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127905922311037928346094301 47964720866639223129785363)
          ·
            refine ⟨71947081299958834694678045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47964720866639223129785363 71947081299958834694678045)
            ·
              refine ⟨26980155487484563010504267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71947081299958834694678045 26980155487484563010504267)
              ·
                refine ⟨40470233231226844515756401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26980155487484563010504267 40470233231226844515756401)
                ·
                  refine ⟨30352674923420133386817301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40470233231226844515756401 30352674923420133386817301)
                  ·
                    refine ⟨1422781637035318752507061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30352674923420133386817301 1422781637035318752507061)
                    ·
                      rfl

theorem cell23_8312572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_8312572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312572 prefixEnd_8312572 := by exact prefixLift 8312572
  have htrace : WordTrace (prefixWord ++ tailWord_8312572) baseStart_8312572 baseEnd_8312572 := by
    simpa [prefixWord, tailWord_8312572, baseEnd_8312572] using wordTrace_append hprefix tailTrace_8312572
  have hstable : (prefixWord ++ tailWord_8312572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312572).length < 2 ^ (prefixWord ++ tailWord_8312572).sum := by decide
  have hdescent : baseEnd_8312572 < baseStart_8312572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312579 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 1, 4, 2]
def baseStart_8312579 : Nat := 118140960795 + 8312579 * 2 ^ 59
def prefixEnd_8312579 : Nat := 4983230072969 + 3 ^ 40 * 8312579 * 2
def baseEnd_8312579 : Nat := 4268348505470537730133651

theorem tailTrace_8312579 : CollatzResearch.WordTrace tailWord_8312579 prefixEnd_8312579 4268348505470537730133651 := by
  unfold tailWord_8312579
  simp only [CollatzResearch.WordTrace]
  refine ⟨303184663751953433312172791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202123109167968955541448527 303184663751953433312172791)
  ·
    refine ⟨454776995627930149968259187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303184663751953433312172791 454776995627930149968259187)
    ·
      refine ⟨682165493441895224952388781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454776995627930149968259187 682165493441895224952388781)
      ·
        refine ⟨255812060040710709357145793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682165493441895224952388781 255812060040710709357145793)
        ·
          refine ⟨191859045030533032017859345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255812060040710709357145793 191859045030533032017859345)
          ·
            refine ⟨143894283772899774013394509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191859045030533032017859345 143894283772899774013394509)
            ·
              refine ⟨53960356414837415255022941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143894283772899774013394509 53960356414837415255022941)
              ·
                refine ⟨20235133655564030720633603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53960356414837415255022941 20235133655564030720633603)
                ·
                  refine ⟨30352700483346046080950405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20235133655564030720633603 30352700483346046080950405)
                  ·
                    refine ⟨5691131340627383640178201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30352700483346046080950405 5691131340627383640178201)
                    ·
                      refine ⟨4268348505470537730133651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691131340627383640178201 4268348505470537730133651)
                      ·
                        rfl

theorem cell23_8312579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_8312579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312579 prefixEnd_8312579 := by exact prefixLift 8312579
  have htrace : WordTrace (prefixWord ++ tailWord_8312579) baseStart_8312579 baseEnd_8312579 := by
    simpa [prefixWord, tailWord_8312579, baseEnd_8312579] using wordTrace_append hprefix tailTrace_8312579
  have hstable : (prefixWord ++ tailWord_8312579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312579).length < 2 ^ (prefixWord ++ tailWord_8312579).sum := by decide
  have hdescent : baseEnd_8312579 < baseStart_8312579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312613 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 2, 2, 2]
def baseStart_8312613 : Nat := 118140960795 + 8312613 * 2 ^ 59
def prefixEnd_8312613 : Nat := 4983230072969 + 3 ^ 40 * 8312613 * 2
def baseEnd_8312613 : Nat := 4268365963812790597108495

theorem tailTrace_8312613 : CollatzResearch.WordTrace tailWord_8312613 prefixEnd_8312613 4268365963812790597108495 := by
  unfold tailWord_8312613
  simp only [CollatzResearch.WordTrace]
  refine ⟨303185903833830257118910493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202123935889220171412606995 303185903833830257118910493)
  ·
    refine ⟨113694713937686346419591435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303185903833830257118910493 113694713937686346419591435)
    ·
      refine ⟨170542070906529519629387153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113694713937686346419591435 170542070906529519629387153)
      ·
        refine ⟨127906553179897139722040365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170542070906529519629387153 127906553179897139722040365)
        ·
          refine ⟨47964957442461427395765137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127906553179897139722040365 47964957442461427395765137)
          ·
            refine ⟨35973718081846070546823853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47964957442461427395765137 35973718081846070546823853)
            ·
              refine ⟨13490144280692276455058945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35973718081846070546823853 13490144280692276455058945)
              ·
                refine ⟨10117608210519207341294209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13490144280692276455058945 10117608210519207341294209)
                ·
                  refine ⟨7588206157889405505970657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10117608210519207341294209 7588206157889405505970657)
                  ·
                    refine ⟨5691154618417054129477993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588206157889405505970657 5691154618417054129477993)
                    ·
                      refine ⟨4268365963812790597108495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691154618417054129477993 4268365963812790597108495)
                      ·
                        rfl

theorem cell23_8312613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_8312613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312613 prefixEnd_8312613 := by exact prefixLift 8312613
  have htrace : WordTrace (prefixWord ++ tailWord_8312613) baseStart_8312613 baseEnd_8312613 := by
    simpa [prefixWord, tailWord_8312613, baseEnd_8312613] using wordTrace_append hprefix tailTrace_8312613
  have hstable : (prefixWord ++ tailWord_8312613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312613).length < 2 ^ (prefixWord ++ tailWord_8312613).sum := by decide
  have hdescent : baseEnd_8312613 < baseStart_8312613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312630 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_8312630 : Nat := 118140960795 + 8312630 * 2 ^ 59
def prefixEnd_8312630 : Nat := 4983230072969 + 3 ^ 40 * 8312630 * 2
def baseEnd_8312630 : Nat := 4268374692983917030595917

theorem tailTrace_8312630 : CollatzResearch.WordTrace tailWord_8312630 prefixEnd_8312630 4268374692983917030595917 := by
  unfold tailWord_8312630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949157742173041813892459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202124349249845779348186229 18949157742173041813892459)
  ·
    refine ⟨28423736613259562720838689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949157742173041813892459 28423736613259562720838689)
    ·
      refine ⟨21317802459944672040629017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28423736613259562720838689 21317802459944672040629017)
      ·
        refine ⟨15988351844958504030471763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21317802459944672040629017 15988351844958504030471763)
        ·
          refine ⟨23982527767437756045707645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15988351844958504030471763 23982527767437756045707645)
          ·
            refine ⟨8993447912789158517140367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23982527767437756045707645 8993447912789158517140367)
            ·
              refine ⟨13490171869183737775710551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993447912789158517140367 13490171869183737775710551)
              ·
                refine ⟨20235257803775606663565827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13490171869183737775710551 20235257803775606663565827)
                ·
                  refine ⟨30352886705663409995348741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20235257803775606663565827 30352886705663409995348741)
                  ·
                    refine ⟨5691166257311889374127889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30352886705663409995348741 5691166257311889374127889)
                    ·
                      refine ⟨4268374692983917030595917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691166257311889374127889 4268374692983917030595917)
                      ·
                        rfl

theorem cell23_8312630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_8312630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312630 prefixEnd_8312630 := by exact prefixLift 8312630
  have htrace : WordTrace (prefixWord ++ tailWord_8312630) baseStart_8312630 baseEnd_8312630 := by
    simpa [prefixWord, tailWord_8312630, baseEnd_8312630] using wordTrace_append hprefix tailTrace_8312630
  have hstable : (prefixWord ++ tailWord_8312630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312630).length < 2 ^ (prefixWord ++ tailWord_8312630).sum := by decide
  have hdescent : baseEnd_8312630 < baseStart_8312630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312632 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_8312632 : Nat := 118140960795 + 8312632 * 2 ^ 59
def prefixEnd_8312632 : Nat := 4983230072969 + 3 ^ 40 * 8312632 * 2
def baseEnd_8312632 : Nat := 1422791906648408674256969

theorem tailTrace_8312632 : CollatzResearch.WordTrace tailWord_8312632 prefixEnd_8312632 1422791906648408674256969 := by
  unfold tailWord_8312632
  simp only [CollatzResearch.WordTrace]
  refine ⟨151593298410380711681926075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202124397880507615575901433 151593298410380711681926075)
  ·
    refine ⟨227389947615571067522889113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151593298410380711681926075 227389947615571067522889113)
    ·
      refine ⟨170542460711678300642166835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227389947615571067522889113 170542460711678300642166835)
      ·
        refine ⟨255813691067517450963250253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170542460711678300642166835 255813691067517450963250253)
        ·
          refine ⟨95930134150319044111218845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255813691067517450963250253 95930134150319044111218845)
          ·
            refine ⟨35973800306369641541707067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95930134150319044111218845 35973800306369641541707067)
            ·
              refine ⟨53960700459554462312560601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35973800306369641541707067 53960700459554462312560601)
              ·
                refine ⟨40470525344665846734420451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53960700459554462312560601 40470525344665846734420451)
                ·
                  refine ⟨60705788016998770101630677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40470525344665846734420451 60705788016998770101630677)
                  ·
                    refine ⟨1422791906648408674256969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60705788016998770101630677 1422791906648408674256969)
                    ·
                      rfl

theorem cell23_8312632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_8312632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312632 prefixEnd_8312632 := by exact prefixLift 8312632
  have htrace : WordTrace (prefixWord ++ tailWord_8312632) baseStart_8312632 baseEnd_8312632 := by
    simpa [prefixWord, tailWord_8312632, baseEnd_8312632] using wordTrace_append hprefix tailTrace_8312632
  have hstable : (prefixWord ++ tailWord_8312632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312632).length < 2 ^ (prefixWord ++ tailWord_8312632).sum := by decide
  have hdescent : baseEnd_8312632 < baseStart_8312632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312653 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 5]
def baseStart_8312653 : Nat := 118140960795 + 8312653 * 2 ^ 59
def prefixEnd_8312653 : Nat := 4983230072969 + 3 ^ 40 * 8312653 * 2
def baseEnd_8312653 : Nat := 474265167004330048956479

theorem tailTrace_8312653 : CollatzResearch.WordTrace tailWord_8312653 prefixEnd_8312653 474265167004330048956479 := by
  unfold tailWord_8312653
  simp only [CollatzResearch.WordTrace]
  refine ⟨303187362753685343950366613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202124908502456895966911075 303187362753685343950366613)
  ·
    refine ⟨14211907629079000497673435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303187362753685343950366613 14211907629079000497673435)
    ·
      refine ⟨21317861443618500746510153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14211907629079000497673435 21317861443618500746510153)
      ·
        refine ⟨15988396082713875559882615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21317861443618500746510153 15988396082713875559882615)
        ·
          refine ⟨23982594124070813339823923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15988396082713875559882615 23982594124070813339823923)
          ·
            refine ⟨35973891186106220009735885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23982594124070813339823923 35973891186106220009735885)
            ·
              refine ⟨13490209194789832503650957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35973891186106220009735885 13490209194789832503650957)
              ·
                refine ⟨5058828448046187188869109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13490209194789832503650957 5058828448046187188869109)
                ·
                  refine ⟨474265167004330048956479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058828448046187188869109 474265167004330048956479)
                  ·
                    rfl

theorem cell23_8312653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_8312653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312653 prefixEnd_8312653 := by exact prefixLift 8312653
  have htrace : WordTrace (prefixWord ++ tailWord_8312653) baseStart_8312653 baseEnd_8312653 := by
    simpa [prefixWord, tailWord_8312653, baseEnd_8312653] using wordTrace_append hprefix tailTrace_8312653
  have hstable : (prefixWord ++ tailWord_8312653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312653).length < 2 ^ (prefixWord ++ tailWord_8312653).sum := by decide
  have hdescent : baseEnd_8312653 < baseStart_8312653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312689 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_8312689 : Nat := 118140960795 + 8312689 * 2 ^ 59
def prefixEnd_8312689 : Nat := 4983230072969 + 3 ^ 40 * 8312689 * 2
def baseEnd_8312689 : Nat := 4268404988342532299758145

theorem tailTrace_8312689 : CollatzResearch.WordTrace tailWord_8312689 prefixEnd_8312689 4268404988342532299758145 := by
  unfold tailWord_8312689
  simp only [CollatzResearch.WordTrace]
  refine ⟨303188675781554922098677121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202125783854369948065784747 303188675781554922098677121)
  ·
    refine ⟨227391506836166191574007841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303188675781554922098677121 227391506836166191574007841)
    ·
      refine ⟨170543630127124643680505881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227391506836166191574007841 170543630127124643680505881)
      ·
        refine ⟨127907722595343482760379411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170543630127124643680505881 127907722595343482760379411)
        ·
          refine ⟨191861583893015224140569117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127907722595343482760379411 191861583893015224140569117)
          ·
            refine ⟨71948093959880709052713419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191861583893015224140569117 71948093959880709052713419)
            ·
              refine ⟨107922140939821063579070129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71948093959880709052713419 107922140939821063579070129)
              ·
                refine ⟨80941605704865797684302597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107922140939821063579070129 80941605704865797684302597)
                ·
                  refine ⟨15176551069662337065806737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80941605704865797684302597 15176551069662337065806737)
                  ·
                    refine ⟨11382413302246752799355053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15176551069662337065806737 11382413302246752799355053)
                    ·
                      refine ⟨4268404988342532299758145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382413302246752799355053 4268404988342532299758145)
                      ·
                        rfl

theorem cell23_8312689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_8312689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312689 prefixEnd_8312689 := by exact prefixLift 8312689
  have htrace : WordTrace (prefixWord ++ tailWord_8312689) baseStart_8312689 baseEnd_8312689 := by
    simpa [prefixWord, tailWord_8312689, baseEnd_8312689] using wordTrace_append hprefix tailTrace_8312689
  have hstable : (prefixWord ++ tailWord_8312689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312689).length < 2 ^ (prefixWord ++ tailWord_8312689).sum := by decide
  have hdescent : baseEnd_8312689 < baseStart_8312689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312730 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_8312730 : Nat := 118140960795 + 8312730 * 2 ^ 59
def prefixEnd_8312730 : Nat := 4983230072969 + 3 ^ 40 * 8312730 * 2
def baseEnd_8312730 : Nat := 1422808680349788879781819

theorem tailTrace_8312730 : CollatzResearch.WordTrace tailWord_8312730 prefixEnd_8312730 1422808680349788879781819 := by
  unfold tailWord_8312730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75797542793601596525229911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202126780782937590733946429 75797542793601596525229911)
  ·
    refine ⟨113696314190402394787844867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75797542793601596525229911 113696314190402394787844867)
    ·
      refine ⟨170544471285603592181767301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113696314190402394787844867 170544471285603592181767301)
      ·
        refine ⟨31977088366050673534081369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170544471285603592181767301 31977088366050673534081369)
        ·
          refine ⟨23982816274538005150561027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31977088366050673534081369 23982816274538005150561027)
          ·
            refine ⟨35974224411807007725841541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23982816274538005150561027 35974224411807007725841541)
            ·
              refine ⟨6745167077213813948595289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35974224411807007725841541 6745167077213813948595289)
              ·
                refine ⟨5058875307910360461446467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745167077213813948595289 5058875307910360461446467)
                ·
                  refine ⟨7588312961865540692169701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058875307910360461446467 7588312961865540692169701)
                  ·
                    refine ⟨1422808680349788879781819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7588312961865540692169701 1422808680349788879781819)
                    ·
                      rfl

theorem cell23_8312730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_8312730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312730 prefixEnd_8312730 := by exact prefixLift 8312730
  have htrace : WordTrace (prefixWord ++ tailWord_8312730) baseStart_8312730 baseEnd_8312730 := by
    simpa [prefixWord, tailWord_8312730, baseEnd_8312730] using wordTrace_append hprefix tailTrace_8312730
  have hstable : (prefixWord ++ tailWord_8312730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312730).length < 2 ^ (prefixWord ++ tailWord_8312730).sum := by decide
  have hdescent : baseEnd_8312730 < baseStart_8312730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312736 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 3, 1, 3]
def baseStart_8312736 : Nat := 118140960795 + 8312736 * 2 ^ 59
def prefixEnd_8312736 : Nat := 4983230072969 + 3 ^ 40 * 8312736 * 2
def baseEnd_8312736 : Nat := 4268429121933293615870429

theorem tailTrace_8312736 : CollatzResearch.WordTrace tailWord_8312736 prefixEnd_8312736 4268429121933293615870429 := by
  unfold tailWord_8312736
  simp only [CollatzResearch.WordTrace]
  refine ⟨151595195006192324562819031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202126926674923099417092041 151595195006192324562819031)
  ·
    refine ⟨227392792509288486844228547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151595195006192324562819031 227392792509288486844228547)
    ·
      refine ⟨341089188763932730266342821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227392792509288486844228547 341089188763932730266342821)
      ·
        refine ⟨63954222893237386924939279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341089188763932730266342821 63954222893237386924939279)
        ·
          refine ⟨95931334339856080387408919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63954222893237386924939279 95931334339856080387408919)
          ·
            refine ⟨143897001509784120581113379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95931334339856080387408919 143897001509784120581113379)
            ·
              refine ⟨215845502264676180871670069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143897001509784120581113379 215845502264676180871670069)
              ·
                refine ⟨20235515837313391956719069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215845502264676180871670069 20235515837313391956719069)
                ·
                  refine ⟨7588318438992521983769651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20235515837313391956719069 7588318438992521983769651)
                  ·
                    refine ⟨11382477658488782975654477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588318438992521983769651 11382477658488782975654477)
                    ·
                      refine ⟨4268429121933293615870429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382477658488782975654477 4268429121933293615870429)
                      ·
                        rfl

theorem cell23_8312736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_8312736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312736 prefixEnd_8312736 := by exact prefixLift 8312736
  have htrace : WordTrace (prefixWord ++ tailWord_8312736) baseStart_8312736 baseEnd_8312736 := by
    simpa [prefixWord, tailWord_8312736, baseEnd_8312736] using wordTrace_append hprefix tailTrace_8312736
  have hstable : (prefixWord ++ tailWord_8312736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312736).length < 2 ^ (prefixWord ++ tailWord_8312736).sum := by decide
  have hdescent : baseEnd_8312736 < baseStart_8312736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312753 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_8312753 : Nat := 118140960795 + 8312753 * 2 ^ 59
def prefixEnd_8312753 : Nat := 4983230072969 + 3 ^ 40 * 8312753 * 2
def baseEnd_8312753 : Nat := 4268437851104420049357851

theorem tailTrace_8312753 : CollatzResearch.WordTrace tailWord_8312753 prefixEnd_8312753 4268437851104420049357851 := by
  unfold tailWord_8312753
  simp only [CollatzResearch.WordTrace]
  refine ⟨303191010053323061029006913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202127340035548707352671275 303191010053323061029006913)
  ·
    refine ⟨227393257539992295771755185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303191010053323061029006913 227393257539992295771755185)
    ·
      refine ⟨170544943154994221828816389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227393257539992295771755185 170544943154994221828816389)
      ·
        refine ⟨31977176841561416592903073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170544943154994221828816389 31977176841561416592903073)
        ·
          refine ⟨23982882631171062444677305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31977176841561416592903073 23982882631171062444677305)
          ·
            refine ⟨17987161973378296833507979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23982882631171062444677305 17987161973378296833507979)
            ·
              refine ⟨26980742960067445250261969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987161973378296833507979 26980742960067445250261969)
              ·
                refine ⟨20235557220050583937696477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26980742960067445250261969 20235557220050583937696477)
                ·
                  refine ⟨7588333957518968976636179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20235557220050583937696477 7588333957518968976636179)
                  ·
                    refine ⟨11382500936278453464954269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588333957518968976636179 11382500936278453464954269)
                    ·
                      refine ⟨4268437851104420049357851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382500936278453464954269 4268437851104420049357851)
                      ·
                        rfl

theorem cell23_8312753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_8312753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312753 prefixEnd_8312753 := by exact prefixLift 8312753
  have htrace : WordTrace (prefixWord ++ tailWord_8312753) baseStart_8312753 baseEnd_8312753 := by
    simpa [prefixWord, tailWord_8312753, baseEnd_8312753] using wordTrace_append hprefix tailTrace_8312753
  have hstable : (prefixWord ++ tailWord_8312753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312753).length < 2 ^ (prefixWord ++ tailWord_8312753).sum := by decide
  have hdescent : baseEnd_8312753 < baseStart_8312753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312779 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5]
def baseStart_8312779 : Nat := 118140960795 + 8312779 * 2 ^ 59
def prefixEnd_8312779 : Nat := 4983230072969 + 3 ^ 40 * 8312779 * 2
def baseEnd_8312779 : Nat := 4268451201601436947632731

theorem tailTrace_8312779 : CollatzResearch.WordTrace tailWord_8312779 prefixEnd_8312779 4268451201601436947632731 := by
  unfold tailWord_8312779
  simp only [CollatzResearch.WordTrace]
  refine ⟨303191958351228867469453391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202127972234152578312968927 303191958351228867469453391)
  ·
    refine ⟨454787937526843301204180087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303191958351228867469453391 454787937526843301204180087)
    ·
      refine ⟨682181906290264951806270131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454787937526843301204180087 682181906290264951806270131)
      ·
        refine ⟨1023272859435397427709405197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682181906290264951806270131 1023272859435397427709405197)
        ·
          refine ⟨383727322288274035391026949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1023272859435397427709405197 383727322288274035391026949)
          ·
            refine ⟨71948872929051381635817553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383727322288274035391026949 71948872929051381635817553)
            ·
              refine ⟨53961654696788536226863165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71948872929051381635817553 53961654696788536226863165)
              ·
                refine ⟨20235620511295701085073687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53961654696788536226863165 20235620511295701085073687)
                ·
                  refine ⟨30353430766943551627610531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20235620511295701085073687 30353430766943551627610531)
                  ·
                    refine ⟨45530146150415327441415797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30353430766943551627610531 45530146150415327441415797)
                    ·
                      refine ⟨4268451201601436947632731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45530146150415327441415797 4268451201601436947632731)
                      ·
                        rfl

theorem cell23_8312779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].length) (baseStart_8312779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312779 prefixEnd_8312779 := by exact prefixLift 8312779
  have htrace : WordTrace (prefixWord ++ tailWord_8312779) baseStart_8312779 baseEnd_8312779 := by
    simpa [prefixWord, tailWord_8312779, baseEnd_8312779] using wordTrace_append hprefix tailTrace_8312779
  have hstable : (prefixWord ++ tailWord_8312779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312779).length < 2 ^ (prefixWord ++ tailWord_8312779).sum := by decide
  have hdescent : baseEnd_8312779 < baseStart_8312779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312830 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_8312830 : Nat := 118140960795 + 8312830 * 2 ^ 59
def prefixEnd_8312830 : Nat := 4983230072969 + 3 ^ 40 * 8312830 * 2
def baseEnd_8312830 : Nat := 4268477389114816248094997

theorem tailTrace_8312830 : CollatzResearch.WordTrace tailWord_8312830 prefixEnd_8312830 4268477389114816248094997 := by
  unfold tailWord_8312830
  simp only [CollatzResearch.WordTrace]
  refine ⟨37899227309255512897444993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202129212316029402119706629 37899227309255512897444993)
  ·
    refine ⟨28424420481941634673083745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37899227309255512897444993 28424420481941634673083745)
    ·
      refine ⟨21318315361456226004812809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28424420481941634673083745 21318315361456226004812809)
      ·
        refine ⟨15988736521092169503609607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21318315361456226004812809 15988736521092169503609607)
        ·
          refine ⟨23983104781638254255414411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15988736521092169503609607 23983104781638254255414411)
          ·
            refine ⟨35974657172457381383121617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23983104781638254255414411 35974657172457381383121617)
            ·
              refine ⟨26980992879343036037341213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35974657172457381383121617 26980992879343036037341213)
              ·
                refine ⟨10117872329753638514002955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26980992879343036037341213 10117872329753638514002955)
                ·
                  refine ⟨15176808494630457771004433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10117872329753638514002955 15176808494630457771004433)
                  ·
                    refine ⟨11382606370972843328253325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15176808494630457771004433 11382606370972843328253325)
                    ·
                      refine ⟨4268477389114816248094997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382606370972843328253325 4268477389114816248094997)
                      ·
                        rfl

theorem cell23_8312830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_8312830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312830 prefixEnd_8312830 := by exact prefixLift 8312830
  have htrace : WordTrace (prefixWord ++ tailWord_8312830) baseStart_8312830 baseEnd_8312830 := by
    simpa [prefixWord, tailWord_8312830, baseEnd_8312830] using wordTrace_append hprefix tailTrace_8312830
  have hstable : (prefixWord ++ tailWord_8312830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312830).length < 2 ^ (prefixWord ++ tailWord_8312830).sum := by decide
  have hdescent : baseEnd_8312830 < baseStart_8312830 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312838 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_8312838 : Nat := 118140960795 + 8312838 * 2 ^ 59
def prefixEnd_8312838 : Nat := 4983230072969 + 3 ^ 40 * 8312838 * 2
def baseEnd_8312838 : Nat := 4268481496960052216794961

theorem tailTrace_8312838 : CollatzResearch.WordTrace tailWord_8312838 prefixEnd_8312838 4268481496960052216794961 := by
  unfold tailWord_8312838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474815945562972517057849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202129406838676747030567445 9474815945562972517057849)
  ·
    refine ⟨7106111959172229387793387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9474815945562972517057849 7106111959172229387793387)
    ·
      refine ⟨10659167938758344081690081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7106111959172229387793387 10659167938758344081690081)
      ·
        refine ⟨7994375954068758061267561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10659167938758344081690081 7994375954068758061267561)
        ·
          refine ⟨5995781965551568545950671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994375954068758061267561 5995781965551568545950671)
          ·
            refine ⟨8993672948327352818926007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995781965551568545950671 8993672948327352818926007)
            ·
              refine ⟨13490509422491029228389011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993672948327352818926007 13490509422491029228389011)
              ·
                refine ⟨20235764133736543842583517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13490509422491029228389011 20235764133736543842583517)
                ·
                  refine ⟨7588411550151203940968819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20235764133736543842583517 7588411550151203940968819)
                  ·
                    refine ⟨11382617325226805911453229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588411550151203940968819 11382617325226805911453229)
                    ·
                      refine ⟨4268481496960052216794961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382617325226805911453229 4268481496960052216794961)
                      ·
                        rfl

theorem cell23_8312838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_8312838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312838 prefixEnd_8312838 := by exact prefixLift 8312838
  have htrace : WordTrace (prefixWord ++ tailWord_8312838) baseStart_8312838 baseEnd_8312838 := by
    simpa [prefixWord, tailWord_8312838, baseEnd_8312838] using wordTrace_append hprefix tailTrace_8312838
  have hstable : (prefixWord ++ tailWord_8312838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312838).length < 2 ^ (prefixWord ++ tailWord_8312838).sum := by decide
  have hdescent : baseEnd_8312838 < baseStart_8312838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312843 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 3]
def baseStart_8312843 : Nat := 118140960795 + 8312843 * 2 ^ 59
def prefixEnd_8312843 : Nat := 4983230072969 + 3 ^ 40 * 8312843 * 2
def baseEnd_8312843 : Nat := 4268484064363324697232437

theorem tailTrace_8312843 : CollatzResearch.WordTrace tailWord_8312843 prefixEnd_8312843 4268484064363324697232437 := by
  unfold tailWord_8312843
  simp only [CollatzResearch.WordTrace]
  refine ⟨303194292622997006399783183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202129528415331337599855455 303194292622997006399783183)
  ·
    refine ⟨454791438934495509599674775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303194292622997006399783183 454791438934495509599674775)
    ·
      refine ⟨682187158401743264399512163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454791438934495509599674775 682187158401743264399512163)
      ·
        refine ⟨1023280737602614896599268245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682187158401743264399512163 1023280737602614896599268245)
        ·
          refine ⟨47966284575122573278090699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1023280737602614896599268245 47966284575122573278090699)
          ·
            refine ⟨71949426862683859917136049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47966284575122573278090699 71949426862683859917136049)
            ·
              refine ⟨53962070147012894937852037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71949426862683859917136049 53962070147012894937852037)
              ·
                refine ⟨10117888152564917800847257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53962070147012894937852037 10117888152564917800847257)
                ·
                  refine ⟨7588416114423688350635443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10117888152564917800847257 7588416114423688350635443)
                  ·
                    refine ⟨11382624171635532525953165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588416114423688350635443 11382624171635532525953165)
                    ·
                      refine ⟨4268484064363324697232437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382624171635532525953165 4268484064363324697232437)
                      ·
                        rfl

theorem cell23_8312843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 3].length) (baseStart_8312843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312843 prefixEnd_8312843 := by exact prefixLift 8312843
  have htrace : WordTrace (prefixWord ++ tailWord_8312843) baseStart_8312843 baseEnd_8312843 := by
    simpa [prefixWord, tailWord_8312843, baseEnd_8312843] using wordTrace_append hprefix tailTrace_8312843
  have hstable : (prefixWord ++ tailWord_8312843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312843).length < 2 ^ (prefixWord ++ tailWord_8312843).sum := by decide
  have hdescent : baseEnd_8312843 < baseStart_8312843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312860 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_8312860 : Nat := 118140960795 + 8312860 * 2 ^ 59
def prefixEnd_8312860 : Nat := 4983230072969 + 3 ^ 40 * 8312860 * 2
def baseEnd_8312860 : Nat := 4268492793534451130719859

theorem tailTrace_8312860 : CollatzResearch.WordTrace tailWord_8312860 prefixEnd_8312860 4268492793534451130719859 := by
  unfold tailWord_8312860
  simp only [CollatzResearch.WordTrace]
  refine ⟨151597456331967709151576017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202129941775956945535434689 151597456331967709151576017)
  ·
    refine ⟨113698092248975781863682013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151597456331967709151576017 113698092248975781863682013)
    ·
      refine ⟨42636784593365918198880755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113698092248975781863682013 42636784593365918198880755)
      ·
        refine ⟨63955176890048877298321133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42636784593365918198880755 63955176890048877298321133)
        ·
          refine ⟨23983191333768328986870425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63955176890048877298321133 23983191333768328986870425)
          ·
            refine ⟨17987393500326246740152819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23983191333768328986870425 17987393500326246740152819)
            ·
              refine ⟨26981090250489370110229229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987393500326246740152819 26981090250489370110229229)
              ·
                refine ⟨10117908843933513791335961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26981090250489370110229229 10117908843933513791335961)
                ·
                  refine ⟨7588431632950135343501971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10117908843933513791335961 7588431632950135343501971)
                  ·
                    refine ⟨11382647449425203015252957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588431632950135343501971 11382647449425203015252957)
                    ·
                      refine ⟨4268492793534451130719859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382647449425203015252957 4268492793534451130719859)
                      ·
                        rfl

theorem cell23_8312860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_8312860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312860 prefixEnd_8312860 := by exact prefixLift 8312860
  have htrace : WordTrace (prefixWord ++ tailWord_8312860) baseStart_8312860 baseEnd_8312860 := by
    simpa [prefixWord, tailWord_8312860, baseEnd_8312860] using wordTrace_append hprefix tailTrace_8312860
  have hstable : (prefixWord ++ tailWord_8312860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312860).length < 2 ^ (prefixWord ++ tailWord_8312860).sum := by decide
  have hdescent : baseEnd_8312860 < baseStart_8312860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312879 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_8312879 : Nat := 118140960795 + 8312879 * 2 ^ 59
def prefixEnd_8312879 : Nat := 4983230072969 + 3 ^ 40 * 8312879 * 2
def baseEnd_8312879 : Nat := 4268502549666886556382271

theorem tailTrace_8312879 : CollatzResearch.WordTrace tailWord_8312879 prefixEnd_8312879 4268502549666886556382271 := by
  unfold tailWord_8312879
  simp only [CollatzResearch.WordTrace]
  refine ⟨303195605650866584548093691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202130403767244389698729127 303195605650866584548093691)
  ·
    refine ⟨454793408476299876822140537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303195605650866584548093691 454793408476299876822140537)
    ·
      refine ⟨341095056357224907616605403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454793408476299876822140537 341095056357224907616605403)
      ·
        refine ⟨511642584535837361424908105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341095056357224907616605403 511642584535837361424908105)
        ·
          refine ⟨383731938401878021068681079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511642584535837361424908105 383731938401878021068681079)
          ·
            refine ⟨575597907602817031603021619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383731938401878021068681079 575597907602817031603021619)
            ·
              refine ⟨863396861404225547404532429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575597907602817031603021619 863396861404225547404532429)
              ·
                refine ⟨323773823026584580276699661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863396861404225547404532429 323773823026584580276699661)
                ·
                  refine ⟨121415183634969217603762373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323773823026584580276699661 121415183634969217603762373)
                  ·
                    refine ⟨22765346931556728300705445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121415183634969217603762373 22765346931556728300705445)
                    ·
                      refine ⟨4268502549666886556382271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22765346931556728300705445 4268502549666886556382271)
                      ·
                        rfl

theorem cell23_8312879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_8312879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312879 prefixEnd_8312879 := by exact prefixLift 8312879
  have htrace : WordTrace (prefixWord ++ tailWord_8312879) baseStart_8312879 baseEnd_8312879 := by
    simpa [prefixWord, tailWord_8312879, baseEnd_8312879] using wordTrace_append hprefix tailTrace_8312879
  have hstable : (prefixWord ++ tailWord_8312879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312879).length < 2 ^ (prefixWord ++ tailWord_8312879).sum := by decide
  have hdescent : baseEnd_8312879 < baseStart_8312879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312883 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 6, 2, 2]
def baseStart_8312883 : Nat := 118140960795 + 8312883 * 2 ^ 59
def prefixEnd_8312883 : Nat := 4983230072969 + 3 ^ 40 * 8312883 * 2
def baseEnd_8312883 : Nat := 4268504603589504540732253

theorem tailTrace_8312883 : CollatzResearch.WordTrace tailWord_8312883 prefixEnd_8312883 4268504603589504540732253 := by
  unfold tailWord_8312883
  simp only [CollatzResearch.WordTrace]
  refine ⟨303195751542852093231239303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202130501028568062154159535 303195751542852093231239303)
  ·
    refine ⟨454793627314278139846858955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303195751542852093231239303 454793627314278139846858955)
    ·
      refine ⟨682190440971417209770288433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454793627314278139846858955 682190440971417209770288433)
      ·
        refine ⟨511642830728562907327716325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682190440971417209770288433 511642830728562907327716325)
        ·
          refine ⟨95933030761605545123946811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511642830728562907327716325 95933030761605545123946811)
          ·
            refine ⟨143899546142408317685920217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95933030761605545123946811 143899546142408317685920217)
            ·
              refine ⟨107924659606806238264440163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143899546142408317685920217 107924659606806238264440163)
              ·
                refine ⟨161886989410209357396660245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107924659606806238264440163 161886989410209357396660245)
                ·
                  refine ⟨7588452628603563627968449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161886989410209357396660245 7588452628603563627968449)
                  ·
                    refine ⟨5691339471452672720976337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588452628603563627968449 5691339471452672720976337)
                    ·
                      refine ⟨4268504603589504540732253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691339471452672720976337 4268504603589504540732253)
                      ·
                        rfl

theorem cell23_8312883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 2, 2].length) (baseStart_8312883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312883 prefixEnd_8312883 := by exact prefixLift 8312883
  have htrace : WordTrace (prefixWord ++ tailWord_8312883) baseStart_8312883 baseEnd_8312883 := by
    simpa [prefixWord, tailWord_8312883, baseEnd_8312883] using wordTrace_append hprefix tailTrace_8312883
  have hstable : (prefixWord ++ tailWord_8312883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312883).length < 2 ^ (prefixWord ++ tailWord_8312883).sum := by decide
  have hdescent : baseEnd_8312883 < baseStart_8312883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312976 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_8312976 : Nat := 118140960795 + 8312976 * 2 ^ 59
def prefixEnd_8312976 : Nat := 4983230072969 + 3 ^ 40 * 8312976 * 2
def baseEnd_8312976 : Nat := 4268552357290372676869325

theorem tailTrace_8312976 : CollatzResearch.WordTrace tailWord_8312976 prefixEnd_8312976 4268552357290372676869325 := by
  unfold tailWord_8312976
  simp only [CollatzResearch.WordTrace]
  refine ⟨151599571765757585057187391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202132762354343446742916521 151599571765757585057187391)
  ·
    refine ⟨227399357648636377585781087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151599571765757585057187391 227399357648636377585781087)
    ·
      refine ⟨341099036472954566378671631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227399357648636377585781087 341099036472954566378671631)
      ·
        refine ⟨511648554709431849568007447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341099036472954566378671631 511648554709431849568007447)
        ·
          refine ⟨767472832064147774352011171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511648554709431849568007447 767472832064147774352011171)
          ·
            refine ⟨1151209248096221661528016757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767472832064147774352011171 1151209248096221661528016757)
            ·
              refine ⟨107925867009020780768251571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1151209248096221661528016757 107925867009020780768251571)
              ·
                refine ⟨161888800513531171152377357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107925867009020780768251571 161888800513531171152377357)
                ·
                  refine ⟨60708300192574189182141509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161888800513531171152377357 60708300192574189182141509)
                  ·
                    refine ⟨11382806286107660471651533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60708300192574189182141509 11382806286107660471651533)
                    ·
                      refine ⟨4268552357290372676869325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382806286107660471651533 4268552357290372676869325)
                      ·
                        rfl

theorem cell23_8312976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_8312976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312976 prefixEnd_8312976 := by exact prefixLift 8312976
  have htrace : WordTrace (prefixWord ++ tailWord_8312976) baseStart_8312976 baseEnd_8312976 := by
    simpa [prefixWord, tailWord_8312976, baseEnd_8312976] using wordTrace_append hprefix tailTrace_8312976
  have hstable : (prefixWord ++ tailWord_8312976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312976).length < 2 ^ (prefixWord ++ tailWord_8312976).sum := by decide
  have hdescent : baseEnd_8312976 < baseStart_8312976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8312993 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_8312993 : Nat := 118140960795 + 8312993 * 2 ^ 59
def prefixEnd_8312993 : Nat := 4983230072969 + 3 ^ 40 * 8312993 * 2
def baseEnd_8312993 : Nat := 4268561086461499110356747

theorem tailTrace_8312993 : CollatzResearch.WordTrace tailWord_8312993 prefixEnd_8312993 4268561086461499110356747 := by
  unfold tailWord_8312993
  simp only [CollatzResearch.WordTrace]
  refine ⟨303199763572453582017743633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202133175714969054678495755 303199763572453582017743633)
  ·
    refine ⟨227399822679340186513307725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303199763572453582017743633 227399822679340186513307725)
    ·
      refine ⟨85274933504752569942490397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227399822679340186513307725 85274933504752569942490397)
      ·
        refine ⟨31978100064282213728433899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85274933504752569942490397 31978100064282213728433899)
        ·
          refine ⟨47967150096423320592650849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31978100064282213728433899 47967150096423320592650849)
          ·
            refine ⟨35975362572317490444488137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47967150096423320592650849 35975362572317490444488137)
            ·
              refine ⟨26981521929238117833366103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35975362572317490444488137 26981521929238117833366103)
              ·
                refine ⟨40472282893857176750049155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26981521929238117833366103 40472282893857176750049155)
                ·
                  refine ⟨60708424340785765125073733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40472282893857176750049155 60708424340785765125073733)
                  ·
                    refine ⟨11382829563897330960951325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60708424340785765125073733 11382829563897330960951325)
                    ·
                      refine ⟨4268561086461499110356747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382829563897330960951325 4268561086461499110356747)
                      ·
                        rfl

theorem cell23_8312993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_8312993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8312993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8312993 prefixEnd_8312993 := by exact prefixLift 8312993
  have htrace : WordTrace (prefixWord ++ tailWord_8312993) baseStart_8312993 baseEnd_8312993 := by
    simpa [prefixWord, tailWord_8312993, baseEnd_8312993] using wordTrace_append hprefix tailTrace_8312993
  have hstable : (prefixWord ++ tailWord_8312993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8312993).length < 2 ^ (prefixWord ++ tailWord_8312993).sum := by decide
  have hdescent : baseEnd_8312993 < baseStart_8312993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8312993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313017 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 1, 4]
def baseStart_8313017 : Nat := 118140960795 + 8313017 * 2 ^ 59
def prefixEnd_8313017 : Nat := 4983230072969 + 3 ^ 40 * 8313017 * 2
def baseEnd_8313017 : Nat := 1422857803332402338818879

theorem tailTrace_8313017 : CollatzResearch.WordTrace tailWord_8313017 prefixEnd_8313017 1422857803332402338818879 := by
  unfold tailWord_8313017
  simp only [CollatzResearch.WordTrace]
  refine ⟨303200638924366634116617305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202133759282911089411078203 303200638924366634116617305)
  ·
    refine ⟨227400479193274975587462979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303200638924366634116617305 227400479193274975587462979)
    ·
      refine ⟨341100718789912463381194469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227400479193274975587462979 341100718789912463381194469)
      ·
        refine ⟨63956384773108586883973963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341100718789912463381194469 63956384773108586883973963)
        ·
          refine ⟨95934577159662880325960945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63956384773108586883973963 95934577159662880325960945)
          ·
            refine ⟨71950932869747160244470709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95934577159662880325960945 71950932869747160244470709)
            ·
              refine ⟨6745399956538796272919129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71950932869747160244470709 6745399956538796272919129)
              ·
                refine ⟨5059049967404097204689347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745399956538796272919129 5059049967404097204689347)
                ·
                  refine ⟨7588574951106145807034021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059049967404097204689347 7588574951106145807034021)
                  ·
                    refine ⟨1422857803332402338818879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7588574951106145807034021 1422857803332402338818879)
                    ·
                      rfl

theorem cell23_8313017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 4].length) (baseStart_8313017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313017 prefixEnd_8313017 := by exact prefixLift 8313017
  have htrace : WordTrace (prefixWord ++ tailWord_8313017) baseStart_8313017 baseEnd_8313017 := by
    simpa [prefixWord, tailWord_8313017, baseEnd_8313017] using wordTrace_append hprefix tailTrace_8313017
  have hstable : (prefixWord ++ tailWord_8313017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313017).length < 2 ^ (prefixWord ++ tailWord_8313017).sum := by decide
  have hdescent : baseEnd_8313017 < baseStart_8313017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313033 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 1, 5, 2]
def baseStart_8313033 : Nat := 118140960795 + 8313033 * 2 ^ 59
def prefixEnd_8313033 : Nat := 4983230072969 + 3 ^ 40 * 8313033 * 2
def baseEnd_8313033 : Nat := 4268581625687678953856563

theorem tailTrace_8313033 : CollatzResearch.WordTrace tailWord_8313033 prefixEnd_8313033 4268581625687678953856563 := by
  unfold tailWord_8313033
  simp only [CollatzResearch.WordTrace]
  refine ⟨303201222492308668849199753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202134148328205779232799835 303201222492308668849199753)
  ·
    refine ⟨227400916869231501636899815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303201222492308668849199753 227400916869231501636899815)
    ·
      refine ⟨341101375303847252455349723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227400916869231501636899815 341101375303847252455349723)
      ·
        refine ⟨511652062955770878683024585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341101375303847252455349723 511652062955770878683024585)
        ·
          refine ⟨383739047216828159012268439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511652062955770878683024585 383739047216828159012268439)
          ·
            refine ⟨575608570825242238518402659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383739047216828159012268439 575608570825242238518402659)
            ·
              refine ⟨863412856237863357777603989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575608570825242238518402659 863412856237863357777603989)
              ·
                refine ⟨40472477636149844895825187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 863412856237863357777603989 40472477636149844895825187)
                ·
                  refine ⟨60708716454224767343737781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40472477636149844895825187 60708716454224767343737781)
                  ·
                    refine ⟨5691442167583571938475417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60708716454224767343737781 5691442167583571938475417)
                    ·
                      refine ⟨4268581625687678953856563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691442167583571938475417 4268581625687678953856563)
                      ·
                        rfl

theorem cell23_8313033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 5, 2].length) (baseStart_8313033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313033 prefixEnd_8313033 := by exact prefixLift 8313033
  have htrace : WordTrace (prefixWord ++ tailWord_8313033) baseStart_8313033 baseEnd_8313033 := by
    simpa [prefixWord, tailWord_8313033, baseEnd_8313033] using wordTrace_append hprefix tailTrace_8313033
  have hstable : (prefixWord ++ tailWord_8313033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313033).length < 2 ^ (prefixWord ++ tailWord_8313033).sum := by decide
  have hdescent : baseEnd_8313033 < baseStart_8313033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313050 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2]
def baseStart_8313050 : Nat := 118140960795 + 8313050 * 2 ^ 59
def prefixEnd_8313050 : Nat := 4983230072969 + 3 ^ 40 * 8313050 * 2
def baseEnd_8313050 : Nat := 4268590354858805387343985

theorem tailTrace_8313050 : CollatzResearch.WordTrace tailWord_8313050 prefixEnd_8313050 4268590354858805387343985 := by
  unfold tailWord_8313050
  simp only [CollatzResearch.WordTrace]
  refine ⟨75800460633311770188142151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202134561688831387168379069 75800460633311770188142151)
  ·
    refine ⟨113700690949967655282213227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75800460633311770188142151 113700690949967655282213227)
    ·
      refine ⟨170551036424951482923319841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113700690949967655282213227 170551036424951482923319841)
      ·
        refine ⟨127913277318713612192489881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170551036424951482923319841 127913277318713612192489881)
        ·
          refine ⟨95934957989035209144367411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127913277318713612192489881 95934957989035209144367411)
          ·
            refine ⟨143902436983552813716551117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95934957989035209144367411 143902436983552813716551117)
            ·
              refine ⟨53963413868832305143706669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143902436983552813716551117 53963413868832305143706669)
              ·
                refine ⟨20236280200812114428890001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53963413868832305143706669 20236280200812114428890001)
                ·
                  refine ⟨15177210150609085821667501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20236280200812114428890001 15177210150609085821667501)
                  ·
                    refine ⟨5691453806478407183125313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15177210150609085821667501 5691453806478407183125313)
                    ·
                      refine ⟨4268590354858805387343985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691453806478407183125313 4268590354858805387343985)
                      ·
                        rfl

theorem cell23_8313050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_8313050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313050 prefixEnd_8313050 := by exact prefixLift 8313050
  have htrace : WordTrace (prefixWord ++ tailWord_8313050) baseStart_8313050 baseEnd_8313050 := by
    simpa [prefixWord, tailWord_8313050, baseEnd_8313050] using wordTrace_append hprefix tailTrace_8313050
  have hstable : (prefixWord ++ tailWord_8313050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313050).length < 2 ^ (prefixWord ++ tailWord_8313050).sum := by decide
  have hdescent : baseEnd_8313050 < baseStart_8313050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313057 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_8313057 : Nat := 118140960795 + 8313057 * 2 ^ 59
def prefixEnd_8313057 : Nat := 4983230072969 + 3 ^ 40 * 8313057 * 2
def baseEnd_8313057 : Nat := 4268593949223386859956453

theorem tailTrace_8313057 : CollatzResearch.WordTrace tailWord_8313057 prefixEnd_8313057 4268593949223386859956453 := by
  unfold tailWord_8313057
  simp only [CollatzResearch.WordTrace]
  refine ⟨303202097844221720948073425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202134731896147813965382283 303202097844221720948073425)
  ·
    refine ⟨227401573383166290711055069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303202097844221720948073425 227401573383166290711055069)
    ·
      refine ⟨85275590018687359016645651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227401573383166290711055069 85275590018687359016645651)
      ·
        refine ⟨127913385028031038524968477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85275590018687359016645651 127913385028031038524968477)
        ·
          refine ⟨47967519385511639446863179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127913385028031038524968477 47967519385511639446863179)
          ·
            refine ⟨71951279078267459170294769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47967519385511639446863179 71951279078267459170294769)
            ·
              refine ⟨53963459308700594377721077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71951279078267459170294769 53963459308700594377721077)
              ·
                refine ⟨5059074310190680722911351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53963459308700594377721077 5059074310190680722911351)
                ·
                  refine ⟨7588611465286021084367027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059074310190680722911351 7588611465286021084367027)
                  ·
                    refine ⟨11382917197929031626550541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588611465286021084367027 11382917197929031626550541)
                    ·
                      refine ⟨4268593949223386859956453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382917197929031626550541 4268593949223386859956453)
                      ·
                        rfl

theorem cell23_8313057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_8313057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313057 prefixEnd_8313057 := by exact prefixLift 8313057
  have htrace : WordTrace (prefixWord ++ tailWord_8313057) baseStart_8313057 baseEnd_8313057 := by
    simpa [prefixWord, tailWord_8313057, baseEnd_8313057] using wordTrace_append hprefix tailTrace_8313057
  have hstable : (prefixWord ++ tailWord_8313057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313057).length < 2 ^ (prefixWord ++ tailWord_8313057).sum := by decide
  have hdescent : baseEnd_8313057 < baseStart_8313057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313073 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 4, 4]
def baseStart_8313073 : Nat := 118140960795 + 8313073 * 2 ^ 59
def prefixEnd_8313073 : Nat := 4983230072969 + 3 ^ 40 * 8313073 * 2
def baseEnd_8313073 : Nat := 1422867388304619599118793

theorem tailTrace_8313073 : CollatzResearch.WordTrace tailWord_8313073 prefixEnd_8313073 1422867388304619599118793 := by
  unfold tailWord_8313073
  simp only [CollatzResearch.WordTrace]
  refine ⟨303202681412163755680655873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202135120941442503787103915 303202681412163755680655873)
  ·
    refine ⟨227402011059122816760491905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303202681412163755680655873 227402011059122816760491905)
    ·
      refine ⟨170551508294342112570368929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227402011059122816760491905 170551508294342112570368929)
      ·
        refine ⟨127913631220756584427776697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170551508294342112570368929 127913631220756584427776697)
        ·
          refine ⟨95935223415567438320832523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127913631220756584427776697 95935223415567438320832523)
          ·
            refine ⟨143902835123351157481248785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95935223415567438320832523 143902835123351157481248785)
            ·
              refine ⟨107927126342513368110936589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143902835123351157481248785 107927126342513368110936589)
              ·
                refine ⟨40472672378442513041601221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107927126342513368110936589 40472672378442513041601221)
                ·
                  refine ⟨7588626070957971195300229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40472672378442513041601221 7588626070957971195300229)
                  ·
                    refine ⟨1422867388304619599118793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7588626070957971195300229 1422867388304619599118793)
                    ·
                      rfl

theorem cell23_8313073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_8313073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313073 prefixEnd_8313073 := by exact prefixLift 8313073
  have htrace : WordTrace (prefixWord ++ tailWord_8313073) baseStart_8313073 baseEnd_8313073 := by
    simpa [prefixWord, tailWord_8313073, baseEnd_8313073] using wordTrace_append hprefix tailTrace_8313073
  have hstable : (prefixWord ++ tailWord_8313073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313073).length < 2 ^ (prefixWord ++ tailWord_8313073).sum := by decide
  have hdescent : baseEnd_8313073 < baseStart_8313073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313074 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_8313074 : Nat := 118140960795 + 8313074 * 2 ^ 59
def prefixEnd_8313074 : Nat := 4983230072969 + 3 ^ 40 * 8313074 * 2
def baseEnd_8313074 : Nat := 4268602678394513293443875

theorem tailTrace_8313074 : CollatzResearch.WordTrace tailWord_8313074 prefixEnd_8313074 4268602678394513293443875 := by
  unfold tailWord_8313074
  simp only [CollatzResearch.WordTrace]
  refine ⟨75800679471290033212860569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202135145256773421900961517 75800679471290033212860569)
  ·
    refine ⟨56850509603467524909645427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75800679471290033212860569 56850509603467524909645427)
    ·
      refine ⟨85275764405201287364468141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56850509603467524909645427 85275764405201287364468141)
      ·
        refine ⟨31978411651950482761675553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85275764405201287364468141 31978411651950482761675553)
        ·
          refine ⟨23983808738962862071256665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31978411651950482761675553 23983808738962862071256665)
          ·
            refine ⟨17987856554222146553442499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23983808738962862071256665 17987856554222146553442499)
            ·
              refine ⟨26981784831333219830163749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987856554222146553442499 26981784831333219830163749)
              ·
                refine ⟨5059084655874978718155703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26981784831333219830163749 5059084655874978718155703)
                ·
                  refine ⟨7588626983812468077233555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059084655874978718155703 7588626983812468077233555)
                  ·
                    refine ⟨11382940475718702115850333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588626983812468077233555 11382940475718702115850333)
                    ·
                      refine ⟨4268602678394513293443875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382940475718702115850333 4268602678394513293443875)
                      ·
                        rfl

theorem cell23_8313074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_8313074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313074 prefixEnd_8313074 := by exact prefixLift 8313074
  have htrace : WordTrace (prefixWord ++ tailWord_8313074) baseStart_8313074 baseEnd_8313074 := by
    simpa [prefixWord, tailWord_8313074, baseEnd_8313074] using wordTrace_append hprefix tailTrace_8313074
  have hstable : (prefixWord ++ tailWord_8313074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313074).length < 2 ^ (prefixWord ++ tailWord_8313074).sum := by decide
  have hdescent : baseEnd_8313074 < baseStart_8313074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313080 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 7, 2, 2]
def baseStart_8313080 : Nat := 118140960795 + 8313080 * 2 ^ 59
def prefixEnd_8313080 : Nat := 4983230072969 + 3 ^ 40 * 8313080 * 2
def baseEnd_8313080 : Nat := 4268605759278440269968847

theorem tailTrace_8313080 : CollatzResearch.WordTrace tailWord_8313080 prefixEnd_8313080 4268605759278440269968847 := by
  unfold tailWord_8313080
  simp only [CollatzResearch.WordTrace]
  refine ⟨151601468361569197938080347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202135291148758930584107129 151601468361569197938080347)
  ·
    refine ⟨227402202542353796907120521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151601468361569197938080347 227402202542353796907120521)
    ·
      refine ⟨170551651906765347680340391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227402202542353796907120521 170551651906765347680340391)
      ·
        refine ⟨255827477860148021520510587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170551651906765347680340391 255827477860148021520510587)
        ·
          refine ⟨383741216790222032280765881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255827477860148021520510587 383741216790222032280765881)
          ·
            refine ⟨287805912592666524210574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383741216790222032280765881 287805912592666524210574411)
            ·
              refine ⟨431708868888999786315861617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287805912592666524210574411 431708868888999786315861617)
              ·
                refine ⟨323781651666749839736896213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431708868888999786315861617 323781651666749839736896213)
                ·
                  refine ⟨7588632460939449368833505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 323781651666749839736896213 7588632460939449368833505)
                  ·
                    refine ⟨5691474345704587026625129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588632460939449368833505 5691474345704587026625129)
                    ·
                      refine ⟨4268605759278440269968847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691474345704587026625129 4268605759278440269968847)
                      ·
                        rfl

theorem cell23_8313080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_8313080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313080 prefixEnd_8313080 := by exact prefixLift 8313080
  have htrace : WordTrace (prefixWord ++ tailWord_8313080) baseStart_8313080 baseEnd_8313080 := by
    simpa [prefixWord, tailWord_8313080, baseEnd_8313080] using wordTrace_append hprefix tailTrace_8313080
  have hstable : (prefixWord ++ tailWord_8313080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313080).length < 2 ^ (prefixWord ++ tailWord_8313080).sum := by decide
  have hdescent : baseEnd_8313080 < baseStart_8313080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313090 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_8313090 : Nat := 118140960795 + 8313090 * 2 ^ 59
def prefixEnd_8313090 : Nat := 4983230072969 + 3 ^ 40 * 8313090 * 2
def baseEnd_8313090 : Nat := 1422870298028328410281267

theorem tailTrace_8313090 : CollatzResearch.WordTrace tailWord_8313090 prefixEnd_8313090 1422870298028328410281267 := by
  unfold tailWord_8313090
  simp only [CollatzResearch.WordTrace]
  refine ⟨75800825363275541896006181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202135534302068111722683149 75800825363275541896006181)
  ·
    refine ⟨14212654755614164105501159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75800825363275541896006181 14212654755614164105501159)
    ·
      refine ⟨21318982133421246158251739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14212654755614164105501159 21318982133421246158251739)
      ·
        refine ⟨31978473200131869237377609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21318982133421246158251739 31978473200131869237377609)
        ·
          refine ⟨23983854900098901928033207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31978473200131869237377609 23983854900098901928033207)
          ·
            refine ⟨35975782350148352892049811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23983854900098901928033207 35975782350148352892049811)
            ·
              refine ⟨53963673525222529338074717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35975782350148352892049811 53963673525222529338074717)
              ·
                refine ⟨20236377571958448501778019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53963673525222529338074717 20236377571958448501778019)
                ·
                  refine ⟨30354566357937672752667029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20236377571958448501778019 30354566357937672752667029)
                  ·
                    refine ⟨1422870298028328410281267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30354566357937672752667029 1422870298028328410281267)
                    ·
                      rfl

theorem cell23_8313090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_8313090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313090 prefixEnd_8313090 := by exact prefixLift 8313090
  have htrace : WordTrace (prefixWord ++ tailWord_8313090) baseStart_8313090 baseEnd_8313090 := by
    simpa [prefixWord, tailWord_8313090, baseEnd_8313090] using wordTrace_append hprefix tailTrace_8313090
  have hstable : (prefixWord ++ tailWord_8313090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313090).length < 2 ^ (prefixWord ++ tailWord_8313090).sum := by decide
  have hdescent : baseEnd_8313090 < baseStart_8313090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313097 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 3, 2, 2]
def baseStart_8313097 : Nat := 118140960795 + 8313097 * 2 ^ 59
def prefixEnd_8313097 : Nat := 4983230072969 + 3 ^ 40 * 8313097 * 2
def baseEnd_8313097 : Nat := 4268614488449566703456269

theorem tailTrace_8313097 : CollatzResearch.WordTrace tailWord_8313097 prefixEnd_8313097 4268614488449566703456269 := by
  unfold tailWord_8313097
  simp only [CollatzResearch.WordTrace]
  refine ⟨303203556764076807779529545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202135704509384538519686363 303203556764076807779529545)
  ·
    refine ⟨227402667573057605834647159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303203556764076807779529545 227402667573057605834647159)
    ·
      refine ⟨341104001359586408751970739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227402667573057605834647159 341104001359586408751970739)
      ·
        refine ⟨511656002039379613127956109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341104001359586408751970739 511656002039379613127956109)
        ·
          refine ⟨191871000764767354922983541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511656002039379613127956109 191871000764767354922983541)
          ·
            refine ⟨17987906321696939524029707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191871000764767354922983541 17987906321696939524029707)
            ·
              refine ⟨26981859482545409286044561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987906321696939524029707 26981859482545409286044561)
              ·
                refine ⟨20236394611909056964533421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26981859482545409286044561 20236394611909056964533421)
                ·
                  refine ⟨7588647979465896361700033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20236394611909056964533421 7588647979465896361700033)
                  ·
                    refine ⟨5691485984599422271275025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588647979465896361700033 5691485984599422271275025)
                    ·
                      refine ⟨4268614488449566703456269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691485984599422271275025 4268614488449566703456269)
                      ·
                        rfl

theorem cell23_8313097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 2, 2].length) (baseStart_8313097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313097 prefixEnd_8313097 := by exact prefixLift 8313097
  have htrace : WordTrace (prefixWord ++ tailWord_8313097) baseStart_8313097 baseEnd_8313097 := by
    simpa [prefixWord, tailWord_8313097, baseEnd_8313097] using wordTrace_append hprefix tailTrace_8313097
  have hstable : (prefixWord ++ tailWord_8313097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313097).length < 2 ^ (prefixWord ++ tailWord_8313097).sum := by decide
  have hdescent : baseEnd_8313097 < baseStart_8313097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313100 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_8313100 : Nat := 118140960795 + 8313100 * 2 ^ 59
def prefixEnd_8313100 : Nat := 4983230072969 + 3 ^ 40 * 8313100 * 2
def baseEnd_8313100 : Nat := 4268616028891530191718755

theorem tailTrace_8313100 : CollatzResearch.WordTrace tailWord_8313100 prefixEnd_8313100 4268616028891530191718755 := by
  unfold tailWord_8313100
  simp only [CollatzResearch.WordTrace]
  refine ⟨151601833091532969645944377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202135777455377292861259169 151601833091532969645944377)
  ·
    refine ⟨113701374818649727234458283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151601833091532969645944377 113701374818649727234458283)
    ·
      refine ⟨170552062227974590851687425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113701374818649727234458283 170552062227974590851687425)
      ·
        refine ⟨127914046670980943138765569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170552062227974590851687425 127914046670980943138765569)
        ·
          refine ⟨95935535003235707354074177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127914046670980943138765569 95935535003235707354074177)
          ·
            refine ⟨71951651252426780515555633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95935535003235707354074177 71951651252426780515555633)
            ·
              refine ⟨53963738439320085386666725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71951651252426780515555633 53963738439320085386666725)
              ·
                refine ⟨10118200957372516010000011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53963738439320085386666725 10118200957372516010000011)
                ·
                  refine ⟨15177301436058774015000017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10118200957372516010000011 15177301436058774015000017)
                  ·
                    refine ⟨11382976077044080511250013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15177301436058774015000017 11382976077044080511250013)
                    ·
                      refine ⟨4268616028891530191718755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11382976077044080511250013 4268616028891530191718755)
                      ·
                        rfl

theorem cell23_8313100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_8313100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313100 prefixEnd_8313100 := by exact prefixLift 8313100
  have htrace : WordTrace (prefixWord ++ tailWord_8313100) baseStart_8313100 baseEnd_8313100 := by
    simpa [prefixWord, tailWord_8313100, baseEnd_8313100] using wordTrace_append hprefix tailTrace_8313100
  have hstable : (prefixWord ++ tailWord_8313100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313100).length < 2 ^ (prefixWord ++ tailWord_8313100).sum := by decide
  have hdescent : baseEnd_8313100 < baseStart_8313100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313114 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4]
def baseStart_8313114 : Nat := 118140960795 + 8313114 * 2 ^ 59
def prefixEnd_8313114 : Nat := 4983230072969 + 3 ^ 40 * 8313114 * 2
def baseEnd_8313114 : Nat := 4268623217620693136943691

theorem tailTrace_8313114 : CollatzResearch.WordTrace tailWord_8313114 prefixEnd_8313114 4268623217620693136943691 := by
  unfold tailWord_8313114
  simp only [CollatzResearch.WordTrace]
  refine ⟨75801044201253804920724599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202136117870010146455265597 75801044201253804920724599)
  ·
    refine ⟨113701566301880707381086899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75801044201253804920724599 113701566301880707381086899)
    ·
      refine ⟨170552349452821061071630349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113701566301880707381086899 170552349452821061071630349)
      ·
        refine ⟨63957131044807897901861381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170552349452821061071630349 63957131044807897901861381)
        ·
          refine ⟨11991962070901480856599009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63957131044807897901861381 11991962070901480856599009)
          ·
            refine ⟨8993971553176110642449257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991962070901480856599009 8993971553176110642449257)
            ·
              refine ⟨6745478664882082981836943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993971553176110642449257 6745478664882082981836943)
              ·
                refine ⟨10118217997323124472755415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745478664882082981836943 10118217997323124472755415)
                ·
                  refine ⟨15177326995984686709133123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10118217997323124472755415 15177326995984686709133123)
                  ·
                    refine ⟨22765990493977030063699685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15177326995984686709133123 22765990493977030063699685)
                    ·
                      refine ⟨4268623217620693136943691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22765990493977030063699685 4268623217620693136943691)
                      ·
                        rfl

theorem cell23_8313114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_8313114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313114 prefixEnd_8313114 := by exact prefixLift 8313114
  have htrace : WordTrace (prefixWord ++ tailWord_8313114) baseStart_8313114 baseEnd_8313114 := by
    simpa [prefixWord, tailWord_8313114, baseEnd_8313114] using wordTrace_append hprefix tailTrace_8313114
  have hstable : (prefixWord ++ tailWord_8313114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313114).length < 2 ^ (prefixWord ++ tailWord_8313114).sum := by decide
  have hdescent : baseEnd_8313114 < baseStart_8313114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313182 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_8313182 : Nat := 118140960795 + 8313182 * 2 ^ 59
def prefixEnd_8313182 : Nat := 4983230072969 + 3 ^ 40 * 8313182 * 2
def baseEnd_8313182 : Nat := 4268658134305198870893379

theorem tailTrace_8313182 : CollatzResearch.WordTrace tailWord_8313182 prefixEnd_8313182 4268658134305198870893379 := by
  unfold tailWord_8313182
  simp only [CollatzResearch.WordTrace]
  refine ⟨37900832121096108412046725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202137771312512578197582533 37900832121096108412046725)
  ·
    refine ⟨7106406022705520327258761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37900832121096108412046725 7106406022705520327258761)
    ·
      refine ⟨5329804517029140245444071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7106406022705520327258761 5329804517029140245444071)
      ·
        refine ⟨7994706775543710368166107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329804517029140245444071 7994706775543710368166107)
        ·
          refine ⟨11992060163315565552249161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994706775543710368166107 11992060163315565552249161)
          ·
            refine ⟨8994045122486674164186871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11992060163315565552249161 8994045122486674164186871)
            ·
              refine ⟨13491067683730011246280307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994045122486674164186871 13491067683730011246280307)
              ·
                refine ⟨20236601525595016869420461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491067683730011246280307 20236601525595016869420461)
                ·
                  refine ⟨7588725572098131326032673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20236601525595016869420461 7588725572098131326032673)
                  ·
                    refine ⟨5691544179073598494524505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588725572098131326032673 5691544179073598494524505)
                    ·
                      refine ⟨4268658134305198870893379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691544179073598494524505 4268658134305198870893379)
                      ·
                        rfl

theorem cell23_8313182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_8313182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313182 prefixEnd_8313182 := by exact prefixLift 8313182
  have htrace : WordTrace (prefixWord ++ tailWord_8313182) baseStart_8313182 baseEnd_8313182 := by
    simpa [prefixWord, tailWord_8313182, baseEnd_8313182] using wordTrace_append hprefix tailTrace_8313182
  have hstable : (prefixWord ++ tailWord_8313182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313182).length < 2 ^ (prefixWord ++ tailWord_8313182).sum := by decide
  have hdescent : baseEnd_8313182 < baseStart_8313182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313183 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_8313183 : Nat := 118140960795 + 8313183 * 2 ^ 59
def prefixEnd_8313183 : Nat := 4983230072969 + 3 ^ 40 * 8313183 * 2
def baseEnd_8313183 : Nat := 4268658647785853366980873

theorem tailTrace_8313183 : CollatzResearch.WordTrace tailWord_8313183 prefixEnd_8313183 4268658647785853366980873 := by
  unfold tailWord_8313183
  simp only [CollatzResearch.WordTrace]
  refine ⟨303206693441765244467160203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202137795627843496311440135 303206693441765244467160203)
  ·
    refine ⟨454810040162647866700740305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303206693441765244467160203 454810040162647866700740305)
    ·
      refine ⟨341107530121985900025555229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454810040162647866700740305 341107530121985900025555229)
      ·
        refine ⟨127915323795744712509583211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341107530121985900025555229 127915323795744712509583211)
        ·
          refine ⟨191872985693617068764374817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127915323795744712509583211 191872985693617068764374817)
          ·
            refine ⟨143904739270212801573281113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191872985693617068764374817 143904739270212801573281113)
            ·
              refine ⟨107928554452659601179960835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143904739270212801573281113 107928554452659601179960835)
              ·
                refine ⟨161892831678989401769941253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107928554452659601179960835 161892831678989401769941253)
                ·
                  refine ⟨30354905939810512831863985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161892831678989401769941253 30354905939810512831863985)
                  ·
                    refine ⟨22766179454857884623897989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30354905939810512831863985 22766179454857884623897989)
                    ·
                      refine ⟨4268658647785853366980873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22766179454857884623897989 4268658647785853366980873)
                      ·
                        rfl

theorem cell23_8313183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_8313183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313183 prefixEnd_8313183 := by exact prefixLift 8313183
  have htrace : WordTrace (prefixWord ++ tailWord_8313183) baseStart_8313183 baseEnd_8313183 := by
    simpa [prefixWord, tailWord_8313183, baseEnd_8313183] using wordTrace_append hprefix tailTrace_8313183
  have hstable : (prefixWord ++ tailWord_8313183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313183).length < 2 ^ (prefixWord ++ tailWord_8313183).sum := by decide
  have hdescent : baseEnd_8313183 < baseStart_8313183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313187 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 4, 2, 2]
def baseStart_8313187 : Nat := 118140960795 + 8313187 * 2 ^ 59
def prefixEnd_8313187 : Nat := 4983230072969 + 3 ^ 40 * 8313187 * 2
def baseEnd_8313187 : Nat := 4268660701708471351330855

theorem tailTrace_8313187 : CollatzResearch.WordTrace tailWord_8313187 prefixEnd_8313187 4268660701708471351330855 := by
  unfold tailWord_8313187
  simp only [CollatzResearch.WordTrace]
  refine ⟨303206839333750753150305815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202137892889167168766870543 303206839333750753150305815)
  ·
    refine ⟨454810259000626129725458723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303206839333750753150305815 454810259000626129725458723)
    ·
      refine ⟨682215388500939194588188085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454810259000626129725458723 682215388500939194588188085)
      ·
        refine ⟨63957692671963049492642633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 682215388500939194588188085 63957692671963049492642633)
        ·
          refine ⟨47968269503972287119481975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63957692671963049492642633 47968269503972287119481975)
          ·
            refine ⟨71952404255958430679222963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47968269503972287119481975 71952404255958430679222963)
            ·
              refine ⟨107928606383937646018834445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71952404255958430679222963 107928606383937646018834445)
              ·
                refine ⟨40473227393976617257062917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107928606383937646018834445 40473227393976617257062917)
                ·
                  refine ⟨7588730136370615735699297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40473227393976617257062917 7588730136370615735699297)
                  ·
                    refine ⟨5691547602277961801774473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588730136370615735699297 5691547602277961801774473)
                    ·
                      refine ⟨4268660701708471351330855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691547602277961801774473 4268660701708471351330855)
                      ·
                        rfl

theorem cell23_8313187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_8313187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313187 prefixEnd_8313187 := by exact prefixLift 8313187
  have htrace : WordTrace (prefixWord ++ tailWord_8313187) baseStart_8313187 baseEnd_8313187 := by
    simpa [prefixWord, tailWord_8313187, baseEnd_8313187] using wordTrace_append hprefix tailTrace_8313187
  have hstable : (prefixWord ++ tailWord_8313187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313187).length < 2 ^ (prefixWord ++ tailWord_8313187).sum := by decide
  have hdescent : baseEnd_8313187 < baseStart_8313187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313250 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_8313250 : Nat := 118140960795 + 8313250 * 2 ^ 59
def prefixEnd_8313250 : Nat := 4983230072969 + 3 ^ 40 * 8313250 * 2
def baseEnd_8313250 : Nat := 4268693050989704604843065

theorem tailTrace_8313250 : CollatzResearch.WordTrace tailWord_8313250 prefixEnd_8313250 4268693050989704604843065 := by
  unfold tailWord_8313250
  simp only [CollatzResearch.WordTrace]
  refine ⟨75802284283130628727462301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202139424755015009939899469 75802284283130628727462301)
  ·
    refine ⟨28425856606173985772798363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75802284283130628727462301 28425856606173985772798363)
    ·
      refine ⟨42638784909260978659197545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28425856606173985772798363 42638784909260978659197545)
      ·
        refine ⟨31979088681945733994398159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42638784909260978659197545 31979088681945733994398159)
        ·
          refine ⟨47968633022918600991597239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31979088681945733994398159 47968633022918600991597239)
          ·
            refine ⟨71952949534377901487395859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47968633022918600991597239 71952949534377901487395859)
            ·
              refine ⟨107929424301566852231093789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71952949534377901487395859 107929424301566852231093789)
              ·
                refine ⟨40473534113087569586660171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107929424301566852231093789 40473534113087569586660171)
                ·
                  refine ⟨60710301169631354379990257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40473534113087569586660171 60710301169631354379990257)
                  ·
                    refine ⟨45532725877223515784992693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60710301169631354379990257 45532725877223515784992693)
                    ·
                      refine ⟨4268693050989704604843065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45532725877223515784992693 4268693050989704604843065)
                      ·
                        rfl

theorem cell23_8313250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_8313250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313250 prefixEnd_8313250 := by exact prefixLift 8313250
  have htrace : WordTrace (prefixWord ++ tailWord_8313250) baseStart_8313250 baseEnd_8313250 := by
    simpa [prefixWord, tailWord_8313250, baseEnd_8313250] using wordTrace_append hprefix tailTrace_8313250
  have hstable : (prefixWord ++ tailWord_8313250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313250).length < 2 ^ (prefixWord ++ tailWord_8313250).sum := by decide
  have hdescent : baseEnd_8313250 < baseStart_8313250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313277 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_8313277 : Nat := 118140960795 + 8313277 * 2 ^ 59
def prefixEnd_8313277 : Nat := 4983230072969 + 3 ^ 40 * 8313277 * 2
def baseEnd_8313277 : Nat := 4268706914967375999205441

theorem tailTrace_8313277 : CollatzResearch.WordTrace tailWord_8313277 prefixEnd_8313277 4268706914967375999205441 := by
  unfold tailWord_8313277
  simp only [CollatzResearch.WordTrace]
  refine ⟨303210121903424698521082085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202140081268949799014054723 303210121903424698521082085)
  ·
    refine ⟨56851897856892130972702891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303210121903424698521082085 56851897856892130972702891)
    ·
      refine ⟨85277846785338196459054337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56851897856892130972702891 85277846785338196459054337)
      ·
        refine ⟨63958385089003647344290753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85277846785338196459054337 63958385089003647344290753)
        ·
          refine ⟨47968788816752735508218065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63958385089003647344290753 47968788816752735508218065)
          ·
            refine ⟨35976591612564551631163549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47968788816752735508218065 35976591612564551631163549)
            ·
              refine ⟨13491221854711706861686331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35976591612564551631163549 13491221854711706861686331)
              ·
                refine ⟨20236832782067560292529497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491221854711706861686331 20236832782067560292529497)
                ·
                  refine ⟨15177624586550670219397123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20236832782067560292529497 15177624586550670219397123)
                  ·
                    refine ⟨22766436879826005329095685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15177624586550670219397123 22766436879826005329095685)
                    ·
                      refine ⟨4268706914967375999205441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22766436879826005329095685 4268706914967375999205441)
                      ·
                        rfl

theorem cell23_8313277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_8313277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313277 prefixEnd_8313277 := by exact prefixLift 8313277
  have htrace : WordTrace (prefixWord ++ tailWord_8313277) baseStart_8313277 baseEnd_8313277 := by
    simpa [prefixWord, tailWord_8313277, baseEnd_8313277] using wordTrace_append hprefix tailTrace_8313277
  have hstable : (prefixWord ++ tailWord_8313277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313277).length < 2 ^ (prefixWord ++ tailWord_8313277).sum := by decide
  have hdescent : baseEnd_8313277 < baseStart_8313277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313283 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 8]
def baseStart_8313283 : Nat := 118140960795 + 8313283 * 2 ^ 59
def prefixEnd_8313283 : Nat := 4983230072969 + 3 ^ 40 * 8313283 * 2
def baseEnd_8313283 : Nat := 474301110650144775081157

theorem tailTrace_8313283 : CollatzResearch.WordTrace tailWord_8313283 prefixEnd_8313283 474301110650144775081157 := by
  unfold tailWord_8313283
  simp only [CollatzResearch.WordTrace]
  refine ⟨303210340741402961545800503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202140227160935307697200335 303210340741402961545800503)
  ·
    refine ⟨454815511112104442318700755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303210340741402961545800503 454815511112104442318700755)
    ·
      refine ⟨682223266668156663478051133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454815511112104442318700755 682223266668156663478051133)
      ·
        refine ⟨255833725000558748804269175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682223266668156663478051133 255833725000558748804269175)
        ·
          refine ⟨383750587500838123206403763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255833725000558748804269175 383750587500838123206403763)
          ·
            refine ⟨575625881251257184809605645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383750587500838123206403763 575625881251257184809605645)
            ·
              refine ⟨215859705469221444303602117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575625881251257184809605645 215859705469221444303602117)
              ·
                refine ⟨40473694775479020806925397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215859705469221444303602117 40473694775479020806925397)
                ·
                  refine ⟨474301110650144775081157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40473694775479020806925397 474301110650144775081157)
                  ·
                    rfl

theorem cell23_8313283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 8].length) (baseStart_8313283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313283 prefixEnd_8313283 := by exact prefixLift 8313283
  have htrace : WordTrace (prefixWord ++ tailWord_8313283) baseStart_8313283 baseEnd_8313283 := by
    simpa [prefixWord, tailWord_8313283, baseEnd_8313283] using wordTrace_append hprefix tailTrace_8313283
  have hstable : (prefixWord ++ tailWord_8313283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313283).length < 2 ^ (prefixWord ++ tailWord_8313283).sum := by decide
  have hdescent : baseEnd_8313283 < baseStart_8313283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313337 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 1, 5, 2]
def baseStart_8313337 : Nat := 118140960795 + 8313337 * 2 ^ 59
def prefixEnd_8313337 : Nat := 4983230072969 + 3 ^ 40 * 8313337 * 2
def baseEnd_8313337 : Nat := 4268737723806645764455165

theorem tailTrace_8313337 : CollatzResearch.WordTrace tailWord_8313337 prefixEnd_8313337 4268737723806645764455165 := by
  unfold tailWord_8313337
  simp only [CollatzResearch.WordTrace]
  refine ⟨303212310283207328768266265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202141540188804885845510843 303212310283207328768266265)
  ·
    refine ⟨227409232712405496576199699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303212310283207328768266265 227409232712405496576199699)
    ·
      refine ⟨341113849068608244864299549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227409232712405496576199699 341113849068608244864299549)
      ·
        refine ⟨127917693400728091824112331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341113849068608244864299549 127917693400728091824112331)
        ·
          refine ⟨191876540101092137736168497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127917693400728091824112331 191876540101092137736168497)
          ·
            refine ⟨143907405075819103302126373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191876540101092137736168497 143907405075819103302126373)
            ·
              refine ⟨26982638451716081869148695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143907405075819103302126373 26982638451716081869148695)
              ·
                refine ⟨40473957677574122803723043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26982638451716081869148695 40473957677574122803723043)
                ·
                  refine ⟨60710936516361184205584565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40473957677574122803723043 60710936516361184205584565)
                  ·
                    refine ⟨5691650298408861019273553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60710936516361184205584565 5691650298408861019273553)
                    ·
                      refine ⟨4268737723806645764455165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691650298408861019273553 4268737723806645764455165)
                      ·
                        rfl

theorem cell23_8313337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_8313337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313337 prefixEnd_8313337 := by exact prefixLift 8313337
  have htrace : WordTrace (prefixWord ++ tailWord_8313337) baseStart_8313337 baseEnd_8313337 := by
    simpa [prefixWord, tailWord_8313337, baseEnd_8313337] using wordTrace_append hprefix tailTrace_8313337
  have hstable : (prefixWord ++ tailWord_8313337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313337).length < 2 ^ (prefixWord ++ tailWord_8313337).sum := by decide
  have hdescent : baseEnd_8313337 < baseStart_8313337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313354 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_8313354 : Nat := 118140960795 + 8313354 * 2 ^ 59
def prefixEnd_8313354 : Nat := 4983230072969 + 3 ^ 40 * 8313354 * 2
def baseEnd_8313354 : Nat := 4268746452977772197942587

theorem tailTrace_8313354 : CollatzResearch.WordTrace tailWord_8313354 prefixEnd_8313354 4268746452977772197942587 := by
  unfold tailWord_8313354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75803232581036435167908779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202141953549430493781090077 75803232581036435167908779)
  ·
    refine ⟨113704848871554652751863169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75803232581036435167908779 113704848871554652751863169)
    ·
      refine ⟨85278636653665989563897377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113704848871554652751863169 85278636653665989563897377)
      ·
        refine ⟨63958977490249492172923033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85278636653665989563897377 63958977490249492172923033)
        ·
          refine ⟨47969233117687119129692275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63958977490249492172923033 47969233117687119129692275)
          ·
            refine ⟨71953849676530678694538413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47969233117687119129692275 71953849676530678694538413)
            ·
              refine ⟨26982693628699004510451905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71953849676530678694538413 26982693628699004510451905)
              ·
                refine ⟨20237020221524253382838929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26982693628699004510451905 20237020221524253382838929)
                ·
                  refine ⟨15177765166143190037129197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20237020221524253382838929 15177765166143190037129197)
                  ·
                    refine ⟨5691661937303696263923449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15177765166143190037129197 5691661937303696263923449)
                    ·
                      refine ⟨4268746452977772197942587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691661937303696263923449 4268746452977772197942587)
                      ·
                        rfl

theorem cell23_8313354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_8313354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313354 prefixEnd_8313354 := by exact prefixLift 8313354
  have htrace : WordTrace (prefixWord ++ tailWord_8313354) baseStart_8313354 baseEnd_8313354 := by
    simpa [prefixWord, tailWord_8313354, baseEnd_8313354] using wordTrace_append hprefix tailTrace_8313354
  have hstable : (prefixWord ++ tailWord_8313354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313354).length < 2 ^ (prefixWord ++ tailWord_8313354).sum := by decide
  have hdescent : baseEnd_8313354 < baseStart_8313354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313384 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_8313384 : Nat := 118140960795 + 8313384 * 2 ^ 59
def prefixEnd_8313384 : Nat := 4983230072969 + 3 ^ 40 * 8313384 * 2
def baseEnd_8313384 : Nat := 4268761857397407080567449

theorem tailTrace_8313384 : CollatzResearch.WordTrace tailWord_8313384 prefixEnd_8313384 4268761857397407080567449 := by
  unfold tailWord_8313384
  simp only [CollatzResearch.WordTrace]
  refine ⟨151607012257018527897613603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202142683009358037196818137 151607012257018527897613603)
  ·
    refine ⟨227410518385527791846420405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151607012257018527897613603 227410518385527791846420405)
    ·
      refine ⟨21319736098643230485601913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227410518385527791846420405 21319736098643230485601913)
      ·
        refine ⟨15989802073982422864201435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21319736098643230485601913 15989802073982422864201435)
        ·
          refine ⟨23984703110973634296302153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15989802073982422864201435 23984703110973634296302153)
          ·
            refine ⟨17988527333230225722226615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23984703110973634296302153 17988527333230225722226615)
            ·
              refine ⟨26982790999845338583339923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17988527333230225722226615 26982790999845338583339923)
              ·
                refine ⟨40474186499768007875009885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26982790999845338583339923 40474186499768007875009885)
                ·
                  refine ⟨15177819937413002953128707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40474186499768007875009885 15177819937413002953128707)
                  ·
                    refine ⟨22766729906119504429693061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15177819937413002953128707 22766729906119504429693061)
                    ·
                      refine ⟨4268761857397407080567449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22766729906119504429693061 4268761857397407080567449)
                      ·
                        rfl

theorem cell23_8313384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_8313384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313384 prefixEnd_8313384 := by exact prefixLift 8313384
  have htrace : WordTrace (prefixWord ++ tailWord_8313384) baseStart_8313384 baseEnd_8313384 := by
    simpa [prefixWord, tailWord_8313384, baseEnd_8313384] using wordTrace_append hprefix tailTrace_8313384
  have hstable : (prefixWord ++ tailWord_8313384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313384).length < 2 ^ (prefixWord ++ tailWord_8313384).sum := by decide
  have hdescent : baseEnd_8313384 < baseStart_8313384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313397 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_8313397 : Nat := 118140960795 + 8313397 * 2 ^ 59
def prefixEnd_8313397 : Nat := 4983230072969 + 3 ^ 40 * 8313397 * 2
def baseEnd_8313397 : Nat := 4268768532645915529704889

theorem tailTrace_8313397 : CollatzResearch.WordTrace tailWord_8313397 prefixEnd_8313397 4268768532645915529704889 := by
  unfold tailWord_8313397
  simp only [CollatzResearch.WordTrace]
  refine ⟨303214498662989959015450445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202142999108659972676966963 303214498662989959015450445)
  ·
    refine ⟨113705436998621234630793917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303214498662989959015450445 113705436998621234630793917)
    ·
      refine ⟨42639538874482962986547719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113705436998621234630793917 42639538874482962986547719)
      ·
        refine ⟨63959308311724444479821579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42639538874482962986547719 63959308311724444479821579)
        ·
          refine ⟨95938962467586666719732369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63959308311724444479821579 95938962467586666719732369)
          ·
            refine ⟨71954221850690000039799277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95938962467586666719732369 71954221850690000039799277)
            ·
              refine ⟨26982833194008750014924729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71954221850690000039799277 26982833194008750014924729)
              ·
                refine ⟨20237124895506562511193547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26982833194008750014924729 20237124895506562511193547)
                ·
                  refine ⟨30355687343259843766790321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20237124895506562511193547 30355687343259843766790321)
                  ·
                    refine ⟨22766765507444882825092741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30355687343259843766790321 22766765507444882825092741)
                    ·
                      refine ⟨4268768532645915529704889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22766765507444882825092741 4268768532645915529704889)
                      ·
                        rfl

theorem cell23_8313397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_8313397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313397 prefixEnd_8313397 := by exact prefixLift 8313397
  have htrace : WordTrace (prefixWord ++ tailWord_8313397) baseStart_8313397 baseEnd_8313397 := by
    simpa [prefixWord, tailWord_8313397, baseEnd_8313397] using wordTrace_append hprefix tailTrace_8313397
  have hstable : (prefixWord ++ tailWord_8313397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313397).length < 2 ^ (prefixWord ++ tailWord_8313397).sum := by decide
  have hdescent : baseEnd_8313397 < baseStart_8313397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313404 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_8313404 : Nat := 118140960795 + 8313404 * 2 ^ 59
def prefixEnd_8313404 : Nat := 4983230072969 + 3 ^ 40 * 8313404 * 2
def baseEnd_8313404 : Nat := 4268772127010497002317357

theorem tailTrace_8313404 : CollatzResearch.WordTrace tailWord_8313404 prefixEnd_8313404 4268772127010497002317357 := by
  unfold tailWord_8313404
  simp only [CollatzResearch.WordTrace]
  refine ⟨151607376986982299605477633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202143169315976399473970177 151607376986982299605477633)
  ·
    refine ⟨113705532740236724704108225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151607376986982299605477633 113705532740236724704108225)
    ·
      refine ⟨85279149555177543528081169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113705532740236724704108225 85279149555177543528081169)
      ·
        refine ⟨63959362166383157646060877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85279149555177543528081169 63959362166383157646060877)
        ·
          refine ⟨23984760812393684117272829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63959362166383157646060877 23984760812393684117272829)
          ·
            refine ⟨8994285304647631543977311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23984760812393684117272829 8994285304647631543977311)
            ·
              refine ⟨13491427956971447315965967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994285304647631543977311 13491427956971447315965967)
              ·
                refine ⟨20237141935457170973948951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491427956971447315965967 20237141935457170973948951)
                ·
                  refine ⟨30355712903185756460923427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20237141935457170973948951 30355712903185756460923427)
                  ·
                    refine ⟨45533569354778634691385141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30355712903185756460923427 45533569354778634691385141)
                    ·
                      refine ⟨4268772127010497002317357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45533569354778634691385141 4268772127010497002317357)
                      ·
                        rfl

theorem cell23_8313404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_8313404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313404 prefixEnd_8313404 := by exact prefixLift 8313404
  have htrace : WordTrace (prefixWord ++ tailWord_8313404) baseStart_8313404 baseEnd_8313404 := by
    simpa [prefixWord, tailWord_8313404, baseEnd_8313404] using wordTrace_append hprefix tailTrace_8313404
  have hstable : (prefixWord ++ tailWord_8313404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313404).length < 2 ^ (prefixWord ++ tailWord_8313404).sum := by decide
  have hdescent : baseEnd_8313404 < baseStart_8313404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313412 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_8313412 : Nat := 118140960795 + 8313412 * 2 ^ 59
def prefixEnd_8313412 : Nat := 4983230072969 + 3 ^ 40 * 8313412 * 2
def baseEnd_8313412 : Nat := 4268776234855732971017321

theorem tailTrace_8313412 : CollatzResearch.WordTrace tailWord_8313412 prefixEnd_8313412 4268776234855732971017321 := by
  unfold tailWord_8313412
  simp only [CollatzResearch.WordTrace]
  refine ⟨151607522878967808288623245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202143363838623744384830993 151607522878967808288623245)
  ·
    refine ⟨56852821079612928108233717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151607522878967808288623245 56852821079612928108233717)
    ·
      refine ⟨5329951976213712010146911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56852821079612928108233717 5329951976213712010146911)
      ·
        refine ⟨7994927964320568015220367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329951976213712010146911 7994927964320568015220367)
        ·
          refine ⟨11992391946480852022830551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994927964320568015220367 11992391946480852022830551)
          ·
            refine ⟨17988587919721278034245827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11992391946480852022830551 17988587919721278034245827)
            ·
              refine ⟨26982881879581917051368741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17988587919721278034245827 26982881879581917051368741)
              ·
                refine ⟨5059290352421609447131639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26982881879581917051368741 5059290352421609447131639)
                ·
                  refine ⟨7588935528632414170697459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059290352421609447131639 7588935528632414170697459)
                  ·
                    refine ⟨11383403292948621256046189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588935528632414170697459 11383403292948621256046189)
                    ·
                      refine ⟨4268776234855732971017321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11383403292948621256046189 4268776234855732971017321)
                      ·
                        rfl

theorem cell23_8313412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_8313412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313412 prefixEnd_8313412 := by exact prefixLift 8313412
  have htrace : WordTrace (prefixWord ++ tailWord_8313412) baseStart_8313412 baseEnd_8313412 := by
    simpa [prefixWord, tailWord_8313412, baseEnd_8313412] using wordTrace_append hprefix tailTrace_8313412
  have hstable : (prefixWord ++ tailWord_8313412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313412).length < 2 ^ (prefixWord ++ tailWord_8313412).sum := by decide
  have hdescent : baseEnd_8313412 < baseStart_8313412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313418 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_8313418 : Nat := 118140960795 + 8313418 * 2 ^ 59
def prefixEnd_8313418 : Nat := 4983230072969 + 3 ^ 40 * 8313418 * 2
def baseEnd_8313418 : Nat := 4268779315739659947542293

theorem tailTrace_8313418 : CollatzResearch.WordTrace tailWord_8313418 prefixEnd_8313418 4268779315739659947542293 := by
  unfold tailWord_8313418
  simp only [CollatzResearch.WordTrace]
  refine ⟨75803816148978469900491227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202143509730609253067976605 75803816148978469900491227)
  ·
    refine ⟨113705724223467704850736841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75803816148978469900491227 113705724223467704850736841)
    ·
      refine ⟨85279293167600778638052631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113705724223467704850736841 85279293167600778638052631)
      ·
        refine ⟨127918939751401167957078947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85279293167600778638052631 127918939751401167957078947)
        ·
          refine ⟨191878409627101751935618421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127918939751401167957078947 191878409627101751935618421)
          ·
            refine ⟨17988600902540789243964227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191878409627101751935618421 17988600902540789243964227)
            ·
              refine ⟨26982901353811183865946341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17988600902540789243964227 26982901353811183865946341)
              ·
                refine ⟨5059294003839596974864939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26982901353811183865946341 5059294003839596974864939)
                ·
                  refine ⟨7588941005759395462297409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059294003839596974864939 7588941005759395462297409)
                  ·
                    refine ⟨5691705754319546596723057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588941005759395462297409 5691705754319546596723057)
                    ·
                      refine ⟨4268779315739659947542293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691705754319546596723057 4268779315739659947542293)
                      ·
                        rfl

theorem cell23_8313418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_8313418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313418 prefixEnd_8313418 := by exact prefixLift 8313418
  have htrace : WordTrace (prefixWord ++ tailWord_8313418) baseStart_8313418 baseEnd_8313418 := by
    simpa [prefixWord, tailWord_8313418, baseEnd_8313418] using wordTrace_append hprefix tailTrace_8313418
  have hstable : (prefixWord ++ tailWord_8313418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313418).length < 2 ^ (prefixWord ++ tailWord_8313418).sum := by decide
  have hdescent : baseEnd_8313418 < baseStart_8313418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313420 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_8313420 : Nat := 118140960795 + 8313420 * 2 ^ 59
def prefixEnd_8313420 : Nat := 4983230072969 + 3 ^ 40 * 8313420 * 2
def baseEnd_8313420 : Nat := 1422926780900322979905761

theorem tailTrace_8313420 : CollatzResearch.WordTrace tailWord_8313420 prefixEnd_8313420 1422926780900322979905761 := by
  unfold tailWord_8313420
  simp only [CollatzResearch.WordTrace]
  refine ⟨151607668770953316971768857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202143558361271089295691809 151607668770953316971768857)
  ·
    refine ⟨113705751578214987728826643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151607668770953316971768857 113705751578214987728826643)
    ·
      refine ⟨170558627367322481593239965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113705751578214987728826643 170558627367322481593239965)
      ·
        refine ⟨63959485262745930597464987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170558627367322481593239965 63959485262745930597464987)
        ·
          refine ⟨95939227894118895896197481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63959485262745930597464987 95939227894118895896197481)
          ·
            refine ⟨71954420920589171922148111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95939227894118895896197481 71954420920589171922148111)
            ·
              refine ⟨107931631380883757883222167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71954420920589171922148111 107931631380883757883222167)
              ·
                refine ⟨161897447071325636824833251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107931631380883757883222167 161897447071325636824833251)
                ·
                  refine ⟨242846170606988455237249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161897447071325636824833251 242846170606988455237249877)
                  ·
                    refine ⟨1422926780900322979905761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 242846170606988455237249877 1422926780900322979905761)
                    ·
                      rfl

theorem cell23_8313420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_8313420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313420 prefixEnd_8313420 := by exact prefixLift 8313420
  have htrace : WordTrace (prefixWord ++ tailWord_8313420) baseStart_8313420 baseEnd_8313420 := by
    simpa [prefixWord, tailWord_8313420, baseEnd_8313420] using wordTrace_append hprefix tailTrace_8313420
  have hstable : (prefixWord ++ tailWord_8313420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313420).length < 2 ^ (prefixWord ++ tailWord_8313420).sum := by decide
  have hdescent : baseEnd_8313420 < baseStart_8313420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313444 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_8313444 : Nat := 118140960795 + 8313444 * 2 ^ 59
def prefixEnd_8313444 : Nat := 4983230072969 + 3 ^ 40 * 8313444 * 2
def baseEnd_8313444 : Nat := 4268792666236676845817173

theorem tailTrace_8313444 : CollatzResearch.WordTrace tailWord_8313444 prefixEnd_8313444 4268792666236676845817173 := by
  unfold tailWord_8313444
  simp only [CollatzResearch.WordTrace]
  refine ⟨151608106446909843021205693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202144141929213124028274257 151608106446909843021205693)
  ·
    refine ⟨56853039917591191132952135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151608106446909843021205693 56853039917591191132952135)
    ·
      refine ⟨85279559876386786699428203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56853039917591191132952135 85279559876386786699428203)
      ·
        refine ⟨127919339814580180049142305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85279559876386786699428203 127919339814580180049142305)
        ·
          refine ⟨95939504860935135036856729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127919339814580180049142305 95939504860935135036856729)
          ·
            refine ⟨71954628645701351277642547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95939504860935135036856729 71954628645701351277642547)
            ·
              refine ⟨107931942968552026916463821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71954628645701351277642547 107931942968552026916463821)
              ·
                refine ⟨40474478613207010093673933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107931942968552026916463821 40474478613207010093673933)
                ·
                  refine ⟨15177929479952628785127725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40474478613207010093673933 15177929479952628785127725)
                  ·
                    refine ⟨5691723554982235794422897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15177929479952628785127725 5691723554982235794422897)
                    ·
                      refine ⟨4268792666236676845817173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691723554982235794422897 4268792666236676845817173)
                      ·
                        rfl

theorem cell23_8313444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_8313444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313444 prefixEnd_8313444 := by exact prefixLift 8313444
  have htrace : WordTrace (prefixWord ++ tailWord_8313444) baseStart_8313444 baseEnd_8313444 := by
    simpa [prefixWord, tailWord_8313444, baseEnd_8313444] using wordTrace_append hprefix tailTrace_8313444
  have hstable : (prefixWord ++ tailWord_8313444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313444).length < 2 ^ (prefixWord ++ tailWord_8313444).sum := by decide
  have hdescent : baseEnd_8313444 < baseStart_8313444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313507 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 3]
def baseStart_8313507 : Nat := 118140960795 + 8313507 * 2 ^ 59
def prefixEnd_8313507 : Nat := 4983230072969 + 3 ^ 40 * 8313507 * 2
def baseEnd_8313507 : Nat := 4268825015517910099329383

theorem tailTrace_8313507 : CollatzResearch.WordTrace tailWord_8313507 prefixEnd_8313507 4268825015517910099329383 := by
  unfold tailWord_8313507
  simp only [CollatzResearch.WordTrace]
  refine ⟨303218510692591447801954775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202145673795060965201303183 303218510692591447801954775)
  ·
    refine ⟨454827766038887171702932163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303218510692591447801954775 454827766038887171702932163)
    ·
      refine ⟨682241649058330757554398245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454827766038887171702932163 682241649058330757554398245)
      ·
        refine ⟨127920309198437017041449671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682241649058330757554398245 127920309198437017041449671)
        ·
          refine ⟨191880463797655525562174507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127920309198437017041449671 191880463797655525562174507)
          ·
            refine ⟨287820695696483288343261761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191880463797655525562174507 287820695696483288343261761)
            ·
              refine ⟨215865521772362466257446321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287820695696483288343261761 215865521772362466257446321)
              ·
                refine ⟨161899141329271849693084741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215865521772362466257446321 161899141329271849693084741)
                ·
                  refine ⟨30356088999238471817453389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161899141329271849693084741 30356088999238471817453389)
                  ·
                    refine ⟨11383533374714426931545021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30356088999238471817453389 11383533374714426931545021)
                    ·
                      refine ⟨4268825015517910099329383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11383533374714426931545021 4268825015517910099329383)
                      ·
                        rfl

theorem cell23_8313507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_8313507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313507 prefixEnd_8313507 := by exact prefixLift 8313507
  have htrace : WordTrace (prefixWord ++ tailWord_8313507) baseStart_8313507 baseEnd_8313507 := by
    simpa [prefixWord, tailWord_8313507, baseEnd_8313507] using wordTrace_append hprefix tailTrace_8313507
  have hstable : (prefixWord ++ tailWord_8313507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313507).length < 2 ^ (prefixWord ++ tailWord_8313507).sum := by decide
  have hdescent : baseEnd_8313507 < baseStart_8313507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313511 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_8313511 : Nat := 118140960795 + 8313511 * 2 ^ 59
def prefixEnd_8313511 : Nat := 4983230072969 + 3 ^ 40 * 8313511 * 2
def baseEnd_8313511 : Nat := 4268827069440528083679365

theorem tailTrace_8313511 : CollatzResearch.WordTrace tailWord_8313511 prefixEnd_8313511 4268827069440528083679365 := by
  unfold tailWord_8313511
  simp only [CollatzResearch.WordTrace]
  refine ⟨303218656584576956485100387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202145771056384637656733591 303218656584576956485100387)
  ·
    refine ⟨454827984876865434727650581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303218656584576956485100387 454827984876865434727650581)
    ·
      refine ⟨21320061791103067252858621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 454827984876865434727650581 21320061791103067252858621)
      ·
        refine ⟨7995023171663650219821983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21320061791103067252858621 7995023171663650219821983)
        ·
          refine ⟨11992534757495475329732975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7995023171663650219821983 11992534757495475329732975)
          ·
            refine ⟨17988802136243212994599463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11992534757495475329732975 17988802136243212994599463)
            ·
              refine ⟨26983203204364819491899195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17988802136243212994599463 26983203204364819491899195)
              ·
                refine ⟨40474804806547229237848793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26983203204364819491899195 40474804806547229237848793)
                ·
                  refine ⟨30356103604910421928386595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40474804806547229237848793 30356103604910421928386595)
                  ·
                    refine ⟨45534155407365632892579893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30356103604910421928386595 45534155407365632892579893)
                    ·
                      refine ⟨4268827069440528083679365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45534155407365632892579893 4268827069440528083679365)
                      ·
                        rfl

theorem cell23_8313511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_8313511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313511 prefixEnd_8313511 := by exact prefixLift 8313511
  have htrace : WordTrace (prefixWord ++ tailWord_8313511) baseStart_8313511 baseEnd_8313511 := by
    simpa [prefixWord, tailWord_8313511, baseEnd_8313511] using wordTrace_append hprefix tailTrace_8313511
  have hstable : (prefixWord ++ tailWord_8313511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313511).length < 2 ^ (prefixWord ++ tailWord_8313511).sum := by decide
  have hdescent : baseEnd_8313511 < baseStart_8313511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313581 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_8313581 : Nat := 118140960795 + 8313581 * 2 ^ 59
def prefixEnd_8313581 : Nat := 4983230072969 + 3 ^ 40 * 8313581 * 2
def baseEnd_8313581 : Nat := 4268863013086342809804043

theorem tailTrace_8313581 : CollatzResearch.WordTrace tailWord_8313581 prefixEnd_8313581 4268863013086342809804043 := by
  unfold tailWord_8313581
  simp only [CollatzResearch.WordTrace]
  refine ⟨303221209694323358440148597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202147473129548905626765731 303221209694323358440148597)
  ·
    refine ⟨28426988408842814853763931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303221209694323358440148597 28426988408842814853763931)
    ·
      refine ⟨42640482613264222280645897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28426988408842814853763931 42640482613264222280645897)
      ·
        refine ⟨31980361959948166710484423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42640482613264222280645897 31980361959948166710484423)
        ·
          refine ⟨47970542939922250065726635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31980361959948166710484423 47970542939922250065726635)
          ·
            refine ⟨71955814409883375098589953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47970542939922250065726635 71955814409883375098589953)
            ·
              refine ⟨53966860807412531323942465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71955814409883375098589953 53966860807412531323942465)
              ·
                refine ⟨40475145605559398492956849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53966860807412531323942465 40475145605559398492956849)
                ·
                  refine ⟨30356359204169548869717637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40475145605559398492956849 30356359204169548869717637)
                  ·
                    refine ⟨5691817350781790413072057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30356359204169548869717637 5691817350781790413072057)
                    ·
                      refine ⟨4268863013086342809804043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691817350781790413072057 4268863013086342809804043)
                      ·
                        rfl

theorem cell23_8313581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_8313581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313581 prefixEnd_8313581 := by exact prefixLift 8313581
  have htrace : WordTrace (prefixWord ++ tailWord_8313581) baseStart_8313581 baseEnd_8313581 := by
    simpa [prefixWord, tailWord_8313581, baseEnd_8313581] using wordTrace_append hprefix tailTrace_8313581
  have hstable : (prefixWord ++ tailWord_8313581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313581).length < 2 ^ (prefixWord ++ tailWord_8313581).sum := by decide
  have hdescent : baseEnd_8313581 < baseStart_8313581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313584 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_8313584 : Nat := 118140960795 + 8313584 * 2 ^ 59
def prefixEnd_8313584 : Nat := 4983230072969 + 3 ^ 40 * 8313584 * 2
def baseEnd_8313584 : Nat := 4268864553528306298066529

theorem tailTrace_8313584 : CollatzResearch.WordTrace tailWord_8313584 prefixEnd_8313584 4268864553528306298066529 := by
  unfold tailWord_8313584
  simp only [CollatzResearch.WordTrace]
  refine ⟨151610659556656244976253903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202147546075541659968338537 151610659556656244976253903)
  ·
    refine ⟨227415989334984367464380855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151610659556656244976253903 227415989334984367464380855)
    ·
      refine ⟨341123984002476551196571283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227415989334984367464380855 341123984002476551196571283)
      ·
        refine ⟨511685976003714826794856925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341123984002476551196571283 511685976003714826794856925)
        ·
          refine ⟨191882241001393060048071347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511685976003714826794856925 191882241001393060048071347)
          ·
            refine ⟨287823361502089590072107021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191882241001393060048071347 287823361502089590072107021)
            ·
              refine ⟨107933760563283596277040133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287823361502089590072107021 107933760563283596277040133)
              ·
                refine ⟨20237580105615674301945025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107933760563283596277040133 20237580105615674301945025)
                ·
                  refine ⟨15178185079211755726458769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20237580105615674301945025 15178185079211755726458769)
                  ·
                    refine ⟨11383638809408816794844077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15178185079211755726458769 11383638809408816794844077)
                    ·
                      refine ⟨4268864553528306298066529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11383638809408816794844077 4268864553528306298066529)
                      ·
                        rfl

theorem cell23_8313584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_8313584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313584 prefixEnd_8313584 := by exact prefixLift 8313584
  have htrace : WordTrace (prefixWord ++ tailWord_8313584) baseStart_8313584 baseEnd_8313584 := by
    simpa [prefixWord, tailWord_8313584, baseEnd_8313584] using wordTrace_append hprefix tailTrace_8313584
  have hstable : (prefixWord ++ tailWord_8313584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313584).length < 2 ^ (prefixWord ++ tailWord_8313584).sum := by decide
  have hdescent : baseEnd_8313584 < baseStart_8313584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313598 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_8313598 : Nat := 118140960795 + 8313598 * 2 ^ 59
def prefixEnd_8313598 : Nat := 4983230072969 + 3 ^ 40 * 8313598 * 2
def baseEnd_8313598 : Nat := 4268871742257469243291465

theorem tailTrace_8313598 : CollatzResearch.WordTrace tailWord_8313598 prefixEnd_8313598 4268871742257469243291465 := by
  unfold tailWord_8313598
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902728716907721292939681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202147886490174513562344965 37902728716907721292939681)
  ·
    refine ⟨28427046537680790969704761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37902728716907721292939681 28427046537680790969704761)
    ·
      refine ⟨21320284903260593227278571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28427046537680790969704761 21320284903260593227278571)
      ·
        refine ⟨31980427354890889840917857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21320284903260593227278571 31980427354890889840917857)
        ·
          refine ⟨23985320516168167380688393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31980427354890889840917857 23985320516168167380688393)
          ·
            refine ⟨17988990387126125535516295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23985320516168167380688393 17988990387126125535516295)
            ·
              refine ⟨26983485580689188303274443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17988990387126125535516295 26983485580689188303274443)
              ·
                refine ⟨40475228371033782454911665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26983485580689188303274443 40475228371033782454911665)
                ·
                  refine ⟨30356421278275336841183749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40475228371033782454911665 30356421278275336841183749)
                  ·
                    refine ⟨5691828989676625657721953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30356421278275336841183749 5691828989676625657721953)
                    ·
                      refine ⟨4268871742257469243291465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691828989676625657721953 4268871742257469243291465)
                      ·
                        rfl

theorem cell23_8313598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_8313598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313598 prefixEnd_8313598 := by exact prefixLift 8313598
  have htrace : WordTrace (prefixWord ++ tailWord_8313598) baseStart_8313598 baseEnd_8313598 := by
    simpa [prefixWord, tailWord_8313598, baseEnd_8313598] using wordTrace_append hprefix tailTrace_8313598
  have hstable : (prefixWord ++ tailWord_8313598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313598).length < 2 ^ (prefixWord ++ tailWord_8313598).sum := by decide
  have hdescent : baseEnd_8313598 < baseStart_8313598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313604 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 6]
def baseStart_8313604 : Nat := 118140960795 + 8313604 * 2 ^ 59
def prefixEnd_8313604 : Nat := 4983230072969 + 3 ^ 40 * 8313604 * 2
def baseEnd_8313604 : Nat := 474319424793488468868493

theorem tailTrace_8313604 : CollatzResearch.WordTrace tailWord_8313604 prefixEnd_8313604 474319424793488468868493 := by
  unfold tailWord_8313604
  simp only [CollatzResearch.WordTrace]
  refine ⟨151611024286620016684117933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202148032382160022245490577 151611024286620016684117933)
  ·
    refine ⟨56854134107482506256544225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151611024286620016684117933 56854134107482506256544225)
    ·
      refine ⟨42640600580611879692408169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56854134107482506256544225 42640600580611879692408169)
      ·
        refine ⟨31980450435458909769306127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42640600580611879692408169 31980450435458909769306127)
        ·
          refine ⟨47970675653188364653959191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31980450435458909769306127 47970675653188364653959191)
          ·
            refine ⟨71956013479782546980938787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47970675653188364653959191 71956013479782546980938787)
            ·
              refine ⟨107934020219673820471408181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71956013479782546980938787 107934020219673820471408181)
              ·
                refine ⟨10118814395594420669194517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107934020219673820471408181 10118814395594420669194517)
                ·
                  refine ⟨474319424793488468868493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10118814395594420669194517 474319424793488468868493)
                  ·
                    rfl

theorem cell23_8313604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_8313604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313604 prefixEnd_8313604 := by exact prefixLift 8313604
  have htrace : WordTrace (prefixWord ++ tailWord_8313604) baseStart_8313604 baseEnd_8313604 := by
    simpa [prefixWord, tailWord_8313604, baseEnd_8313604] using wordTrace_append hprefix tailTrace_8313604
  have hstable : (prefixWord ++ tailWord_8313604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313604).length < 2 ^ (prefixWord ++ tailWord_8313604).sum := by decide
  have hdescent : baseEnd_8313604 < baseStart_8313604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313618 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_8313618 : Nat := 118140960795 + 8313618 * 2 ^ 59
def prefixEnd_8313618 : Nat := 4983230072969 + 3 ^ 40 * 8313618 * 2
def baseEnd_8313618 : Nat := 4268882011870559165041373

theorem tailTrace_8313618 : CollatzResearch.WordTrace tailWord_8313618 prefixEnd_8313618 4268882011870559165041373 := by
  unfold tailWord_8313618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75805639798797328439811377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202148372796792875839497005 75805639798797328439811377)
  ·
    refine ⟨56854229849097996329858533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75805639798797328439811377 56854229849097996329858533)
    ·
      refine ⟨10660168096705874311848475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56854229849097996329858533 10660168096705874311848475)
      ·
        refine ⟨15990252145058811467772713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10660168096705874311848475 15990252145058811467772713)
        ·
          refine ⟨11992689108794108600829535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15990252145058811467772713 11992689108794108600829535)
          ·
            refine ⟨17989033663191162901244303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11992689108794108600829535 17989033663191162901244303)
            ·
              refine ⟨26983550494786744351866455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989033663191162901244303 26983550494786744351866455)
              ·
                refine ⟨40475325742180116527799683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26983550494786744351866455 40475325742180116527799683)
                ·
                  refine ⟨60712988613270174791699525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40475325742180116527799683 60712988613270174791699525)
                  ·
                    refine ⟨11383685364988157773443661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60712988613270174791699525 11383685364988157773443661)
                    ·
                      refine ⟨4268882011870559165041373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11383685364988157773443661 4268882011870559165041373)
                      ·
                        rfl

theorem cell23_8313618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_8313618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313618 prefixEnd_8313618 := by exact prefixLift 8313618
  have htrace : WordTrace (prefixWord ++ tailWord_8313618) baseStart_8313618 baseEnd_8313618 := by
    simpa [prefixWord, tailWord_8313618, baseEnd_8313618] using wordTrace_append hprefix tailTrace_8313618
  have hstable : (prefixWord ++ tailWord_8313618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313618).length < 2 ^ (prefixWord ++ tailWord_8313618).sum := by decide
  have hdescent : baseEnd_8313618 < baseStart_8313618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313738 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_8313738 : Nat := 118140960795 + 8313738 * 2 ^ 59
def prefixEnd_8313738 : Nat := 4983230072969 + 3 ^ 40 * 8313738 * 2
def baseEnd_8313738 : Nat := 4268943629549098695540821

theorem tailTrace_8313738 : CollatzResearch.WordTrace tailWord_8313738 prefixEnd_8313738 4268943629549098695540821 := by
  unfold tailWord_8313738
  simp only [CollatzResearch.WordTrace]
  refine ⟨75806733988688643563403467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202151290636503049502409245 75806733988688643563403467)
  ·
    refine ⟨113710100983032965345105201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75806733988688643563403467 113710100983032965345105201)
    ·
      refine ⟨85282575737274724008828901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113710100983032965345105201 85282575737274724008828901)
      ·
        refine ⟨15990482950739010751655419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85282575737274724008828901 15990482950739010751655419)
        ·
          refine ⟨23985724426108516127483129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15990482950739010751655419 23985724426108516127483129)
          ·
            refine ⟨17989293319581387095612347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23985724426108516127483129 17989293319581387095612347)
            ·
              refine ⟨26983939979372080643418521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989293319581387095612347 26983939979372080643418521)
              ·
                refine ⟨20237954984529060482563891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26983939979372080643418521 20237954984529060482563891)
                ·
                  refine ⟨30356932476793590723845837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20237954984529060482563891 30356932476793590723845837)
                  ·
                    refine ⟨11383849678797596521442189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30356932476793590723845837 11383849678797596521442189)
                    ·
                      refine ⟨4268943629549098695540821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11383849678797596521442189 4268943629549098695540821)
                      ·
                        rfl

theorem cell23_8313738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_8313738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313738 prefixEnd_8313738 := by exact prefixLift 8313738
  have htrace : WordTrace (prefixWord ++ tailWord_8313738) baseStart_8313738 baseEnd_8313738 := by
    simpa [prefixWord, tailWord_8313738, baseEnd_8313738] using wordTrace_append hprefix tailTrace_8313738
  have hstable : (prefixWord ++ tailWord_8313738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313738).length < 2 ^ (prefixWord ++ tailWord_8313738).sum := by decide
  have hdescent : baseEnd_8313738 < baseStart_8313738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313756 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_8313756 : Nat := 118140960795 + 8313756 * 2 ^ 59
def prefixEnd_8313756 : Nat := 4983230072969 + 3 ^ 40 * 8313756 * 2
def baseEnd_8313756 : Nat := 4268952872200879625115739

theorem tailTrace_8313756 : CollatzResearch.WordTrace tailWord_8313756 prefixEnd_8313756 4268952872200879625115739 := by
  unfold tailWord_8313756
  simp only [CollatzResearch.WordTrace]
  refine ⟨151613796234344681663884561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202151728312459575551846081 151613796234344681663884561)
  ·
    refine ⟨113710347175758511247913421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151613796234344681663884561 113710347175758511247913421)
    ·
      refine ⟨42641380190909441717967533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113710347175758511247913421 42641380190909441717967533)
      ·
        refine ⟨15990517571591040644237825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42641380190909441717967533 15990517571591040644237825)
        ·
          refine ⟨11992888178693280483178369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15990517571591040644237825 11992888178693280483178369)
          ·
            refine ⟨8994666134019960362383777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11992888178693280483178369 8994666134019960362383777)
            ·
              refine ⟨6745999600514970271787833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8994666134019960362383777 6745999600514970271787833)
              ·
                refine ⟨5059499700386227703840875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745999600514970271787833 5059499700386227703840875)
                ·
                  refine ⟨7589249550579341555761313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059499700386227703840875 7589249550579341555761313)
                  ·
                    refine ⟨5691937162934506166820985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589249550579341555761313 5691937162934506166820985)
                    ·
                      refine ⟨4268952872200879625115739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691937162934506166820985 4268952872200879625115739)
                      ·
                        rfl

theorem cell23_8313756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_8313756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313756 prefixEnd_8313756 := by exact prefixLift 8313756
  have htrace : WordTrace (prefixWord ++ tailWord_8313756) baseStart_8313756 baseEnd_8313756 := by
    simpa [prefixWord, tailWord_8313756, baseEnd_8313756] using wordTrace_append hprefix tailTrace_8313756
  have hstable : (prefixWord ++ tailWord_8313756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313756).length < 2 ^ (prefixWord ++ tailWord_8313756).sum := by decide
  have hdescent : baseEnd_8313756 < baseStart_8313756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313761 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_8313761 : Nat := 118140960795 + 8313761 * 2 ^ 59
def prefixEnd_8313761 : Nat := 4983230072969 + 3 ^ 40 * 8313761 * 2
def baseEnd_8313761 : Nat := 4268955439604152105553215

theorem tailTrace_8313761 : CollatzResearch.WordTrace tailWord_8313761 prefixEnd_8313761 4268955439604152105553215 := by
  unfold tailWord_8313761
  simp only [CollatzResearch.WordTrace]
  refine ⟨303227774833671249181701137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202151849889114166121134091 303227774833671249181701137)
  ·
    refine ⟨227420831125253436886275853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303227774833671249181701137 227420831125253436886275853)
    ·
      refine ⟨85282811671970038832353445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227420831125253436886275853 85282811671970038832353445)
      ·
        refine ⟨15990527188494382281066271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85282811671970038832353445 15990527188494382281066271)
        ·
          refine ⟨23985790782741573421599407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15990527188494382281066271 23985790782741573421599407)
          ·
            refine ⟨35978686174112360132399111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23985790782741573421599407 35978686174112360132399111)
            ·
              refine ⟨53968029261168540198598667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35978686174112360132399111 53968029261168540198598667)
              ·
                refine ⟨80952043891752810297898001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53968029261168540198598667 80952043891752810297898001)
                ·
                  refine ⟨60714032918814607723423501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80952043891752810297898001 60714032918814607723423501)
                  ·
                    refine ⟨22767762344555477896283813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60714032918814607723423501 22767762344555477896283813)
                    ·
                      refine ⟨4268955439604152105553215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22767762344555477896283813 4268955439604152105553215)
                      ·
                        rfl

theorem cell23_8313761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_8313761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313761 prefixEnd_8313761 := by exact prefixLift 8313761
  have htrace : WordTrace (prefixWord ++ tailWord_8313761) baseStart_8313761 baseEnd_8313761 := by
    simpa [prefixWord, tailWord_8313761, baseEnd_8313761] using wordTrace_append hprefix tailTrace_8313761
  have hstable : (prefixWord ++ tailWord_8313761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313761).length < 2 ^ (prefixWord ++ tailWord_8313761).sum := by decide
  have hdescent : baseEnd_8313761 < baseStart_8313761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313778 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_8313778 : Nat := 118140960795 + 8313778 * 2 ^ 59
def prefixEnd_8313778 : Nat := 4983230072969 + 3 ^ 40 * 8313778 * 2
def baseEnd_8313778 : Nat := 4268964168775278539040637

theorem tailTrace_8313778 : CollatzResearch.WordTrace tailWord_8313778 prefixEnd_8313778 4268964168775278539040637 := by
  unfold tailWord_8313778
  simp only [CollatzResearch.WordTrace]
  refine ⟨75807098718652415271267497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202152263249739774056713325 75807098718652415271267497)
  ·
    refine ⟨56855324038989311453450623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75807098718652415271267497 56855324038989311453450623)
    ·
      refine ⟨85282986058483967180175935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56855324038989311453450623 85282986058483967180175935)
      ·
        refine ⟨127924479087725950770263903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85282986058483967180175935 127924479087725950770263903)
        ·
          refine ⟨191886718631588926155395855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127924479087725950770263903 191886718631588926155395855)
          ·
            refine ⟨287830077947383389233093783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191886718631588926155395855 287830077947383389233093783)
            ·
              refine ⟨431745116921075083849640675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287830077947383389233093783 431745116921075083849640675)
              ·
                refine ⟨647617675381612625774461013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431745116921075083849640675 647617675381612625774461013)
                ·
                  refine ⟨7589269633378272958294465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 647617675381612625774461013 7589269633378272958294465)
                  ·
                    refine ⟨5691952225033704718720849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589269633378272958294465 5691952225033704718720849)
                    ·
                      refine ⟨4268964168775278539040637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691952225033704718720849 4268964168775278539040637)
                      ·
                        rfl

theorem cell23_8313778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_8313778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313778 prefixEnd_8313778 := by exact prefixLift 8313778
  have htrace : WordTrace (prefixWord ++ tailWord_8313778) baseStart_8313778 baseEnd_8313778 := by
    simpa [prefixWord, tailWord_8313778, baseEnd_8313778] using wordTrace_append hprefix tailTrace_8313778
  have hstable : (prefixWord ++ tailWord_8313778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313778).length < 2 ^ (prefixWord ++ tailWord_8313778).sum := by decide
  have hdescent : baseEnd_8313778 < baseStart_8313778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313781 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_8313781 : Nat := 118140960795 + 8313781 * 2 ^ 59
def prefixEnd_8313781 : Nat := 4983230072969 + 3 ^ 40 * 8313781 * 2
def baseEnd_8313781 : Nat := 4268965709217242027303123

theorem tailTrace_8313781 : CollatzResearch.WordTrace tailWord_8313781 prefixEnd_8313781 4268965709217242027303123 := by
  unfold tailWord_8313781
  simp only [CollatzResearch.WordTrace]
  refine ⟨303228504293598792597429197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202152336195732528398286131 303228504293598792597429197)
  ·
    refine ⟨113710689110099547224035949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303228504293598792597429197 113710689110099547224035949)
    ·
      refine ⟨42641508416287330209013481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113710689110099547224035949 42641508416287330209013481)
      ·
        refine ⟨31981131312215497656760111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42641508416287330209013481 31981131312215497656760111)
        ·
          refine ⟨47971696968323246485140167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31981131312215497656760111 47971696968323246485140167)
          ·
            refine ⟨71957545452484869727710251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47971696968323246485140167 71957545452484869727710251)
            ·
              refine ⟨107936318178727304591565377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71957545452484869727710251 107936318178727304591565377)
              ·
                refine ⟨80952238634045478443674033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107936318178727304591565377 80952238634045478443674033)
                ·
                  refine ⟨60714178975534108832755525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80952238634045478443674033 60714178975534108832755525)
                  ·
                    refine ⟨11383908557912645406141661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60714178975534108832755525 11383908557912645406141661)
                    ·
                      refine ⟨4268965709217242027303123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11383908557912645406141661 4268965709217242027303123)
                      ·
                        rfl

theorem cell23_8313781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_8313781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313781 prefixEnd_8313781 := by exact prefixLift 8313781
  have htrace : WordTrace (prefixWord ++ tailWord_8313781) baseStart_8313781 baseEnd_8313781 := by
    simpa [prefixWord, tailWord_8313781, baseEnd_8313781] using wordTrace_append hprefix tailTrace_8313781
  have hstable : (prefixWord ++ tailWord_8313781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313781).length < 2 ^ (prefixWord ++ tailWord_8313781).sum := by decide
  have hdescent : baseEnd_8313781 < baseStart_8313781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313784 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 9]
def baseStart_8313784 : Nat := 118140960795 + 8313784 * 2 ^ 59
def prefixEnd_8313784 : Nat := 4983230072969 + 3 ^ 40 * 8313784 * 2
def baseEnd_8313784 : Nat := 474329694406578390618401

theorem tailTrace_8313784 : CollatzResearch.WordTrace tailWord_8313784 prefixEnd_8313784 474329694406578390618401 := by
  unfold tailWord_8313784
  simp only [CollatzResearch.WordTrace]
  refine ⟨151614306856293962054894203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202152409141725282739858937 151614306856293962054894203)
  ·
    refine ⟨227421460284440943082341305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151614306856293962054894203 227421460284440943082341305)
    ·
      refine ⟨170566095213330707311755979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227421460284440943082341305 170566095213330707311755979)
      ·
        refine ⟨255849142819996060967633969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170566095213330707311755979 255849142819996060967633969)
        ·
          refine ⟨191886857114997045725725477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255849142819996060967633969 191886857114997045725725477)
          ·
            refine ⟨35978785709061946073573527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191886857114997045725725477 35978785709061946073573527)
            ·
              refine ⟨53968178563592919110360291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35978785709061946073573527 53968178563592919110360291)
              ·
                refine ⟨80952267845389378665540437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53968178563592919110360291 80952267845389378665540437)
                ·
                  refine ⟨474329694406578390618401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80952267845389378665540437 474329694406578390618401)
                  ·
                    rfl

theorem cell23_8313784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_8313784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313784 prefixEnd_8313784 := by exact prefixLift 8313784
  have htrace : WordTrace (prefixWord ++ tailWord_8313784) baseStart_8313784 baseEnd_8313784 := by
    simpa [prefixWord, tailWord_8313784, baseEnd_8313784] using wordTrace_append hprefix tailTrace_8313784
  have hstable : (prefixWord ++ tailWord_8313784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313784).length < 2 ^ (prefixWord ++ tailWord_8313784).sum := by decide
  have hdescent : baseEnd_8313784 < baseStart_8313784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313812 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_8313812 : Nat := 118140960795 + 8313812 * 2 ^ 59
def prefixEnd_8313812 : Nat := 4983230072969 + 3 ^ 40 * 8313812 * 2
def baseEnd_8313812 : Nat := 4268981627117531406015481

theorem tailTrace_8313812 : CollatzResearch.WordTrace tailWord_8313812 prefixEnd_8313812 4268981627117531406015481 := by
  unfold tailWord_8313812
  simp only [CollatzResearch.WordTrace]
  refine ⟨151614817478243242445903845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202153089970990989927871793 151614817478243242445903845)
  ·
    refine ⟨28427778277170607958606971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151614817478243242445903845 28427778277170607958606971)
    ·
      refine ⟨42641667415755911937910457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28427778277170607958606971 42641667415755911937910457)
      ·
        refine ⟨31981250561816933953432843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42641667415755911937910457 31981250561816933953432843)
        ·
          refine ⟨47971875842725400930149265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31981250561816933953432843 47971875842725400930149265)
          ·
            refine ⟨35978906882044050697611949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47971875842725400930149265 35978906882044050697611949)
            ·
              refine ⟨13492090080766519011604481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35978906882044050697611949 13492090080766519011604481)
              ·
                refine ⟨10119067560574889258703361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492090080766519011604481 10119067560574889258703361)
                ·
                  refine ⟨7589300670431166944027521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10119067560574889258703361 7589300670431166944027521)
                  ·
                    refine ⟨5691975502823375208020641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589300670431166944027521 5691975502823375208020641)
                    ·
                      refine ⟨4268981627117531406015481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691975502823375208020641 4268981627117531406015481)
                      ·
                        rfl

theorem cell23_8313812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_8313812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313812 prefixEnd_8313812 := by exact prefixLift 8313812
  have htrace : WordTrace (prefixWord ++ tailWord_8313812) baseStart_8313812 baseEnd_8313812 := by
    simpa [prefixWord, tailWord_8313812, baseEnd_8313812] using wordTrace_append hprefix tailTrace_8313812
  have hstable : (prefixWord ++ tailWord_8313812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313812).length < 2 ^ (prefixWord ++ tailWord_8313812).sum := by decide
  have hdescent : baseEnd_8313812 < baseStart_8313812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313818 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_8313818 : Nat := 118140960795 + 8313818 * 2 ^ 59
def prefixEnd_8313818 : Nat := 4983230072969 + 3 ^ 40 * 8313818 * 2
def baseEnd_8313818 : Nat := 474331634222384264726717

theorem tailTrace_8313818 : CollatzResearch.WordTrace tailWord_8313818 prefixEnd_8313818 474331634222384264726717 := by
  unfold tailWord_8313818
  simp only [CollatzResearch.WordTrace]
  refine ⟨75807463448616186979131527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202153235862976498611017405 75807463448616186979131527)
  ·
    refine ⟨113711195172924280468697291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75807463448616186979131527 113711195172924280468697291)
    ·
      refine ⟨170566792759386420703045937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113711195172924280468697291 170566792759386420703045937)
      ·
        refine ⟨127925094569539815527284453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170566792759386420703045937 127925094569539815527284453)
        ·
          refine ⟨23985955231788715411365835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127925094569539815527284453 23985955231788715411365835)
          ·
            refine ⟨35978932847683073117048753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23985955231788715411365835 35978932847683073117048753)
            ·
              refine ⟨26984199635762304837786565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35978932847683073117048753 26984199635762304837786565)
              ·
                refine ⟨5059537431705432157084981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26984199635762304837786565 5059537431705432157084981)
                ·
                  refine ⟨474331634222384264726717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5059537431705432157084981 474331634222384264726717)
                  ·
                    rfl

theorem cell23_8313818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_8313818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313818 prefixEnd_8313818 := by exact prefixLift 8313818
  have htrace : WordTrace (prefixWord ++ tailWord_8313818) baseStart_8313818 baseEnd_8313818 := by
    simpa [prefixWord, tailWord_8313818, baseEnd_8313818] using wordTrace_append hprefix tailTrace_8313818
  have hstable : (prefixWord ++ tailWord_8313818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313818).length < 2 ^ (prefixWord ++ tailWord_8313818).sum := by decide
  have hdescent : baseEnd_8313818 < baseStart_8313818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313829 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 1, 4, 2]
def baseStart_8313829 : Nat := 118140960795 + 8313829 * 2 ^ 59
def prefixEnd_8313829 : Nat := 4983230072969 + 3 ^ 40 * 8313829 * 2
def baseEnd_8313829 : Nat := 4268990356288657839502903

theorem tailTrace_8313829 : CollatzResearch.WordTrace tailWord_8313829 prefixEnd_8313829 4268990356288657839502903 := by
  unfold tailWord_8313829
  simp only [CollatzResearch.WordTrace]
  refine ⟨303230254997424896795176541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202153503331616597863451027 303230254997424896795176541)
  ·
    refine ⟨113711345624034336298191203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303230254997424896795176541 113711345624034336298191203)
    ·
      refine ⟨170567018436051504447286805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113711345624034336298191203 170567018436051504447286805)
      ·
        refine ⟨7995328989189914270966569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170567018436051504447286805 7995328989189914270966569)
        ·
          refine ⟨5996496741892435703224927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7995328989189914270966569 5996496741892435703224927)
          ·
            refine ⟨8994745112838653554837391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996496741892435703224927 8994745112838653554837391)
            ·
              refine ⟨13492117669257980332256087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994745112838653554837391 13492117669257980332256087)
              ·
                refine ⟨20238176503886970498384131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13492117669257980332256087 20238176503886970498384131)
                ·
                  refine ⟨30357264755830455747576197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20238176503886970498384131 30357264755830455747576197)
                  ·
                    refine ⟨5691987141718210452670537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30357264755830455747576197 5691987141718210452670537)
                    ·
                      refine ⟨4268990356288657839502903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5691987141718210452670537 4268990356288657839502903)
                      ·
                        rfl

theorem cell23_8313829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_8313829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313829 prefixEnd_8313829 := by exact prefixLift 8313829
  have htrace : WordTrace (prefixWord ++ tailWord_8313829) baseStart_8313829 baseEnd_8313829 := by
    simpa [prefixWord, tailWord_8313829, baseEnd_8313829] using wordTrace_append hprefix tailTrace_8313829
  have hstable : (prefixWord ++ tailWord_8313829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313829).length < 2 ^ (prefixWord ++ tailWord_8313829).sum := by decide
  have hdescent : baseEnd_8313829 < baseStart_8313829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313831 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 1, 7]
def baseStart_8313831 : Nat := 118140960795 + 8313831 * 2 ^ 59
def prefixEnd_8313831 : Nat := 4983230072969 + 3 ^ 40 * 8313831 * 2
def baseEnd_8313831 : Nat := 1422997127749988943892631

theorem tailTrace_8313831 : CollatzResearch.WordTrace tailWord_8313831 prefixEnd_8313831 1422997127749988943892631 := by
  unfold tailWord_8313831
  simp only [CollatzResearch.WordTrace]
  refine ⟨303230327943417651136749347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202153551962278434091166231 303230327943417651136749347)
  ·
    refine ⟨454845491915126476705124021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303230327943417651136749347 454845491915126476705124021)
    ·
      refine ⟨42641764867043107191105377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454845491915126476705124021 42641764867043107191105377)
      ·
        refine ⟨31981323650282330393329033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42641764867043107191105377 31981323650282330393329033)
        ·
          refine ⟨23985992737711747794996775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31981323650282330393329033 23985992737711747794996775)
          ·
            refine ⟨35978989106567621692495163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23985992737711747794996775 35978989106567621692495163)
            ·
              refine ⟨53968483659851432538742745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35978989106567621692495163 53968483659851432538742745)
              ·
                refine ⟨40476362744888574404057059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53968483659851432538742745 40476362744888574404057059)
                ·
                  refine ⟨60714544117332861606085589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40476362744888574404057059 60714544117332861606085589)
                  ·
                    refine ⟨1422997127749988943892631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60714544117332861606085589 1422997127749988943892631)
                    ·
                      rfl

theorem cell23_8313831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_8313831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313831 prefixEnd_8313831 := by exact prefixLift 8313831
  have htrace : WordTrace (prefixWord ++ tailWord_8313831) baseStart_8313831 baseEnd_8313831 := by
    simpa [prefixWord, tailWord_8313831, baseEnd_8313831] using wordTrace_append hprefix tailTrace_8313831
  have hstable : (prefixWord ++ tailWord_8313831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313831).length < 2 ^ (prefixWord ++ tailWord_8313831).sum := by decide
  have hdescent : baseEnd_8313831 < baseStart_8313831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313851 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 4]
def baseStart_8313851 : Nat := 118140960795 + 8313851 * 2 ^ 59
def prefixEnd_8313851 : Nat := 4983230072969 + 3 ^ 40 * 8313851 * 2
def baseEnd_8313851 : Nat := 4269001652863056753427801

theorem tailTrace_8313851 : CollatzResearch.WordTrace tailWord_8313851 prefixEnd_8313851 4269001652863056753427801 := by
  unfold tailWord_8313851
  simp only [CollatzResearch.WordTrace]
  refine ⟨303231057403345194552477407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202154038268896796368318271 303231057403345194552477407)
  ·
    refine ⟨454846586105017791828716111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303231057403345194552477407 454846586105017791828716111)
    ·
      refine ⟨682269879157526687743074167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454846586105017791828716111 682269879157526687743074167)
      ·
        refine ⟨1023404818736290031614611251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682269879157526687743074167 1023404818736290031614611251)
        ·
          refine ⟨1535107228104435047421916877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023404818736290031614611251 1535107228104435047421916877)
          ·
            refine ⟨575665210539163142783218829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1535107228104435047421916877 575665210539163142783218829)
            ·
              refine ⟨215874453952186178543707061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575665210539163142783218829 215874453952186178543707061)
              ·
                refine ⟨20238230058017454238472537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215874453952186178543707061 20238230058017454238472537)
                ·
                  refine ⟨15178672543513090678854403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20238230058017454238472537 15178672543513090678854403)
                  ·
                    refine ⟨22768008815269636018281605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15178672543513090678854403 22768008815269636018281605)
                    ·
                      refine ⟨4269001652863056753427801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22768008815269636018281605 4269001652863056753427801)
                      ·
                        rfl

theorem cell23_8313851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 4].length) (baseStart_8313851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313851 prefixEnd_8313851 := by exact prefixLift 8313851
  have htrace : WordTrace (prefixWord ++ tailWord_8313851) baseStart_8313851 baseEnd_8313851 := by
    simpa [prefixWord, tailWord_8313851, baseEnd_8313851] using wordTrace_append hprefix tailTrace_8313851
  have hstable : (prefixWord ++ tailWord_8313851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313851).length < 2 ^ (prefixWord ++ tailWord_8313851).sum := by decide
  have hdescent : baseEnd_8313851 < baseStart_8313851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313868 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_8313868 : Nat := 118140960795 + 8313868 * 2 ^ 59
def prefixEnd_8313868 : Nat := 4983230072969 + 3 ^ 40 * 8313868 * 2
def baseEnd_8313868 : Nat := 4269010382034183186915223

theorem tailTrace_8313868 : CollatzResearch.WordTrace tailWord_8313868 prefixEnd_8313868 4269010382034183186915223 := by
  unfold tailWord_8313868
  simp only [CollatzResearch.WordTrace]
  refine ⟨151615838722141803227923129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202154451629522404303897505 151615838722141803227923129)
  ·
    refine ⟨113711879041606352420942347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151615838722141803227923129 113711879041606352420942347)
    ·
      refine ⟨170567818562409528631413521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113711879041606352420942347 170567818562409528631413521)
      ·
        refine ⟨127925863921807146473560141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170567818562409528631413521 127925863921807146473560141)
        ·
          refine ⟨47972198970677679927585053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127925863921807146473560141 47972198970677679927585053)
          ·
            refine ⟨17989574614004129972844395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47972198970677679927585053 17989574614004129972844395)
            ·
              refine ⟨26984361921006194959266593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989574614004129972844395 26984361921006194959266593)
              ·
                refine ⟨20238271440754646219449945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26984361921006194959266593 20238271440754646219449945)
                ·
                  refine ⟨15178703580565984664587459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20238271440754646219449945 15178703580565984664587459)
                  ·
                    refine ⟨22768055370848976996881189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15178703580565984664587459 22768055370848976996881189)
                    ·
                      refine ⟨4269010382034183186915223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22768055370848976996881189 4269010382034183186915223)
                      ·
                        rfl

theorem cell23_8313868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_8313868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313868 prefixEnd_8313868 := by exact prefixLift 8313868
  have htrace : WordTrace (prefixWord ++ tailWord_8313868) baseStart_8313868 baseEnd_8313868 := by
    simpa [prefixWord, tailWord_8313868, baseEnd_8313868] using wordTrace_append hprefix tailTrace_8313868
  have hstable : (prefixWord ++ tailWord_8313868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313868).length < 2 ^ (prefixWord ++ tailWord_8313868).sum := by decide
  have hdescent : baseEnd_8313868 < baseStart_8313868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313938 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_8313938 : Nat := 118140960795 + 8313938 * 2 ^ 59
def prefixEnd_8313938 : Nat := 4983230072969 + 3 ^ 40 * 8313938 * 2
def baseEnd_8313938 : Nat := 1423015441893332637679967

theorem tailTrace_8313938 : CollatzResearch.WordTrace tailWord_8313938 prefixEnd_8313938 1423015441893332637679967 := by
  unfold tailWord_8313938
  simp only [CollatzResearch.WordTrace]
  refine ⟨75808557638507502102723617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202156153702686672273929645 75808557638507502102723617)
  ·
    refine ⟨56856418228880626577042713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75808557638507502102723617 56856418228880626577042713)
    ·
      refine ⟨42642313671660469932782035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56856418228880626577042713 42642313671660469932782035)
      ·
        refine ⟨63963470507490704899173053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42642313671660469932782035 63963470507490704899173053)
        ·
          refine ⟨23986301440309014337189895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63963470507490704899173053 23986301440309014337189895)
          ·
            refine ⟨35979452160463521505784843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23986301440309014337189895 35979452160463521505784843)
            ·
              refine ⟨53969178240695282258677265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35979452160463521505784843 53969178240695282258677265)
              ·
                refine ⟨40476883680521461694007949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53969178240695282258677265 40476883680521461694007949)
                ·
                  refine ⟨15178831380195548135252981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40476883680521461694007949 15178831380195548135252981)
                  ·
                    refine ⟨1423015441893332637679967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15178831380195548135252981 1423015441893332637679967)
                    ·
                      rfl

theorem cell23_8313938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_8313938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313938 prefixEnd_8313938 := by exact prefixLift 8313938
  have htrace : WordTrace (prefixWord ++ tailWord_8313938) baseStart_8313938 baseEnd_8313938 := by
    simpa [prefixWord, tailWord_8313938, baseEnd_8313938] using wordTrace_append hprefix tailTrace_8313938
  have hstable : (prefixWord ++ tailWord_8313938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313938).length < 2 ^ (prefixWord ++ tailWord_8313938).sum := by decide
  have hdescent : baseEnd_8313938 < baseStart_8313938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313962 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_8313962 : Nat := 118140960795 + 8313962 * 2 ^ 59
def prefixEnd_8313962 : Nat := 4983230072969 + 3 ^ 40 * 8313962 * 2
def baseEnd_8313962 : Nat := 4269058649215705819139791

theorem tailTrace_8313962 : CollatzResearch.WordTrace tailWord_8313962 prefixEnd_8313962 4269058649215705819139791 := by
  unfold tailWord_8313962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75808776476485765127442035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202156737270628707006512093 75808776476485765127442035)
  ·
    refine ⟨113713164714728647691163053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75808776476485765127442035 113713164714728647691163053)
    ·
      refine ⟨42642436768023242884186145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113713164714728647691163053 42642436768023242884186145)
      ·
        refine ⟨31981827576017432163139609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42642436768023242884186145 31981827576017432163139609)
        ·
          refine ⟨23986370682013074122354707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31981827576017432163139609 23986370682013074122354707)
          ·
            refine ⟨35979556023019611183532061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23986370682013074122354707 35979556023019611183532061)
            ·
              refine ⟨13492333508632354193824523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35979556023019611183532061 13492333508632354193824523)
              ·
                refine ⟨20238500262948531290736785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13492333508632354193824523 20238500262948531290736785)
                ·
                  refine ⟨15178875197211398468052589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20238500262948531290736785 15178875197211398468052589)
                  ·
                    refine ⟨5692078198954274425519721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15178875197211398468052589 5692078198954274425519721)
                    ·
                      refine ⟨4269058649215705819139791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692078198954274425519721 4269058649215705819139791)
                      ·
                        rfl

theorem cell23_8313962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_8313962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313962 prefixEnd_8313962 := by exact prefixLift 8313962
  have htrace : WordTrace (prefixWord ++ tailWord_8313962) baseStart_8313962 baseEnd_8313962 := by
    simpa [prefixWord, tailWord_8313962, baseEnd_8313962] using wordTrace_append hprefix tailTrace_8313962
  have hstable : (prefixWord ++ tailWord_8313962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313962).length < 2 ^ (prefixWord ++ tailWord_8313962).sum := by decide
  have hdescent : baseEnd_8313962 < baseStart_8313962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313968 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 4, 4]
def baseStart_8313968 : Nat := 118140960795 + 8313968 * 2 ^ 59
def prefixEnd_8313968 : Nat := 4983230072969 + 3 ^ 40 * 8313968 * 2
def baseEnd_8313968 : Nat := 1423020576699877598554921

theorem tailTrace_8313968 : CollatzResearch.WordTrace tailWord_8313968 prefixEnd_8313968 1423020576699877598554921 := by
  unfold tailWord_8313968
  simp only [CollatzResearch.WordTrace]
  refine ⟨151617662371960661767243279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202156883162614215689657705 151617662371960661767243279)
  ·
    refine ⟨227426493557940992650864919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151617662371960661767243279 227426493557940992650864919)
    ·
      refine ⟨341139740336911488976297379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227426493557940992650864919 341139740336911488976297379)
      ·
        refine ⟨511709610505367233464446069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341139740336911488976297379 511709610505367233464446069)
        ·
          refine ⟨47972775984878178137291819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 511709610505367233464446069 47972775984878178137291819)
          ·
            refine ⟨71959163977317267205937729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47972775984878178137291819 71959163977317267205937729)
            ·
              refine ⟨53969372982987950404453297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71959163977317267205937729 53969372982987950404453297)
              ·
                refine ⟨40477029737240962803339973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53969372982987950404453297 40477029737240962803339973)
                ·
                  refine ⟨7589443075732680525626245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40477029737240962803339973 7589443075732680525626245)
                  ·
                    refine ⟨1423020576699877598554921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589443075732680525626245 1423020576699877598554921)
                    ·
                      rfl

theorem cell23_8313968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_8313968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313968 prefixEnd_8313968 := by exact prefixLift 8313968
  have htrace : WordTrace (prefixWord ++ tailWord_8313968) baseStart_8313968 baseEnd_8313968 := by
    simpa [prefixWord, tailWord_8313968, baseEnd_8313968] using wordTrace_append hprefix tailTrace_8313968
  have hstable : (prefixWord ++ tailWord_8313968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313968).length < 2 ^ (prefixWord ++ tailWord_8313968).sum := by decide
  have hdescent : baseEnd_8313968 < baseStart_8313968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313975 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 5, 2, 2]
def baseStart_8313975 : Nat := 118140960795 + 8313975 * 2 ^ 59
def prefixEnd_8313975 : Nat := 4983230072969 + 3 ^ 40 * 8313975 * 2
def baseEnd_8313975 : Nat := 4269065324464214268277231

theorem tailTrace_8313975 : CollatzResearch.WordTrace tailWord_8313975 prefixEnd_8313975 4269065324464214268277231 := by
  unfold tailWord_8313975
  simp only [CollatzResearch.WordTrace]
  refine ⟨303235580054895963729991379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202157053369930642486660919 303235580054895963729991379)
  ·
    refine ⟨454853370082343945594987069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303235580054895963729991379 454853370082343945594987069)
    ·
      refine ⟨170570013780878979598120151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454853370082343945594987069 170570013780878979598120151)
      ·
        refine ⟨255855020671318469397180227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170570013780878979598120151 255855020671318469397180227)
        ·
          refine ⟨383782531006977704095770341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255855020671318469397180227 383782531006977704095770341)
          ·
            refine ⟨71959224563808319517956939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383782531006977704095770341 71959224563808319517956939)
            ·
              refine ⟨107938836845712479276935409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71959224563808319517956939 107938836845712479276935409)
              ·
                refine ⟨80954127634284359457701557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107938836845712479276935409 80954127634284359457701557)
                ·
                  refine ⟨7589449465714158699159521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80954127634284359457701557 7589449465714158699159521)
                  ·
                    refine ⟨5692087099285619024369641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589449465714158699159521 5692087099285619024369641)
                    ·
                      refine ⟨4269065324464214268277231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692087099285619024369641 4269065324464214268277231)
                      ·
                        rfl

theorem cell23_8313975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_8313975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313975 prefixEnd_8313975 := by exact prefixLift 8313975
  have htrace : WordTrace (prefixWord ++ tailWord_8313975) baseStart_8313975 baseEnd_8313975 := by
    simpa [prefixWord, tailWord_8313975, baseEnd_8313975] using wordTrace_append hprefix tailTrace_8313975
  have hstable : (prefixWord ++ tailWord_8313975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313975).length < 2 ^ (prefixWord ++ tailWord_8313975).sum := by decide
  have hdescent : baseEnd_8313975 < baseStart_8313975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313981 : List Nat := [1, 4, 1, 1, 3, 1, 12]
def baseStart_8313981 : Nat := 118140960795 + 8313981 * 2 ^ 59
def prefixEnd_8313981 : Nat := 4983230072969 + 3 ^ 40 * 8313981 * 2
def baseEnd_8313981 : Nat := 52704548214174583269163

theorem tailTrace_8313981 : CollatzResearch.WordTrace tailWord_8313981 prefixEnd_8313981 52704548214174583269163 := by
  unfold tailWord_8313981
  simp only [CollatzResearch.WordTrace]
  refine ⟨303235798892874226754709797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202157199261916151169806531 303235798892874226754709797)
  ·
    refine ⟨56856712292413917516508087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303235798892874226754709797 56856712292413917516508087)
    ·
      refine ⟨85285068438620876274762131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56856712292413917516508087 85285068438620876274762131)
      ·
        refine ⟨127927602657931314412143197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85285068438620876274762131 127927602657931314412143197)
        ·
          refine ⟨47972850996724242904553699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127927602657931314412143197 47972850996724242904553699)
          ·
            refine ⟨71959276495086364356830549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47972850996724242904553699 71959276495086364356830549)
            ·
              refine ⟨52704548214174583269163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71959276495086364356830549 52704548214174583269163)
              ·
                rfl

theorem cell23_8313981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 12].length) (baseStart_8313981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313981 prefixEnd_8313981 := by exact prefixLift 8313981
  have htrace : WordTrace (prefixWord ++ tailWord_8313981) baseStart_8313981 baseEnd_8313981 := by
    simpa [prefixWord, tailWord_8313981, baseEnd_8313981] using wordTrace_append hprefix tailTrace_8313981
  have hstable : (prefixWord ++ tailWord_8313981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313981).length < 2 ^ (prefixWord ++ tailWord_8313981).sum := by decide
  have hdescent : baseEnd_8313981 < baseStart_8313981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313985 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 4, 4]
def baseStart_8313985 : Nat := 118140960795 + 8313985 * 2 ^ 59
def prefixEnd_8313985 : Nat := 4983230072969 + 3 ^ 40 * 8313985 * 2
def baseEnd_8313985 : Nat := 1423023486423586409717395

theorem tailTrace_8313985 : CollatzResearch.WordTrace tailWord_8313985 prefixEnd_8313985 1423023486423586409717395 := by
  unfold tailWord_8313985
  simp only [CollatzResearch.WordTrace]
  refine ⟨303235944784859735437855409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202157296523239823625236939 303235944784859735437855409)
  ·
    refine ⟨227426958588644801578391557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303235944784859735437855409 227426958588644801578391557)
    ·
      refine ⟨42642554735370900295948417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227426958588644801578391557 42642554735370900295948417)
      ·
        refine ⟨31981916051528175221961313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42642554735370900295948417 31981916051528175221961313)
        ·
          refine ⟨23986437038646131416470985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31981916051528175221961313 23986437038646131416470985)
          ·
            refine ⟨17989827778984598562353239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23986437038646131416470985 17989827778984598562353239)
            ·
              refine ⟨26984741668476897843529859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989827778984598562353239 26984741668476897843529859)
              ·
                refine ⟨40477112502715346765294789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26984741668476897843529859 40477112502715346765294789)
                ·
                  refine ⟨7589458594259127518492773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40477112502715346765294789 7589458594259127518492773)
                  ·
                    refine ⟨1423023486423586409717395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589458594259127518492773 1423023486423586409717395)
                    ·
                      rfl

theorem cell23_8313985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_8313985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313985 prefixEnd_8313985 := by exact prefixLift 8313985
  have htrace : WordTrace (prefixWord ++ tailWord_8313985) baseStart_8313985 baseEnd_8313985 := by
    simpa [prefixWord, tailWord_8313985, baseEnd_8313985] using wordTrace_append hprefix tailTrace_8313985
  have hstable : (prefixWord ++ tailWord_8313985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313985).length < 2 ^ (prefixWord ++ tailWord_8313985).sum := by decide
  have hdescent : baseEnd_8313985 < baseStart_8313985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313991 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_8313991 : Nat := 118140960795 + 8313991 * 2 ^ 59
def prefixEnd_8313991 : Nat := 4983230072969 + 3 ^ 40 * 8313991 * 2
def baseEnd_8313991 : Nat := 4269073540154686205677157

theorem tailTrace_8313991 : CollatzResearch.WordTrace tailWord_8313991 prefixEnd_8313991 4269073540154686205677157 := by
  unfold tailWord_8313991
  simp only [CollatzResearch.WordTrace]
  refine ⟨303236163622837998462573827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202157442415225332308382551 303236163622837998462573827)
  ·
    refine ⟨454854245434256997693860741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303236163622837998462573827 454854245434256997693860741)
    ·
      refine ⟨85285171018923187067598889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454854245434256997693860741 85285171018923187067598889)
      ·
        refine ⟨63963878264192390300699167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85285171018923187067598889 63963878264192390300699167)
        ·
          refine ⟨95945817396288585451048751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63963878264192390300699167 95945817396288585451048751)
          ·
            refine ⟨143918726094432878176573127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95945817396288585451048751 143918726094432878176573127)
            ·
              refine ⟨215878089141649317264859691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143918726094432878176573127 215878089141649317264859691)
              ·
                refine ⟨323817133712473975897289537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215878089141649317264859691 323817133712473975897289537)
                ·
                  refine ⟨242862850284355481922967153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323817133712473975897289537 242862850284355481922967153)
                  ·
                    refine ⟨182147137713266611442225365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242862850284355481922967153 182147137713266611442225365)
                    ·
                      refine ⟨4269073540154686205677157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182147137713266611442225365 4269073540154686205677157)
                      ·
                        rfl

theorem cell23_8313991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_8313991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8313991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8313991 prefixEnd_8313991 := by exact prefixLift 8313991
  have htrace : WordTrace (prefixWord ++ tailWord_8313991) baseStart_8313991 baseEnd_8313991 := by
    simpa [prefixWord, tailWord_8313991, baseEnd_8313991] using wordTrace_append hprefix tailTrace_8313991
  have hstable : (prefixWord ++ tailWord_8313991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313991).length < 2 ^ (prefixWord ++ tailWord_8313991).sum := by decide
  have hdescent : baseEnd_8313991 < baseStart_8313991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314012 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_8314012 : Nat := 118140960795 + 8314012 * 2 ^ 59
def prefixEnd_8314012 : Nat := 4983230072969 + 3 ^ 40 * 8314012 * 2
def baseEnd_8314012 : Nat := 4269084323248430623514561

theorem tailTrace_8314012 : CollatzResearch.WordTrace tailWord_8314012 prefixEnd_8314012 4269084323248430623514561 := by
  unfold tailWord_8314012
  simp only [CollatzResearch.WordTrace]
  refine ⟨151618464777880959524544145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202157953037174612699392193 151618464777880959524544145)
  ·
    refine ⟨113713848583410719643408109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151618464777880959524544145 113713848583410719643408109)
    ·
      refine ⟨42642693218779019866278041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113713848583410719643408109 42642693218779019866278041)
      ·
        refine ⟨31982019914084264899708531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42642693218779019866278041 31982019914084264899708531)
        ·
          refine ⟨47973029871126397349562797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31982019914084264899708531 47973029871126397349562797)
          ·
            refine ⟨17989886201672399006086049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47973029871126397349562797 17989886201672399006086049)
            ·
              refine ⟨13492414651254299254564537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17989886201672399006086049 13492414651254299254564537)
              ·
                refine ⟨10119310988440724440923403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492414651254299254564537 10119310988440724440923403)
                ·
                  refine ⟨15178966482661086661385105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119310988440724440923403 15178966482661086661385105)
                  ·
                    refine ⟨11384224861995814996038829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15178966482661086661385105 11384224861995814996038829)
                    ·
                      refine ⟨4269084323248430623514561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384224861995814996038829 4269084323248430623514561)
                      ·
                        rfl

theorem cell23_8314012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_8314012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314012 prefixEnd_8314012 := by exact prefixLift 8314012
  have htrace : WordTrace (prefixWord ++ tailWord_8314012) baseStart_8314012 baseEnd_8314012 := by
    simpa [prefixWord, tailWord_8314012, baseEnd_8314012] using wordTrace_append hprefix tailTrace_8314012
  have hstable : (prefixWord ++ tailWord_8314012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314012).length < 2 ^ (prefixWord ++ tailWord_8314012).sum := by decide
  have hdescent : baseEnd_8314012 < baseStart_8314012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314065 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 1, 4, 2]
def baseStart_8314065 : Nat := 118140960795 + 8314065 * 2 ^ 59
def prefixEnd_8314065 : Nat := 4983230072969 + 3 ^ 40 * 8314065 * 2
def baseEnd_8314065 : Nat := 4269111537723118916151817

theorem tailTrace_8314065 : CollatzResearch.WordTrace tailWord_8314065 prefixEnd_8314065 4269111537723118916151817 := by
  unfold tailWord_8314065
  simp only [CollatzResearch.WordTrace]
  refine ⟨303238862624569909100767649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202159241749713272733845099 303238862624569909100767649)
  ·
    refine ⟨227429146968427431825575737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303238862624569909100767649 227429146968427431825575737)
    ·
      refine ⟨170571860226320573869181803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227429146968427431825575737 170571860226320573869181803)
      ·
        refine ⟨255857790339480860803772705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170571860226320573869181803 255857790339480860803772705)
        ·
          refine ⟨191893342754610645602829529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255857790339480860803772705 191893342754610645602829529)
          ·
            refine ⟨143920007065957984202122147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191893342754610645602829529 143920007065957984202122147)
            ·
              refine ⟨215880010598936976303183221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143920007065957984202122147 215880010598936976303183221)
              ·
                refine ⟨20238750993650341528423427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215880010598936976303183221 20238750993650341528423427)
                ·
                  refine ⟨30358126490475512292635141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20238750993650341528423427 30358126490475512292635141)
                  ·
                    refine ⟨5692148716964158554869089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30358126490475512292635141 5692148716964158554869089)
                    ·
                      refine ⟨4269111537723118916151817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692148716964158554869089 4269111537723118916151817)
                      ·
                        rfl

theorem cell23_8314065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_8314065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314065 prefixEnd_8314065 := by exact prefixLift 8314065
  have htrace : WordTrace (prefixWord ++ tailWord_8314065) baseStart_8314065 baseEnd_8314065 := by
    simpa [prefixWord, tailWord_8314065, baseEnd_8314065] using wordTrace_append hprefix tailTrace_8314065
  have hstable : (prefixWord ++ tailWord_8314065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314065).length < 2 ^ (prefixWord ++ tailWord_8314065).sum := by decide
  have hdescent : baseEnd_8314065 < baseStart_8314065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314069 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_8314069 : Nat := 118140960795 + 8314069 * 2 ^ 59
def prefixEnd_8314069 : Nat := 4983230072969 + 3 ^ 40 * 8314069 * 2
def baseEnd_8314069 : Nat := 4269113591645736900501799

theorem tailTrace_8314069 : CollatzResearch.WordTrace tailWord_8314069 prefixEnd_8314069 4269113591645736900501799 := by
  unfold tailWord_8314069
  simp only [CollatzResearch.WordTrace]
  refine ⟨303239008516555417783913261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202159339011036945189275507 303239008516555417783913261)
  ·
    refine ⟨113714628193708281668967473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303239008516555417783913261 113714628193708281668967473)
    ·
      refine ⟨85285971145281211251725605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113714628193708281668967473 85285971145281211251725605)
      ·
        refine ⟨15991119589740227109698551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85285971145281211251725605 15991119589740227109698551)
        ·
          refine ⟨23986679384610340664547827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15991119589740227109698551 23986679384610340664547827)
          ·
            refine ⟨35980019076915510996821741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23986679384610340664547827 35980019076915510996821741)
            ·
              refine ⟨13492507153843316623808153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35980019076915510996821741 13492507153843316623808153)
              ·
                refine ⟨10119380365382487467856115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492507153843316623808153 10119380365382487467856115)
                ·
                  refine ⟨15179070548073731201784173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119380365382487467856115 15179070548073731201784173)
                  ·
                    refine ⟨5692151455527649200669065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15179070548073731201784173 5692151455527649200669065)
                    ·
                      refine ⟨4269113591645736900501799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692151455527649200669065 4269113591645736900501799)
                      ·
                        rfl

theorem cell23_8314069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_8314069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314069 prefixEnd_8314069 := by exact prefixLift 8314069
  have htrace : WordTrace (prefixWord ++ tailWord_8314069) baseStart_8314069 baseEnd_8314069 := by
    simpa [prefixWord, tailWord_8314069, baseEnd_8314069] using wordTrace_append hprefix tailTrace_8314069
  have hstable : (prefixWord ++ tailWord_8314069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314069).length < 2 ^ (prefixWord ++ tailWord_8314069).sum := by decide
  have hdescent : baseEnd_8314069 < baseStart_8314069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314099 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 2, 2, 2]
def baseStart_8314099 : Nat := 118140960795 + 8314099 * 2 ^ 59
def prefixEnd_8314099 : Nat := 4983230072969 + 3 ^ 40 * 8314099 * 2
def baseEnd_8314099 : Nat := 4269128996065371783126661

theorem tailTrace_8314099 : CollatzResearch.WordTrace tailWord_8314099 prefixEnd_8314099 4269128996065371783126661 := by
  unfold tailWord_8314099
  simp only [CollatzResearch.WordTrace]
  refine ⟨303240102706446732907505351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202160068470964488605003567 303240102706446732907505351)
  ·
    refine ⟨454860154059670099361258027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303240102706446732907505351 454860154059670099361258027)
    ·
      refine ⟨682290231089505149041887041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454860154059670099361258027 682290231089505149041887041)
      ·
        refine ⟨511717673317128861781415281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682290231089505149041887041 511717673317128861781415281)
        ·
          refine ⟨383788254987846646336061461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511717673317128861781415281 383788254987846646336061461)
          ·
            refine ⟨17990074452555311547002881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383788254987846646336061461 17990074452555311547002881)
            ·
              refine ⟨13492555839416483660252161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17990074452555311547002881 13492555839416483660252161)
              ·
                refine ⟨10119416879562362745189121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492555839416483660252161 10119416879562362745189121)
                ·
                  refine ⟨7589562659671772058891841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10119416879562362745189121 7589562659671772058891841)
                  ·
                    refine ⟨5692171994753829044168881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589562659671772058891841 5692171994753829044168881)
                    ·
                      refine ⟨4269128996065371783126661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692171994753829044168881 4269128996065371783126661)
                      ·
                        rfl

theorem cell23_8314099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 2, 2].length) (baseStart_8314099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314099 prefixEnd_8314099 := by exact prefixLift 8314099
  have htrace : WordTrace (prefixWord ++ tailWord_8314099) baseStart_8314099 baseEnd_8314099 := by
    simpa [prefixWord, tailWord_8314099, baseEnd_8314099] using wordTrace_append hprefix tailTrace_8314099
  have hstable : (prefixWord ++ tailWord_8314099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314099).length < 2 ^ (prefixWord ++ tailWord_8314099).sum := by decide
  have hdescent : baseEnd_8314099 < baseStart_8314099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314105 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 5]
def baseStart_8314105 : Nat := 118140960795 + 8314105 * 2 ^ 59
def prefixEnd_8314105 : Nat := 4983230072969 + 3 ^ 40 * 8314105 * 2
def baseEnd_8314105 : Nat := 474348008549922084405737

theorem tailTrace_8314105 : CollatzResearch.WordTrace tailWord_8314105 prefixEnd_8314105 474348008549922084405737 := by
  unfold tailWord_8314105
  simp only [CollatzResearch.WordTrace]
  refine ⟨303240321544424995932223769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202160214362949997288149179 303240321544424995932223769)
  ·
    refine ⟨227430241158318746949167827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303240321544424995932223769 227430241158318746949167827)
    ·
      refine ⟨341145361737478120423751741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227430241158318746949167827 341145361737478120423751741)
      ·
        refine ⟨127929510651554295158906903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341145361737478120423751741 127929510651554295158906903)
        ·
          refine ⟨191894265977331442738360355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127929510651554295158906903 191894265977331442738360355)
          ·
            refine ⟨287841398965997164107540533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191894265977331442738360355 287841398965997164107540533)
            ·
              refine ⟨26985131153062234135081925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287841398965997164107540533 26985131153062234135081925)
              ·
                refine ⟨5059712091199168900327861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26985131153062234135081925 5059712091199168900327861)
                ·
                  refine ⟨474348008549922084405737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5059712091199168900327861 474348008549922084405737)
                  ·
                    rfl

theorem cell23_8314105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 5].length) (baseStart_8314105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314105 prefixEnd_8314105 := by exact prefixLift 8314105
  have htrace : WordTrace (prefixWord ++ tailWord_8314105) baseStart_8314105 baseEnd_8314105 := by
    simpa [prefixWord, tailWord_8314105, baseEnd_8314105] using wordTrace_append hprefix tailTrace_8314105
  have hstable : (prefixWord ++ tailWord_8314105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314105).length < 2 ^ (prefixWord ++ tailWord_8314105).sum := by decide
  have hdescent : baseEnd_8314105 < baseStart_8314105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314115 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 3]
def baseStart_8314115 : Nat := 118140960795 + 8314115 * 2 ^ 59
def prefixEnd_8314115 : Nat := 4983230072969 + 3 ^ 40 * 8314115 * 2
def baseEnd_8314115 : Nat := 4269137211755843720526587

theorem tailTrace_8314115 : CollatzResearch.WordTrace tailWord_8314115 prefixEnd_8314115 4269137211755843720526587 := by
  unfold tailWord_8314115
  simp only [CollatzResearch.WordTrace]
  refine ⟨303240686274388767640087799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202160457516259178426725199 303240686274388767640087799)
  ·
    refine ⟨454861029411583151460131699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303240686274388767640087799 454861029411583151460131699)
    ·
      refine ⟨682291544117374727190197549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454861029411583151460131699 682291544117374727190197549)
      ·
        refine ⟨255859329044015522696324081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682291544117374727190197549 255859329044015522696324081)
        ·
          refine ⟨191894496783011642022243061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255859329044015522696324081 191894496783011642022243061)
          ·
            refine ⟨17990109073407341439585287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191894496783011642022243061 17990109073407341439585287)
            ·
              refine ⟨26985163610111012159377931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17990109073407341439585287 26985163610111012159377931)
              ·
                refine ⟨40477745415166518239066897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26985163610111012159377931 40477745415166518239066897)
                ·
                  refine ⟨30358309061374888679300173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40477745415166518239066897 30358309061374888679300173)
                  ·
                    refine ⟨11384365898015583254737565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30358309061374888679300173 11384365898015583254737565)
                    ·
                      refine ⟨4269137211755843720526587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384365898015583254737565 4269137211755843720526587)
                      ·
                        rfl

theorem cell23_8314115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_8314115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314115 prefixEnd_8314115 := by exact prefixLift 8314115
  have htrace : WordTrace (prefixWord ++ tailWord_8314115) baseStart_8314115 baseEnd_8314115 := by
    simpa [prefixWord, tailWord_8314115, baseEnd_8314115] using wordTrace_append hprefix tailTrace_8314115
  have hstable : (prefixWord ++ tailWord_8314115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314115).length < 2 ^ (prefixWord ++ tailWord_8314115).sum := by decide
  have hdescent : baseEnd_8314115 < baseStart_8314115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314168 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_8314168 : Nat := 118140960795 + 8314168 * 2 ^ 59
def prefixEnd_8314168 : Nat := 4983230072969 + 3 ^ 40 * 8314168 * 2
def baseEnd_8314168 : Nat := 4269164426230532013163843

theorem tailTrace_8314168 : CollatzResearch.WordTrace tailWord_8314168 prefixEnd_8314168 4269164426230532013163843 := by
  unfold tailWord_8314168
  simp only [CollatzResearch.WordTrace]
  refine ⟨151621309671598378845883579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202161746228797838461178105 151621309671598378845883579)
  ·
    refine ⟨227431964507397568268825369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151621309671598378845883579 227431964507397568268825369)
    ·
      refine ⟨170573973380548176201619027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227431964507397568268825369 170573973380548176201619027)
      ·
        refine ⟨255860960070822264302428541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170573973380548176201619027 255860960070822264302428541)
        ·
          refine ⟨95947860026558349113410703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255860960070822264302428541 95947860026558349113410703)
          ·
            refine ⟨143921790039837523670116055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95947860026558349113410703 143921790039837523670116055)
            ·
              refine ⟨215882685059756285505174083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143921790039837523670116055 215882685059756285505174083)
              ·
                refine ⟨323824027589634428257761125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215882685059756285505174083 323824027589634428257761125)
                ·
                  refine ⟨60717005173056455298330211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323824027589634428257761125 60717005173056455298330211)
                  ·
                    refine ⟨91075507759584682947495317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60717005173056455298330211 91075507759584682947495317)
                    ·
                      refine ⟨4269164426230532013163843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91075507759584682947495317 4269164426230532013163843)
                      ·
                        rfl

theorem cell23_8314168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_8314168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314168 prefixEnd_8314168 := by exact prefixLift 8314168
  have htrace : WordTrace (prefixWord ++ tailWord_8314168) baseStart_8314168 baseEnd_8314168 := by
    simpa [prefixWord, tailWord_8314168, baseEnd_8314168] using wordTrace_append hprefix tailTrace_8314168
  have hstable : (prefixWord ++ tailWord_8314168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314168).length < 2 ^ (prefixWord ++ tailWord_8314168).sum := by decide
  have hdescent : baseEnd_8314168 < baseStart_8314168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314172 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_8314172 : Nat := 118140960795 + 8314172 * 2 ^ 59
def prefixEnd_8314172 : Nat := 4983230072969 + 3 ^ 40 * 8314172 * 2
def baseEnd_8314172 : Nat := 4269166480153149997513825

theorem tailTrace_8314172 : CollatzResearch.WordTrace tailWord_8314172 prefixEnd_8314172 4269166480153149997513825 := by
  unfold tailWord_8314172
  simp only [CollatzResearch.WordTrace]
  refine ⟨151621382617591133187456385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202161843490121510916608513 151621382617591133187456385)
  ·
    refine ⟨113716036963193349890592289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151621382617591133187456385 113716036963193349890592289)
    ·
      refine ⟨85287027722395012417944217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113716036963193349890592289 85287027722395012417944217)
      ·
        refine ⟨63965270791796259313458163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85287027722395012417944217 63965270791796259313458163)
        ·
          refine ⟨95947906187694388970187245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63965270791796259313458163 95947906187694388970187245)
          ·
            refine ⟨35980464820385395863820217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95947906187694388970187245 35980464820385395863820217)
            ·
              refine ⟨26985348615289046897865163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35980464820385395863820217 26985348615289046897865163)
              ·
                refine ⟨40478022922933570346797745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26985348615289046897865163 40478022922933570346797745)
                ·
                  refine ⟨30358517192200177760098309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40478022922933570346797745 30358517192200177760098309)
                  ·
                    refine ⟨5692221973537533330018433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30358517192200177760098309 5692221973537533330018433)
                    ·
                      refine ⟨4269166480153149997513825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692221973537533330018433 4269166480153149997513825)
                      ·
                        rfl

theorem cell23_8314172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_8314172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314172 prefixEnd_8314172 := by exact prefixLift 8314172
  have htrace : WordTrace (prefixWord ++ tailWord_8314172) baseStart_8314172 baseEnd_8314172 := by
    simpa [prefixWord, tailWord_8314172, baseEnd_8314172] using wordTrace_append hprefix tailTrace_8314172
  have hstable : (prefixWord ++ tailWord_8314172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314172).length < 2 ^ (prefixWord ++ tailWord_8314172).sum := by decide
  have hdescent : baseEnd_8314172 < baseStart_8314172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314175 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_8314175 : Nat := 118140960795 + 8314175 * 2 ^ 59
def prefixEnd_8314175 : Nat := 4983230072969 + 3 ^ 40 * 8314175 * 2
def baseEnd_8314175 : Nat := 4269168020595113485776311

theorem tailTrace_8314175 : CollatzResearch.WordTrace tailWord_8314175 prefixEnd_8314175 4269168020595113485776311 := by
  unfold tailWord_8314175
  simp only [CollatzResearch.WordTrace]
  refine ⟨303242874654171397887271979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202161916436114265258181319 303242874654171397887271979)
  ·
    refine ⟨454864311981257096830907969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303242874654171397887271979 454864311981257096830907969)
    ·
      refine ⟨341148233985942822623180977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454864311981257096830907969 341148233985942822623180977)
      ·
        refine ⟨255861175489457116967385733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341148233985942822623180977 255861175489457116967385733)
        ·
          refine ⟨47973970404273209431384825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255861175489457116967385733 47973970404273209431384825)
          ·
            refine ⟨35980477803204907073538619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47973970404273209431384825 35980477803204907073538619)
            ·
              refine ⟨53970716704807360610307929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35980477803204907073538619 53970716704807360610307929)
              ·
                refine ⟨40478037528605520457730947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53970716704807360610307929 40478037528605520457730947)
                ·
                  refine ⟨60717056292908280686596421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40478037528605520457730947 60717056292908280686596421)
                  ·
                    refine ⟨11384448054920302628736829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60717056292908280686596421 11384448054920302628736829)
                    ·
                      refine ⟨4269168020595113485776311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384448054920302628736829 4269168020595113485776311)
                      ·
                        rfl

theorem cell23_8314175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_8314175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314175 prefixEnd_8314175 := by exact prefixLift 8314175
  have htrace : WordTrace (prefixWord ++ tailWord_8314175) baseStart_8314175 baseEnd_8314175 := by
    simpa [prefixWord, tailWord_8314175, baseEnd_8314175] using wordTrace_append hprefix tailTrace_8314175
  have hstable : (prefixWord ++ tailWord_8314175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314175).length < 2 ^ (prefixWord ++ tailWord_8314175).sum := by decide
  have hdescent : baseEnd_8314175 < baseStart_8314175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314199 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 1, 4]
def baseStart_8314199 : Nat := 118140960795 + 8314199 * 2 ^ 59
def prefixEnd_8314199 : Nat := 4983230072969 + 3 ^ 40 * 8314199 * 2
def baseEnd_8314199 : Nat := 1423060114710273797292067

theorem tailTrace_8314199 : CollatzResearch.WordTrace tailWord_8314199 prefixEnd_8314199 1423060114710273797292067 := by
  unfold tailWord_8314199
  simp only [CollatzResearch.WordTrace]
  refine ⟨303243750006084449986145651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202162500004056299990763767 303243750006084449986145651)
  ·
    refine ⟨454865625009126674979218477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303243750006084449986145651 454865625009126674979218477)
    ·
      refine ⟨170574609378422503117206929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454865625009126674979218477 170574609378422503117206929)
      ·
        refine ⟨127930957033816877337905197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170574609378422503117206929 127930957033816877337905197)
        ·
          refine ⟨47974108887681329001714449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127930957033816877337905197 47974108887681329001714449)
          ·
            refine ⟨35980581665760996751285837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47974108887681329001714449 35980581665760996751285837)
            ·
              refine ⟨13492718124660373781732189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35980581665760996751285837 13492718124660373781732189)
              ·
                refine ⟨5059769296747640168149571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13492718124660373781732189 5059769296747640168149571)
                ·
                  refine ⟨7589653945121460252224357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059769296747640168149571 7589653945121460252224357)
                  ·
                    refine ⟨1423060114710273797292067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589653945121460252224357 1423060114710273797292067)
                    ·
                      rfl

theorem cell23_8314199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_8314199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314199 prefixEnd_8314199 := by exact prefixLift 8314199
  have htrace : WordTrace (prefixWord ++ tailWord_8314199) baseStart_8314199 baseEnd_8314199 := by
    simpa [prefixWord, tailWord_8314199, baseEnd_8314199] using wordTrace_append hprefix tailTrace_8314199
  have hstable : (prefixWord ++ tailWord_8314199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314199).length < 2 ^ (prefixWord ++ tailWord_8314199).sum := by decide
  have hdescent : baseEnd_8314199 < baseStart_8314199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314216 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 3, 4]
def baseStart_8314216 : Nat := 118140960795 + 8314216 * 2 ^ 59
def prefixEnd_8314216 : Nat := 4983230072969 + 3 ^ 40 * 8314216 * 2
def baseEnd_8314216 : Nat := 1423063024433982608454541

theorem tailTrace_8314216 : CollatzResearch.WordTrace tailWord_8314216 prefixEnd_8314216 1423063024433982608454541 := by
  unfold tailWord_8314216
  simp only [CollatzResearch.WordTrace]
  refine ⟨151622185023511430944757251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202162913364681907926343001 151622185023511430944757251)
  ·
    refine ⟨227433277535267146417135877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151622185023511430944757251 227433277535267146417135877)
    ·
      refine ⟨42643739537862589953212977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227433277535267146417135877 42643739537862589953212977)
      ·
        refine ⟨31982804653396942464909733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42643739537862589953212977 31982804653396942464909733)
        ·
          refine ⟨5996775872511926712170575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31982804653396942464909733 5996775872511926712170575)
          ·
            refine ⟨8995163808767890068255863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996775872511926712170575 8995163808767890068255863)
            ·
              refine ⟨13492745713151835102383795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995163808767890068255863 13492745713151835102383795)
              ·
                refine ⟨20239118569727752653575693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13492745713151835102383795 20239118569727752653575693)
                ·
                  refine ⟨7589669463647907245090885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20239118569727752653575693 7589669463647907245090885)
                  ·
                    refine ⟨1423063024433982608454541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589669463647907245090885 1423063024433982608454541)
                    ·
                      rfl

theorem cell23_8314216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_8314216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314216 prefixEnd_8314216 := by exact prefixLift 8314216
  have htrace : WordTrace (prefixWord ++ tailWord_8314216) baseStart_8314216 baseEnd_8314216 := by
    simpa [prefixWord, tailWord_8314216, baseEnd_8314216] using wordTrace_append hprefix tailTrace_8314216
  have hstable : (prefixWord ++ tailWord_8314216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314216).length < 2 ^ (prefixWord ++ tailWord_8314216).sum := by decide
  have hdescent : baseEnd_8314216 < baseStart_8314216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314275 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4]
def baseStart_8314275 : Nat := 118140960795 + 8314275 * 2 ^ 59
def prefixEnd_8314275 : Nat := 4983230072969 + 3 ^ 40 * 8314275 * 2
def baseEnd_8314275 : Nat := 4269219368660563094525851

theorem tailTrace_8314275 : CollatzResearch.WordTrace tailWord_8314275 prefixEnd_8314275 4269219368660563094525851 := by
  unfold tailWord_8314275
  simp only [CollatzResearch.WordTrace]
  refine ⟨303246521953809114965912279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202164347969206076643941519 303246521953809114965912279)
  ·
    refine ⟨454869782930713672448868419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303246521953809114965912279 454869782930713672448868419)
    ·
      refine ⟨682304674396070508673302629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454869782930713672448868419 682304674396070508673302629)
      ·
        refine ⟨127932126449263220376244243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682304674396070508673302629 127932126449263220376244243)
        ·
          refine ⟨191898189673894830564366365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127932126449263220376244243 191898189673894830564366365)
          ·
            refine ⟨71961821127710561461637387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191898189673894830564366365 71961821127710561461637387)
            ·
              refine ⟨107942731691565842192456081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71961821127710561461637387 107942731691565842192456081)
              ·
                refine ⟨80957048768674381644342061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107942731691565842192456081 80957048768674381644342061)
                ·
                  refine ⟨30358893288252893116628273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80957048768674381644342061 30358893288252893116628273)
                  ·
                    refine ⟨22769169966189669837471205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30358893288252893116628273 22769169966189669837471205)
                    ·
                      refine ⟨4269219368660563094525851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22769169966189669837471205 4269219368660563094525851)
                      ·
                        rfl

theorem cell23_8314275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_8314275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314275 prefixEnd_8314275 := by exact prefixLift 8314275
  have htrace : WordTrace (prefixWord ++ tailWord_8314275) baseStart_8314275 baseEnd_8314275 := by
    simpa [prefixWord, tailWord_8314275, baseEnd_8314275] using wordTrace_append hprefix tailTrace_8314275
  have hstable : (prefixWord ++ tailWord_8314275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314275).length < 2 ^ (prefixWord ++ tailWord_8314275).sum := by decide
  have hdescent : baseEnd_8314275 < baseStart_8314275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314312 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_8314312 : Nat := 118140960795 + 8314312 * 2 ^ 59
def prefixEnd_8314312 : Nat := 4983230072969 + 3 ^ 40 * 8314312 * 2
def baseEnd_8314312 : Nat := 4269238367444779449763181

theorem tailTrace_8314312 : CollatzResearch.WordTrace tailWord_8314312 prefixEnd_8314312 4269238367444779449763181 := by
  unfold tailWord_8314312
  simp only [CollatzResearch.WordTrace]
  refine ⟨151623935727337535142504595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202165247636450046856672793 151623935727337535142504595)
  ·
    refine ⟨227435903591006302713756893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151623935727337535142504595 227435903591006302713756893)
    ·
      refine ⟨85288463846627363517658835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227435903591006302713756893 85288463846627363517658835)
      ·
        refine ⟨127932695769941045276488253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85288463846627363517658835 127932695769941045276488253)
        ·
          refine ⟨47974760913727891978683095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127932695769941045276488253 47974760913727891978683095)
          ·
            refine ⟨71962141370591837968024643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47974760913727891978683095 71962141370591837968024643)
            ·
              refine ⟨107943212055887756952036965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71962141370591837968024643 107943212055887756952036965)
              ·
                refine ⟨20239352260478954428506931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107943212055887756952036965 20239352260478954428506931)
                ·
                  refine ⟨30359028390718431642760397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20239352260478954428506931 30359028390718431642760397)
                  ·
                    refine ⟨11384635646519411866035149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30359028390718431642760397 11384635646519411866035149)
                    ·
                      refine ⟨4269238367444779449763181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384635646519411866035149 4269238367444779449763181)
                      ·
                        rfl

theorem cell23_8314312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_8314312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314312 prefixEnd_8314312 := by exact prefixLift 8314312
  have htrace : WordTrace (prefixWord ++ tailWord_8314312) baseStart_8314312 baseEnd_8314312 := by
    simpa [prefixWord, tailWord_8314312, baseEnd_8314312] using wordTrace_append hprefix tailTrace_8314312
  have hstable : (prefixWord ++ tailWord_8314312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314312).length < 2 ^ (prefixWord ++ tailWord_8314312).sum := by decide
  have hdescent : baseEnd_8314312 < baseStart_8314312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314316 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 1, 2, 3]
def baseStart_8314316 : Nat := 118140960795 + 8314316 * 2 ^ 59
def prefixEnd_8314316 : Nat := 4983230072969 + 3 ^ 40 * 8314316 * 2
def baseEnd_8314316 : Nat := 4269240421367397434113163

theorem tailTrace_8314316 : CollatzResearch.WordTrace tailWord_8314316 prefixEnd_8314316 4269240421367397434113163 := by
  unfold tailWord_8314316
  simp only [CollatzResearch.WordTrace]
  refine ⟨151624008673330289484077401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202165344897773719312103201 151624008673330289484077401)
  ·
    refine ⟨113718006504997717113058051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151624008673330289484077401 113718006504997717113058051)
    ·
      refine ⟨170577009757496575669587077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113718006504997717113058051 170577009757496575669587077)
      ·
        refine ⟨31983189329530607938047577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170577009757496575669587077 31983189329530607938047577)
        ·
          refine ⟨23987391997147955953535683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31983189329530607938047577 23987391997147955953535683)
          ·
            refine ⟨35981087995721933930303525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23987391997147955953535683 35981087995721933930303525)
            ·
              refine ⟨6746453999197862611931911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35981087995721933930303525 6746453999197862611931911)
              ·
                refine ⟨10119680998796793917897867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6746453999197862611931911 10119680998796793917897867)
                ·
                  refine ⟨15179521498195190876846801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119680998796793917897867 15179521498195190876846801)
                  ·
                    refine ⟨11384641123646393157635101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15179521498195190876846801 11384641123646393157635101)
                    ·
                      refine ⟨4269240421367397434113163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384641123646393157635101 4269240421367397434113163)
                      ·
                        rfl

theorem cell23_8314316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_8314316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314316 prefixEnd_8314316 := by exact prefixLift 8314316
  have htrace : WordTrace (prefixWord ++ tailWord_8314316) baseStart_8314316 baseEnd_8314316 := by
    simpa [prefixWord, tailWord_8314316, baseEnd_8314316] using wordTrace_append hprefix tailTrace_8314316
  have hstable : (prefixWord ++ tailWord_8314316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314316).length < 2 ^ (prefixWord ++ tailWord_8314316).sum := by decide
  have hdescent : baseEnd_8314316 < baseStart_8314316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314329 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 3]
def baseStart_8314329 : Nat := 118140960795 + 8314329 * 2 ^ 59
def prefixEnd_8314329 : Nat := 4983230072969 + 3 ^ 40 * 8314329 * 2
def baseEnd_8314329 : Nat := 4269247096615905883250603

theorem tailTrace_8314329 : CollatzResearch.WordTrace tailWord_8314329 prefixEnd_8314329 4269247096615905883250603 := by
  unfold tailWord_8314329
  simp only [CollatzResearch.WordTrace]
  refine ⟨303248491495613482188378041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202165660997075654792252027 303248491495613482188378041)
  ·
    refine ⟨227436368621710111641283531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303248491495613482188378041 227436368621710111641283531)
    ·
      refine ⟨341154552932565167461925297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227436368621710111641283531 341154552932565167461925297)
      ·
        refine ⟨255865914699423875596443973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341154552932565167461925297 255865914699423875596443973)
        ·
          refine ⟨47974859006141976674333245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255865914699423875596443973 47974859006141976674333245)
          ·
            refine ⟨17990572127303241252874967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47974859006141976674333245 17990572127303241252874967)
            ·
              refine ⟨26985858190954861879312451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17990572127303241252874967 26985858190954861879312451)
              ·
                refine ⟨40478787286432292818968677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26985858190954861879312451 40478787286432292818968677)
                ·
                  refine ⟨7589772616206054903556627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40478787286432292818968677 7589772616206054903556627)
                  ·
                    refine ⟨11384658924309082355334941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7589772616206054903556627 11384658924309082355334941)
                    ·
                      refine ⟨4269247096615905883250603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384658924309082355334941 4269247096615905883250603)
                      ·
                        rfl

theorem cell23_8314329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_8314329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314329 prefixEnd_8314329 := by exact prefixLift 8314329
  have htrace : WordTrace (prefixWord ++ tailWord_8314329) baseStart_8314329 baseEnd_8314329 := by
    simpa [prefixWord, tailWord_8314329, baseEnd_8314329] using wordTrace_append hprefix tailTrace_8314329
  have hstable : (prefixWord ++ tailWord_8314329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314329).length < 2 ^ (prefixWord ++ tailWord_8314329).sum := by decide
  have hdescent : baseEnd_8314329 < baseStart_8314329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314346 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_8314346 : Nat := 118140960795 + 8314346 * 2 ^ 59
def prefixEnd_8314346 : Nat := 4983230072969 + 3 ^ 40 * 8314346 * 2
def baseEnd_8314346 : Nat := 4269255825787032316738025

theorem tailTrace_8314346 : CollatzResearch.WordTrace tailWord_8314346 prefixEnd_8314346 4269255825787032316738025 := by
  unfold tailWord_8314346
  simp only [CollatzResearch.WordTrace]
  refine ⟨75812277884137973522936723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202166074357701262727831261 75812277884137973522936723)
  ·
    refine ⟨113718416826206960284405085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75812277884137973522936723 113718416826206960284405085)
    ·
      refine ⟨42644406309827610106651907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113718416826206960284405085 42644406309827610106651907)
      ·
        refine ⟨63966609464741415159977861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42644406309827610106651907 63966609464741415159977861)
        ·
          refine ⟨11993739274639015342495849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63966609464741415159977861 11993739274639015342495849)
          ·
            refine ⟨8995304455979261506871887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11993739274639015342495849 8995304455979261506871887)
            ·
              refine ⟨13492956683968892260307831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995304455979261506871887 13492956683968892260307831)
              ·
                refine ⟨20239435025953338390461747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13492956683968892260307831 20239435025953338390461747)
                ·
                  refine ⟨30359152538930007585692621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20239435025953338390461747 30359152538930007585692621)
                  ·
                    refine ⟨11384682202098752844634733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30359152538930007585692621 11384682202098752844634733)
                    ·
                      refine ⟨4269255825787032316738025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384682202098752844634733 4269255825787032316738025)
                      ·
                        rfl

theorem cell23_8314346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_8314346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314346 prefixEnd_8314346 := by exact prefixLift 8314346
  have htrace : WordTrace (prefixWord ++ tailWord_8314346) baseStart_8314346 baseEnd_8314346 := by
    simpa [prefixWord, tailWord_8314346, baseEnd_8314346] using wordTrace_append hprefix tailTrace_8314346
  have hstable : (prefixWord ++ tailWord_8314346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314346).length < 2 ^ (prefixWord ++ tailWord_8314346).sum := by decide
  have hdescent : baseEnd_8314346 < baseStart_8314346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314385 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_8314385 : Nat := 118140960795 + 8314385 * 2 ^ 59
def prefixEnd_8314385 : Nat := 4983230072969 + 3 ^ 40 * 8314385 * 2
def baseEnd_8314385 : Nat := 4269275851532557664150345

theorem tailTrace_8314385 : CollatzResearch.WordTrace tailWord_8314385 prefixEnd_8314385 4269275851532557664150345 := by
  unfold tailWord_8314385
  simp only [CollatzResearch.WordTrace]
  refine ⟨303250533983410603752416609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202167022655607069168277739 303250533983410603752416609)
  ·
    refine ⟨227437900487557952814312457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303250533983410603752416609 227437900487557952814312457)
    ·
      refine ⟨170578425365668464610734343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227437900487557952814312457 170578425365668464610734343)
      ·
        refine ⟨255867638048502696916101515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170578425365668464610734343 255867638048502696916101515)
        ·
          refine ⟨383801457072754045374152273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255867638048502696916101515 383801457072754045374152273)
          ·
            refine ⟨287851092804565534030614205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383801457072754045374152273 287851092804565534030614205)
            ·
              refine ⟨107944159801712075261480327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287851092804565534030614205 107944159801712075261480327)
              ·
                refine ⟨161916239702568112892220491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107944159801712075261480327 161916239702568112892220491)
                ·
                  refine ⟨242874359553852169338330737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161916239702568112892220491 242874359553852169338330737)
                  ·
                    refine ⟨182155769665389127003748053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242874359553852169338330737 182155769665389127003748053)
                    ·
                      refine ⟨4269275851532557664150345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182155769665389127003748053 4269275851532557664150345)
                      ·
                        rfl

theorem cell23_8314385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_8314385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314385 prefixEnd_8314385 := by exact prefixLift 8314385
  have htrace : WordTrace (prefixWord ++ tailWord_8314385) baseStart_8314385 baseEnd_8314385 := by
    simpa [prefixWord, tailWord_8314385, baseEnd_8314385] using wordTrace_append hprefix tailTrace_8314385
  have hstable : (prefixWord ++ tailWord_8314385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314385).length < 2 ^ (prefixWord ++ tailWord_8314385).sum := by decide
  have hdescent : baseEnd_8314385 < baseStart_8314385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314403 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 2, 2, 2]
def baseStart_8314403 : Nat := 118140960795 + 8314403 * 2 ^ 59
def prefixEnd_8314403 : Nat := 4983230072969 + 3 ^ 40 * 8314403 * 2
def baseEnd_8314403 : Nat := 4269285094184338593725263

theorem tailTrace_8314403 : CollatzResearch.WordTrace tailWord_8314403 prefixEnd_8314403 4269285094184338593725263 := by
  unfold tailWord_8314403
  simp only [CollatzResearch.WordTrace]
  refine ⟨303251190497345392826571863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202167460331563595217714575 303251190497345392826571863)
  ·
    refine ⟨454876785746018089239857795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303251190497345392826571863 454876785746018089239857795)
    ·
      refine ⟨682315178619027133859786693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454876785746018089239857795 682315178619027133859786693)
      ·
        refine ⟨127934095991067587598710005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682315178619027133859786693 127934095991067587598710005)
        ·
          refine ⟨11993821499162586337379063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127934095991067587598710005 11993821499162586337379063)
          ·
            refine ⟨17990732248743879506068595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11993821499162586337379063 17990732248743879506068595)
            ·
              refine ⟨26986098373115819259102893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17990732248743879506068595 26986098373115819259102893)
              ·
                refine ⟨10119786889918432222163585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26986098373115819259102893 10119786889918432222163585)
                ·
                  refine ⟨7589840167438824166622689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10119786889918432222163585 7589840167438824166622689)
                  ·
                    refine ⟨5692380125579118124967017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589840167438824166622689 5692380125579118124967017)
                    ·
                      refine ⟨4269285094184338593725263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692380125579118124967017 4269285094184338593725263)
                      ·
                        rfl

theorem cell23_8314403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_8314403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314403 prefixEnd_8314403 := by exact prefixLift 8314403
  have htrace : WordTrace (prefixWord ++ tailWord_8314403) baseStart_8314403 baseEnd_8314403 := by
    simpa [prefixWord, tailWord_8314403, baseEnd_8314403] using wordTrace_append hprefix tailTrace_8314403
  have hstable : (prefixWord ++ tailWord_8314403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314403).length < 2 ^ (prefixWord ++ tailWord_8314403).sum := by decide
  have hdescent : baseEnd_8314403 < baseStart_8314403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314469 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_8314469 : Nat := 118140960795 + 8314469 * 2 ^ 59
def prefixEnd_8314469 : Nat := 4983230072969 + 3 ^ 40 * 8314469 * 2
def baseEnd_8314469 : Nat := 1423106327969178445166653

theorem tailTrace_8314469 : CollatzResearch.WordTrace tailWord_8314469 prefixEnd_8314469 1423106327969178445166653 := by
  unfold tailWord_8314469
  simp only [CollatzResearch.WordTrace]
  refine ⟨303253597715106286098474461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202169065143404190732316307 303253597715106286098474461)
  ·
    refine ⟨113720099143164857286927923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303253597715106286098474461 113720099143164857286927923)
    ·
      refine ⟨170580148714747285930391885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113720099143164857286927923 170580148714747285930391885)
      ·
        refine ⟨63967555768030232223896957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170580148714747285930391885 63967555768030232223896957)
        ·
          refine ⟨23987833413011337083961359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63967555768030232223896957 23987833413011337083961359)
          ·
            refine ⟨35981750119517005625942039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23987833413011337083961359 35981750119517005625942039)
            ·
              refine ⟨53972625179275508438913059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35981750119517005625942039 53972625179275508438913059)
              ·
                refine ⟨80958937768913262658369589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53972625179275508438913059 80958937768913262658369589)
                ·
                  refine ⟨7589900415835618374222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80958937768913262658369589 7589900415835618374222149)
                  ·
                    refine ⟨1423106327969178445166653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589900415835618374222149 1423106327969178445166653)
                    ·
                      rfl

theorem cell23_8314469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_8314469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314469 prefixEnd_8314469 := by exact prefixLift 8314469
  have htrace : WordTrace (prefixWord ++ tailWord_8314469) baseStart_8314469 baseEnd_8314469 := by
    simpa [prefixWord, tailWord_8314469, baseEnd_8314469] using wordTrace_append hprefix tailTrace_8314469
  have hstable : (prefixWord ++ tailWord_8314469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314469).length < 2 ^ (prefixWord ++ tailWord_8314469).sum := by decide
  have hdescent : baseEnd_8314469 < baseStart_8314469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314512 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_8314512 : Nat := 118140960795 + 8314512 * 2 ^ 59
def prefixEnd_8314512 : Nat := 4983230072969 + 3 ^ 40 * 8314512 * 2
def baseEnd_8314512 : Nat := 1423113687858559555754087

theorem tailTrace_8314512 : CollatzResearch.WordTrace tailWord_8314512 prefixEnd_8314512 1423113687858559555754087 := by
  unfold tailWord_8314512
  simp only [CollatzResearch.WordTrace]
  refine ⟨151627583026975252221144895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202170110702633669628193193 151627583026975252221144895)
  ·
    refine ⟨227441374540462878331717343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151627583026975252221144895 227441374540462878331717343)
    ·
      refine ⟨341162061810694317497576015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227441374540462878331717343 341162061810694317497576015)
      ·
        refine ⟨511743092716041476246364023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341162061810694317497576015 511743092716041476246364023)
        ·
          refine ⟨767614639074062214369546035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511743092716041476246364023 767614639074062214369546035)
          ·
            refine ⟨1151421958611093321554319053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767614639074062214369546035 1151421958611093321554319053)
            ·
              refine ⟨431783234479159995582869645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1151421958611093321554319053 431783234479159995582869645)
              ·
                refine ⟨161918712929684998343576117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431783234479159995582869645 161918712929684998343576117)
                ·
                  refine ⟨15179879337157968594710261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161918712929684998343576117 15179879337157968594710261)
                  ·
                    refine ⟨1423113687858559555754087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15179879337157968594710261 1423113687858559555754087)
                    ·
                      rfl

theorem cell23_8314512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_8314512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314512 prefixEnd_8314512 := by exact prefixLift 8314512
  have htrace : WordTrace (prefixWord ++ tailWord_8314512) baseStart_8314512 baseEnd_8314512 := by
    simpa [prefixWord, tailWord_8314512, baseEnd_8314512] using wordTrace_append hprefix tailTrace_8314512
  have hstable : (prefixWord ++ tailWord_8314512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314512).length < 2 ^ (prefixWord ++ tailWord_8314512).sum := by decide
  have hdescent : baseEnd_8314512 < baseStart_8314512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314559 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 4, 4]
def baseStart_8314559 : Nat := 118140960795 + 8314559 * 2 ^ 59
def prefixEnd_8314559 : Nat := 4983230072969 + 3 ^ 40 * 8314559 * 2
def baseEnd_8314559 : Nat := 1423121732388813327791515

theorem tailTrace_8314559 : CollatzResearch.WordTrace tailWord_8314559 prefixEnd_8314559 1423121732388813327791515 := by
  unfold tailWord_8314559
  simp only [CollatzResearch.WordTrace]
  refine ⟨303256880284780231469250731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202171253523186820979500487 303256880284780231469250731)
  ·
    refine ⟨454885320427170347203876097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303256880284780231469250731 454885320427170347203876097)
    ·
      refine ⟨341163990320377760402907073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454885320427170347203876097 341163990320377760402907073)
      ·
        refine ⟨255872992740283320302180305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341163990320377760402907073 255872992740283320302180305)
        ·
          refine ⟨191904744555212490226635229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255872992740283320302180305 191904744555212490226635229)
          ·
            refine ⟨71964279208204683834988211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191904744555212490226635229 71964279208204683834988211)
            ·
              refine ⟨107946418812307025752482317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71964279208204683834988211 107946418812307025752482317)
              ·
                refine ⟨40479907054615134657180869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107946418812307025752482317 40479907054615134657180869)
                ·
                  refine ⟨7589982572740337748221413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40479907054615134657180869 7589982572740337748221413)
                  ·
                    refine ⟨1423121732388813327791515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7589982572740337748221413 1423121732388813327791515)
                    ·
                      rfl

theorem cell23_8314559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_8314559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314559 prefixEnd_8314559 := by exact prefixLift 8314559
  have htrace : WordTrace (prefixWord ++ tailWord_8314559) baseStart_8314559 baseEnd_8314559 := by
    simpa [prefixWord, tailWord_8314559, baseEnd_8314559] using wordTrace_append hprefix tailTrace_8314559
  have hstable : (prefixWord ++ tailWord_8314559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314559).length < 2 ^ (prefixWord ++ tailWord_8314559).sum := by decide
  have hdescent : baseEnd_8314559 < baseStart_8314559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314560 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 1, 1, 3]
def baseStart_8314560 : Nat := 118140960795 + 8314560 * 2 ^ 59
def prefixEnd_8314560 : Nat := 4983230072969 + 3 ^ 40 * 8314560 * 2
def baseEnd_8314560 : Nat := 4269365710647094479462041

theorem tailTrace_8314560 : CollatzResearch.WordTrace tailWord_8314560 prefixEnd_8314560 4269365710647094479462041 := by
  unfold tailWord_8314560
  simp only [CollatzResearch.WordTrace]
  refine ⟨151628458378888304320018567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202171277838517739093358089 151628458378888304320018567)
  ·
    refine ⟨227442687568332456480027851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151628458378888304320018567 227442687568332456480027851)
    ·
      refine ⟨341164031352498684720041777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227442687568332456480027851 341164031352498684720041777)
      ·
        refine ⟨255873023514374013540031333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341164031352498684720041777 255873023514374013540031333)
        ·
          refine ⟨47976191908945127538755875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255873023514374013540031333 47976191908945127538755875)
          ·
            refine ⟨71964287863417691308133813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47976191908945127538755875 71964287863417691308133813)
            ·
              refine ⟨6746651987195408560137545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71964287863417691308133813 6746651987195408560137545)
              ·
                refine ⟨5059988990396556420103159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6746651987195408560137545 5059988990396556420103159)
                ·
                  refine ⟨7589983485594834630154739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059988990396556420103159 7589983485594834630154739)
                  ·
                    refine ⟨11384975228392251945232109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7589983485594834630154739 11384975228392251945232109)
                    ·
                      refine ⟨4269365710647094479462041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11384975228392251945232109 4269365710647094479462041)
                      ·
                        rfl

theorem cell23_8314560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_8314560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314560 prefixEnd_8314560 := by exact prefixLift 8314560
  have htrace : WordTrace (prefixWord ++ tailWord_8314560) baseStart_8314560 baseEnd_8314560 := by
    simpa [prefixWord, tailWord_8314560, baseEnd_8314560] using wordTrace_append hprefix tailTrace_8314560
  have hstable : (prefixWord ++ tailWord_8314560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314560).length < 2 ^ (prefixWord ++ tailWord_8314560).sum := by decide
  have hdescent : baseEnd_8314560 < baseStart_8314560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314586 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_8314586 : Nat := 118140960795 + 8314586 * 2 ^ 59
def prefixEnd_8314586 : Nat := 4983230072969 + 3 ^ 40 * 8314586 * 2
def baseEnd_8314586 : Nat := 4269379061144111377736921

theorem tailTrace_8314586 : CollatzResearch.WordTrace tailWord_8314586 prefixEnd_8314586 4269379061144111377736921 := by
  unfold tailWord_8314586
  simp only [CollatzResearch.WordTrace]
  refine ⟨75814466263920603770120903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202171910037121610053655741 75814466263920603770120903)
  ·
    refine ⟨113721699395880905655181355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75814466263920603770120903 113721699395880905655181355)
    ·
      refine ⟨170582549093821358482772033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113721699395880905655181355 170582549093821358482772033)
      ·
        refine ⟨127936911820366018862079025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170582549093821358482772033 127936911820366018862079025)
        ·
          refine ⟨95952683865274514146559269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127936911820366018862079025 95952683865274514146559269)
          ·
            refine ⟨17991128224738971402479863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95952683865274514146559269 17991128224738971402479863)
            ·
              refine ⟨26986692337108457103719795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17991128224738971402479863 26986692337108457103719795)
              ·
                refine ⟨40480038505662685655579693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26986692337108457103719795 40480038505662685655579693)
                ·
                  refine ⟨15180014439623507120842385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40480038505662685655579693 15180014439623507120842385)
                  ·
                    refine ⟨11385010829717630340631789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15180014439623507120842385 11385010829717630340631789)
                    ·
                      refine ⟨4269379061144111377736921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11385010829717630340631789 4269379061144111377736921)
                      ·
                        rfl

theorem cell23_8314586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_8314586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314586 prefixEnd_8314586 := by exact prefixLift 8314586
  have htrace : WordTrace (prefixWord ++ tailWord_8314586) baseStart_8314586 baseEnd_8314586 := by
    simpa [prefixWord, tailWord_8314586, baseEnd_8314586] using wordTrace_append hprefix tailTrace_8314586
  have hstable : (prefixWord ++ tailWord_8314586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314586).length < 2 ^ (prefixWord ++ tailWord_8314586).sum := by decide
  have hdescent : baseEnd_8314586 < baseStart_8314586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314659 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5]
def baseStart_8314659 : Nat := 118140960795 + 8314659 * 2 ^ 59
def prefixEnd_8314659 : Nat := 4983230072969 + 3 ^ 40 * 8314659 * 2
def baseEnd_8314659 : Nat := 4269416545231889592124085

theorem tailTrace_8314659 : CollatzResearch.WordTrace tailWord_8314659 prefixEnd_8314659 4269416545231889592124085 := by
  unfold tailWord_8314659
  simp only [CollatzResearch.WordTrace]
  refine ⟨303260527584417948547891031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202173685056278632365260687 303260527584417948547891031)
  ·
    refine ⟨454890791376626922821836547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303260527584417948547891031 454890791376626922821836547)
    ·
      refine ⟨682336187064940384232754821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454890791376626922821836547 682336187064940384232754821)
      ·
        refine ⟨127938035074676322043641529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682336187064940384232754821 127938035074676322043641529)
        ·
          refine ⟨95953526306007241532731147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127938035074676322043641529 95953526306007241532731147)
          ·
            refine ⟨143930289459010862299096721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95953526306007241532731147 143930289459010862299096721)
            ·
              refine ⟨107947717094258146724322541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143930289459010862299096721 107947717094258146724322541)
              ·
                refine ⟨40480393910346805021620953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107947717094258146724322541 40480393910346805021620953)
                ·
                  refine ⟨30360295432760103766215715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40480393910346805021620953 30360295432760103766215715)
                  ·
                    refine ⟨45540443149140155649323573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30360295432760103766215715 45540443149140155649323573)
                    ·
                      refine ⟨4269416545231889592124085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45540443149140155649323573 4269416545231889592124085)
                      ·
                        rfl

theorem cell23_8314659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_8314659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314659 prefixEnd_8314659 := by exact prefixLift 8314659
  have htrace : WordTrace (prefixWord ++ tailWord_8314659) baseStart_8314659 baseEnd_8314659 := by
    simpa [prefixWord, tailWord_8314659, baseEnd_8314659] using wordTrace_append hprefix tailTrace_8314659
  have hstable : (prefixWord ++ tailWord_8314659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314659).length < 2 ^ (prefixWord ++ tailWord_8314659).sum := by decide
  have hdescent : baseEnd_8314659 < baseStart_8314659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314660 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_8314660 : Nat := 118140960795 + 8314660 * 2 ^ 59
def prefixEnd_8314660 : Nat := 4983230072969 + 3 ^ 40 * 8314660 * 2
def baseEnd_8314660 : Nat := 4269417058712544088211581

theorem tailTrace_8314660 : CollatzResearch.WordTrace tailWord_8314660 prefixEnd_8314660 4269417058712544088211581 := by
  unfold tailWord_8314660
  simp only [CollatzResearch.WordTrace]
  refine ⟨151630282028707162859338717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202173709371609550479118289 151630282028707162859338717)
  ·
    refine ⟨56861355760765186072252019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151630282028707162859338717 56861355760765186072252019)
    ·
      refine ⟨85292033641147779108378029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56861355760765186072252019 85292033641147779108378029)
      ·
        refine ⟨31984512615430417165641761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85292033641147779108378029 31984512615430417165641761)
        ·
          refine ⟨23988384461572812874231321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31984512615430417165641761 23988384461572812874231321)
          ·
            refine ⟨17991288346179609655673491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23988384461572812874231321 17991288346179609655673491)
            ·
              refine ⟨26986932519269414483510237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17991288346179609655673491 26986932519269414483510237)
              ·
                refine ⟨10120099694726030431316339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26986932519269414483510237 10120099694726030431316339)
                ·
                  refine ⟨15180149542089045646974509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10120099694726030431316339 15180149542089045646974509)
                  ·
                    refine ⟨5692556078283392117615441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15180149542089045646974509 5692556078283392117615441)
                    ·
                      refine ⟨4269417058712544088211581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692556078283392117615441 4269417058712544088211581)
                      ·
                        rfl

theorem cell23_8314660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_8314660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314660 prefixEnd_8314660 := by exact prefixLift 8314660
  have htrace : WordTrace (prefixWord ++ tailWord_8314660) baseStart_8314660 baseEnd_8314660 := by
    simpa [prefixWord, tailWord_8314660, baseEnd_8314660] using wordTrace_append hprefix tailTrace_8314660
  have hstable : (prefixWord ++ tailWord_8314660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314660).length < 2 ^ (prefixWord ++ tailWord_8314660).sum := by decide
  have hdescent : baseEnd_8314660 < baseStart_8314660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314694 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_8314694 : Nat := 118140960795 + 8314694 * 2 ^ 59
def prefixEnd_8314694 : Nat := 4983230072969 + 3 ^ 40 * 8314694 * 2
def baseEnd_8314694 : Nat := 4269434517054796955186425

theorem tailTrace_8314694 : CollatzResearch.WordTrace tailWord_8314694 prefixEnd_8314694 4269434517054796955186425 := by
  unfold tailWord_8314694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476931379352848422669223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202174536092860766350276757 9476931379352848422669223)
  ·
    refine ⟨14215397069029272634003835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9476931379352848422669223 14215397069029272634003835)
    ·
      refine ⟨21323095603543908951005753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14215397069029272634003835 21323095603543908951005753)
      ·
        refine ⟨15992321702657931713254315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21323095603543908951005753 15992321702657931713254315)
        ·
          refine ⟨23988482553986897569881473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992321702657931713254315 23988482553986897569881473)
          ·
            refine ⟨17991361915490173177411105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23988482553986897569881473 17991361915490173177411105)
            ·
              refine ⟨13493521436617629883058329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17991361915490173177411105 13493521436617629883058329)
              ·
                refine ⟨10120141077463222412293747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13493521436617629883058329 10120141077463222412293747)
                ·
                  refine ⟨15180211616194833618440621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10120141077463222412293747 15180211616194833618440621)
                  ·
                    refine ⟨5692579356073062606915233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15180211616194833618440621 5692579356073062606915233)
                    ·
                      refine ⟨4269434517054796955186425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692579356073062606915233 4269434517054796955186425)
                      ·
                        rfl

theorem cell23_8314694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_8314694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314694 prefixEnd_8314694 := by exact prefixLift 8314694
  have htrace : WordTrace (prefixWord ++ tailWord_8314694) baseStart_8314694 baseEnd_8314694 := by
    simpa [prefixWord, tailWord_8314694, baseEnd_8314694] using wordTrace_append hprefix tailTrace_8314694
  have hstable : (prefixWord ++ tailWord_8314694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314694).length < 2 ^ (prefixWord ++ tailWord_8314694).sum := by decide
  have hdescent : baseEnd_8314694 < baseStart_8314694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314730 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_8314730 : Nat := 118140960795 + 8314730 * 2 ^ 59
def prefixEnd_8314730 : Nat := 4983230072969 + 3 ^ 40 * 8314730 * 2
def baseEnd_8314730 : Nat := 474383666928706534926251

theorem tailTrace_8314730 : CollatzResearch.WordTrace tailWord_8314730 prefixEnd_8314730 474383666928706534926251 := by
  unfold tailWord_8314730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75815779291790181918431411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202175411444773818449150429 75815779291790181918431411)
  ·
    refine ⟨113723668937685272877647117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75815779291790181918431411 113723668937685272877647117)
    ·
      refine ⟨42646375851631977329117669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113723668937685272877647117 42646375851631977329117669)
      ·
        refine ⟨7996195472180995749209563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42646375851631977329117669 7996195472180995749209563)
        ·
          refine ⟨11994293208271493623814345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996195472180995749209563 11994293208271493623814345)
          ·
            refine ⟨8995719906203620217860759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11994293208271493623814345 8995719906203620217860759)
            ·
              refine ⟨13493579859305430326791139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995719906203620217860759 13493579859305430326791139)
              ·
                refine ⟨20240369788958145490186709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13493579859305430326791139 20240369788958145490186709)
                ·
                  refine ⟨474383666928706534926251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20240369788958145490186709 474383666928706534926251)
                  ·
                    rfl

theorem cell23_8314730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_8314730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314730 prefixEnd_8314730 := by exact prefixLift 8314730
  have htrace : WordTrace (prefixWord ++ tailWord_8314730) baseStart_8314730 baseEnd_8314730 := by
    simpa [prefixWord, tailWord_8314730, baseEnd_8314730] using wordTrace_append hprefix tailTrace_8314730
  have hstable : (prefixWord ++ tailWord_8314730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314730).length < 2 ^ (prefixWord ++ tailWord_8314730).sum := by decide
  have hdescent : baseEnd_8314730 < baseStart_8314730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314769 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 10]
def baseStart_8314769 : Nat := 118140960795 + 8314769 * 2 ^ 59
def prefixEnd_8314769 : Nat := 4983230072969 + 3 ^ 40 * 8314769 * 2
def baseEnd_8314769 : Nat := 474385892011542684638731

theorem tailTrace_8314769 : CollatzResearch.WordTrace tailWord_8314769 prefixEnd_8314769 474385892011542684638731 := by
  unfold tailWord_8314769
  simp only [CollatzResearch.WordTrace]
  refine ⟨303264539614019437334395361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202176359742679624889596907 303264539614019437334395361)
  ·
    refine ⟨227448404710514578000796521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303264539614019437334395361 227448404710514578000796521)
    ·
      refine ⟨170586303532885933500597391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227448404710514578000796521 170586303532885933500597391)
      ·
        refine ⟨255879455299328900250896087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170586303532885933500597391 255879455299328900250896087)
        ·
          refine ⟨383819182948993350376344131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255879455299328900250896087 383819182948993350376344131)
          ·
            refine ⟨575728774423490025564516197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383819182948993350376344131 575728774423490025564516197)
            ·
              refine ⟨107949145204404379793346787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575728774423490025564516197 107949145204404379793346787)
              ·
                refine ⟨161923717806606569690020181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107949145204404379793346787 161923717806606569690020181)
                ·
                  refine ⟨474385892011542684638731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 161923717806606569690020181 474385892011542684638731)
                  ·
                    rfl

theorem cell23_8314769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_8314769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314769 prefixEnd_8314769 := by exact prefixLift 8314769
  have htrace : WordTrace (prefixWord ++ tailWord_8314769) baseStart_8314769 baseEnd_8314769 := by
    simpa [prefixWord, tailWord_8314769, baseEnd_8314769] using wordTrace_append hprefix tailTrace_8314769
  have hstable : (prefixWord ++ tailWord_8314769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314769).length < 2 ^ (prefixWord ++ tailWord_8314769).sum := by decide
  have hdescent : baseEnd_8314769 < baseStart_8314769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314816 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_8314816 : Nat := 118140960795 + 8314816 * 2 ^ 59
def prefixEnd_8314816 : Nat := 4983230072969 + 3 ^ 40 * 8314816 * 2
def baseEnd_8314816 : Nat := 1423165720564881825953621

theorem tailTrace_8314816 : CollatzResearch.WordTrace tailWord_8314816 prefixEnd_8314816 1423165720564881825953621 := by
  unfold tailWord_8314816
  simp only [CollatzResearch.WordTrace]
  refine ⟨151633126922424582180678151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202177502563232776240904201 151633126922424582180678151)
  ·
    refine ⟨227449690383636873271017227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151633126922424582180678151 227449690383636873271017227)
    ·
      refine ⟨341174535575455309906525841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227449690383636873271017227 341174535575455309906525841)
      ·
        refine ⟨255880901681591482429894381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341174535575455309906525841 255880901681591482429894381)
        ·
          refine ⟨95955338130596805911210393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255880901681591482429894381 95955338130596805911210393)
          ·
            refine ⟨71966503597947604433407795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95955338130596805911210393 71966503597947604433407795)
            ·
              refine ⟨107949755396921406650111693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71966503597947604433407795 107949755396921406650111693)
              ·
                refine ⟨40481158273845527493791885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107949755396921406650111693 40481158273845527493791885)
                ·
                  refine ⟨15180434352692072810171957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40481158273845527493791885 15180434352692072810171957)
                  ·
                    refine ⟨1423165720564881825953621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15180434352692072810171957 1423165720564881825953621)
                    ·
                      rfl

theorem cell23_8314816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_8314816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314816 prefixEnd_8314816 := by exact prefixLift 8314816
  have htrace : WordTrace (prefixWord ++ tailWord_8314816) baseStart_8314816 baseEnd_8314816 := by
    simpa [prefixWord, tailWord_8314816, baseEnd_8314816] using wordTrace_append hprefix tailTrace_8314816
  have hstable : (prefixWord ++ tailWord_8314816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314816).length < 2 ^ (prefixWord ++ tailWord_8314816).sum := by decide
  have hdescent : baseEnd_8314816 < baseStart_8314816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314847 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 1, 1, 3]
def baseStart_8314847 : Nat := 118140960795 + 8314847 * 2 ^ 59
def prefixEnd_8314847 : Nat := 4983230072969 + 3 ^ 40 * 8314847 * 2
def baseEnd_8314847 : Nat := 4269513079594934856573221

theorem tailTrace_8314847 : CollatzResearch.WordTrace tailWord_8314847 prefixEnd_8314847 4269513079594934856573221 := by
  unfold tailWord_8314847
  simp only [CollatzResearch.WordTrace]
  refine ⟨303267384507736856655734795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202178256338491237770489863 303267384507736856655734795)
  ·
    refine ⟨454901076761605284983602193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303267384507736856655734795 454901076761605284983602193)
    ·
      refine ⟨341175807571203963737701645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454901076761605284983602193 341175807571203963737701645)
      ·
        refine ⟨127940927839201486401638117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341175807571203963737701645 127940927839201486401638117)
        ·
          refine ⟨23988923969850278700307147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127940927839201486401638117 23988923969850278700307147)
          ·
            refine ⟨35983385954775418050460721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23988923969850278700307147 35983385954775418050460721)
            ·
              refine ⟨26987539466081563537845541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35983385954775418050460721 26987539466081563537845541)
              ·
                refine ⟨5060163649890293163346039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26987539466081563537845541 5060163649890293163346039)
                ·
                  refine ⟨7590245474835439745019059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060163649890293163346039 7590245474835439745019059)
                  ·
                    refine ⟨11385368212253159617528589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7590245474835439745019059 11385368212253159617528589)
                    ·
                      refine ⟨4269513079594934856573221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11385368212253159617528589 4269513079594934856573221)
                      ·
                        rfl

theorem cell23_8314847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_8314847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314847 prefixEnd_8314847 := by exact prefixLift 8314847
  have htrace : WordTrace (prefixWord ++ tailWord_8314847) baseStart_8314847 baseEnd_8314847 := by
    simpa [prefixWord, tailWord_8314847, baseEnd_8314847] using wordTrace_append hprefix tailTrace_8314847
  have hstable : (prefixWord ++ tailWord_8314847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314847).length < 2 ^ (prefixWord ++ tailWord_8314847).sum := by decide
  have hdescent : baseEnd_8314847 < baseStart_8314847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314876 : List Nat := [2, 2, 2, 1, 2, 2, 3, 9]
def baseStart_8314876 : Nat := 118140960795 + 8314876 * 2 ^ 59
def prefixEnd_8314876 : Nat := 4983230072969 + 3 ^ 40 * 8314876 * 2
def baseEnd_8314876 : Nat := 158130665575330194189281

theorem tailTrace_8314876 : CollatzResearch.WordTrace tailWord_8314876 prefixEnd_8314876 158130665575330194189281 := by
  unfold tailWord_8314876
  simp only [CollatzResearch.WordTrace]
  refine ⟨151634221112315897304270241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202178961483087863072360321 151634221112315897304270241)
  ·
    refine ⟨113725665834236922978202681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151634221112315897304270241 113725665834236922978202681)
    ·
      refine ⟨85294249375677692233652011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113725665834236922978202681 85294249375677692233652011)
      ·
        refine ⟨127941374063516538350478017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85294249375677692233652011 127941374063516538350478017)
        ·
          refine ⟨95956030547637403762858513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127941374063516538350478017 95956030547637403762858513)
          ·
            refine ⟨71967022910728052822143885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95956030547637403762858513 71967022910728052822143885)
            ·
              refine ⟨26987633591523019808303957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71967022910728052822143885 26987633591523019808303957)
              ·
                refine ⟨158130665575330194189281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26987633591523019808303957 158130665575330194189281)
                ·
                  rfl

theorem cell23_8314876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 9].length) (baseStart_8314876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314876 prefixEnd_8314876 := by exact prefixLift 8314876
  have htrace : WordTrace (prefixWord ++ tailWord_8314876) baseStart_8314876 baseEnd_8314876 := by
    simpa [prefixWord, tailWord_8314876, baseEnd_8314876] using wordTrace_append hprefix tailTrace_8314876
  have hstable : (prefixWord ++ tailWord_8314876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314876).length < 2 ^ (prefixWord ++ tailWord_8314876).sum := by decide
  have hdescent : baseEnd_8314876 < baseStart_8314876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314890 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_8314890 : Nat := 118140960795 + 8314890 * 2 ^ 59
def prefixEnd_8314890 : Nat := 4983230072969 + 3 ^ 40 * 8314890 * 2
def baseEnd_8314890 : Nat := 4269535159263078188335523

theorem tailTrace_8314890 : CollatzResearch.WordTrace tailWord_8314890 prefixEnd_8314890 4269535159263078188335523 := by
  unfold tailWord_8314890
  simp only [CollatzResearch.WordTrace]
  refine ⟨75817238211645268749887531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202179301897720716666366749 75817238211645268749887531)
  ·
    refine ⟨113725857317467903124831297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75817238211645268749887531 113725857317467903124831297)
    ·
      refine ⟨85294392988100927343623473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113725857317467903124831297 85294392988100927343623473)
      ·
        refine ⟨63970794741075695507717605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85294392988100927343623473 63970794741075695507717605)
        ·
          refine ⟨11994524013951692907697051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63970794741075695507717605 11994524013951692907697051)
          ·
            refine ⟨17991786020927539361545577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11994524013951692907697051 17991786020927539361545577)
            ·
              refine ⟨13493839515695654521159183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17991786020927539361545577 13493839515695654521159183)
              ·
                refine ⟨20240759273543481781738775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13493839515695654521159183 20240759273543481781738775)
                ·
                  refine ⟨30361138910315222672608163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20240759273543481781738775 30361138910315222672608163)
                  ·
                    refine ⟨45541708365472834008912245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30361138910315222672608163 45541708365472834008912245)
                    ·
                      refine ⟨4269535159263078188335523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45541708365472834008912245 4269535159263078188335523)
                      ·
                        rfl

theorem cell23_8314890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_8314890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314890 prefixEnd_8314890 := by exact prefixLift 8314890
  have htrace : WordTrace (prefixWord ++ tailWord_8314890) baseStart_8314890 baseEnd_8314890 := by
    simpa [prefixWord, tailWord_8314890, baseEnd_8314890] using wordTrace_append hprefix tailTrace_8314890
  have hstable : (prefixWord ++ tailWord_8314890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314890).length < 2 ^ (prefixWord ++ tailWord_8314890).sum := by decide
  have hdescent : baseEnd_8314890 < baseStart_8314890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314983 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 7]
def baseStart_8314983 : Nat := 118140960795 + 8314983 * 2 ^ 59
def prefixEnd_8314983 : Nat := 4983230072969 + 3 ^ 40 * 8314983 * 2
def baseEnd_8314983 : Nat := 474398101440438480496955

theorem tailTrace_8314983 : CollatzResearch.WordTrace tailWord_8314983 prefixEnd_8314983 474398101440438480496955 := by
  unfold tailWord_8314983
  simp only [CollatzResearch.WordTrace]
  refine ⟨303272344835244151882685603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202181563223496101255123735 303272344835244151882685603)
  ·
    refine ⟨454908517252866227824028405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303272344835244151882685603 454908517252866227824028405)
    ·
      refine ⟨42647673492456208858502663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454908517252866227824028405 42647673492456208858502663)
      ·
        refine ⟨63971510238684313287753995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42647673492456208858502663 63971510238684313287753995)
        ·
          refine ⟨95957265358026469931630993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63971510238684313287753995 95957265358026469931630993)
          ·
            refine ⟨71967949018519852448723245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95957265358026469931630993 71967949018519852448723245)
            ·
              refine ⟨26987980881944944668271217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71967949018519852448723245 26987980881944944668271217)
              ·
                refine ⟨20240985661458708501203413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26987980881944944668271217 20240985661458708501203413)
                ·
                  refine ⟨474398101440438480496955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20240985661458708501203413 474398101440438480496955)
                  ·
                    rfl

theorem cell23_8314983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 7].length) (baseStart_8314983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314983 prefixEnd_8314983 := by exact prefixLift 8314983
  have htrace : WordTrace (prefixWord ++ tailWord_8314983) baseStart_8314983 baseEnd_8314983 := by
    simpa [prefixWord, tailWord_8314983, baseEnd_8314983] using wordTrace_append hprefix tailTrace_8314983
  have hstable : (prefixWord ++ tailWord_8314983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314983).length < 2 ^ (prefixWord ++ tailWord_8314983).sum := by decide
  have hdescent : baseEnd_8314983 < baseStart_8314983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8314993 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_8314993 : Nat := 118140960795 + 8314993 * 2 ^ 59
def prefixEnd_8314993 : Nat := 4983230072969 + 3 ^ 40 * 8314993 * 2
def baseEnd_8314993 : Nat := 4269588047770491285347549

theorem tailTrace_8314993 : CollatzResearch.WordTrace tailWord_8314993 prefixEnd_8314993 4269588047770491285347549 := by
  unfold tailWord_8314993
  simp only [CollatzResearch.WordTrace]
  refine ⟨303272709565207923590549633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202181806376805282393699755 303272709565207923590549633)
  ·
    refine ⟨227454532173905942692912225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303272709565207923590549633 227454532173905942692912225)
    ·
      refine ⟨170590899130429457019684169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227454532173905942692912225 170590899130429457019684169)
      ·
        refine ⟨127943174347822092764763127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170590899130429457019684169 127943174347822092764763127)
        ·
          refine ⟨191914761521733139147144691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127943174347822092764763127 191914761521733139147144691)
          ·
            refine ⟨287872142282599708720717037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191914761521733139147144691 287872142282599708720717037)
            ·
              refine ⟨107952053355974890770268889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287872142282599708720717037 107952053355974890770268889)
              ·
                refine ⟨80964040016981168077701667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107952053355974890770268889 80964040016981168077701667)
                ·
                  refine ⟨121446060025471752116552501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80964040016981168077701667 121446060025471752116552501)
                  ·
                    refine ⟨11385568127387976760926797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121446060025471752116552501 11385568127387976760926797)
                    ·
                      refine ⟨4269588047770491285347549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11385568127387976760926797 4269588047770491285347549)
                      ·
                        rfl

theorem cell23_8314993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_8314993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8314993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8314993 prefixEnd_8314993 := by exact prefixLift 8314993
  have htrace : WordTrace (prefixWord ++ tailWord_8314993) baseStart_8314993 baseEnd_8314993 := by
    simpa [prefixWord, tailWord_8314993, baseEnd_8314993] using wordTrace_append hprefix tailTrace_8314993
  have hstable : (prefixWord ++ tailWord_8314993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8314993).length < 2 ^ (prefixWord ++ tailWord_8314993).sum := by decide
  have hdescent : baseEnd_8314993 < baseStart_8314993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8314993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315028 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_8315028 : Nat := 118140960795 + 8315028 * 2 ^ 59
def prefixEnd_8315028 : Nat := 4983230072969 + 3 ^ 40 * 8315028 * 2
def baseEnd_8315028 : Nat := 4269606019593398648409889

theorem tailTrace_8315028 : CollatzResearch.WordTrace tailWord_8315028 prefixEnd_8315028 4269606019593398648409889 := by
  unfold tailWord_8315028
  simp only [CollatzResearch.WordTrace]
  refine ⟨151636993060040562284036869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202182657413387416378715825 151636993060040562284036869)
  ·
    refine ⟨28431936198757605428256913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151636993060040562284036869 28431936198757605428256913)
    ·
      refine ⟨21323952149068204071192685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28431936198757605428256913 21323952149068204071192685)
      ·
        refine ⟨7996482055900576526697257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21323952149068204071192685 7996482055900576526697257)
        ·
          refine ⟨5997361541925432395022943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7996482055900576526697257 5997361541925432395022943)
          ·
            refine ⟨8996042312888148592534415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997361541925432395022943 8996042312888148592534415)
            ·
              refine ⟨13494063469332222888801623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996042312888148592534415 13494063469332222888801623)
              ·
                refine ⟨20241095203998334333202435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13494063469332222888801623 20241095203998334333202435)
                ·
                  refine ⟨30361642805997501499803653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20241095203998334333202435 30361642805997501499803653)
                  ·
                    refine ⟨5692808026124531531213185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30361642805997501499803653 5692808026124531531213185)
                    ·
                      refine ⟨4269606019593398648409889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692808026124531531213185 4269606019593398648409889)
                      ·
                        rfl

theorem cell23_8315028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_8315028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315028 prefixEnd_8315028 := by exact prefixLift 8315028
  have htrace : WordTrace (prefixWord ++ tailWord_8315028) baseStart_8315028 baseEnd_8315028 := by
    simpa [prefixWord, tailWord_8315028, baseEnd_8315028] using wordTrace_append hprefix tailTrace_8315028
  have hstable : (prefixWord ++ tailWord_8315028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315028).length < 2 ^ (prefixWord ++ tailWord_8315028).sum := by decide
  have hdescent : baseEnd_8315028 < baseStart_8315028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315074 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_8315074 : Nat := 118140960795 + 8315074 * 2 ^ 59
def prefixEnd_8315074 : Nat := 4983230072969 + 3 ^ 40 * 8315074 * 2
def baseEnd_8315074 : Nat := 4269629639703505468434677

theorem tailTrace_8315074 : CollatzResearch.WordTrace tailWord_8315074 prefixEnd_8315074 4269629639703505468434677 := by
  unfold tailWord_8315074
  simp only [CollatzResearch.WordTrace]
  refine ⟨75818915969478618606062069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202183775918609649616165517 75818915969478618606062069)
  ·
    refine ⟨7108023372138620494318319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75818915969478618606062069 7108023372138620494318319)
    ·
      refine ⟨10662035058207930741477479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7108023372138620494318319 10662035058207930741477479)
      ·
        refine ⟨15993052587311896112216219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662035058207930741477479 15993052587311896112216219)
        ·
          refine ⟨23989578880967844168324329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15993052587311896112216219 23989578880967844168324329)
          ·
            refine ⟨17992184160725883126243247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23989578880967844168324329 17992184160725883126243247)
            ·
              refine ⟨26988276241088824689364871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17992184160725883126243247 26988276241088824689364871)
              ·
                refine ⟨40482414361633237034047307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26988276241088824689364871 40482414361633237034047307)
                ·
                  refine ⟨60723621542449855551070961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40482414361633237034047307 60723621542449855551070961)
                  ·
                    refine ⟨45542716156837391663303221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60723621542449855551070961 45542716156837391663303221)
                    ·
                      refine ⟨4269629639703505468434677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45542716156837391663303221 4269629639703505468434677)
                      ·
                        rfl

theorem cell23_8315074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_8315074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315074 prefixEnd_8315074 := by exact prefixLift 8315074
  have htrace : WordTrace (prefixWord ++ tailWord_8315074) baseStart_8315074 baseEnd_8315074 := by
    simpa [prefixWord, tailWord_8315074, baseEnd_8315074] using wordTrace_append hprefix tailTrace_8315074
  have hstable : (prefixWord ++ tailWord_8315074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315074).length < 2 ^ (prefixWord ++ tailWord_8315074).sum := by decide
  have hdescent : baseEnd_8315074 < baseStart_8315074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315077 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_8315077 : Nat := 118140960795 + 8315077 * 2 ^ 59
def prefixEnd_8315077 : Nat := 4983230072969 + 3 ^ 40 * 8315077 * 2
def baseEnd_8315077 : Nat := 1423210393381822985565721

theorem tailTrace_8315077 : CollatzResearch.WordTrace tailWord_8315077 prefixEnd_8315077 1423210393381822985565721 := by
  unfold tailWord_8315077
  simp only [CollatzResearch.WordTrace]
  refine ⟨303275773296903605936607485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202183848864602403957738323 303275773296903605936607485)
  ·
    refine ⟨113728414986338852226227807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303275773296903605936607485 113728414986338852226227807)
    ·
      refine ⟨170592622479508278339341711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113728414986338852226227807 170592622479508278339341711)
      ·
        refine ⟨255888933719262417509012567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170592622479508278339341711 255888933719262417509012567)
        ·
          refine ⟨383833400578893626263518851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255888933719262417509012567 383833400578893626263518851)
          ·
            refine ⟨575750100868340439395278277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383833400578893626263518851 575750100868340439395278277)
            ·
              refine ⟨107953143912813832386614677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575750100868340439395278277 107953143912813832386614677)
              ·
                refine ⟨5060303620913148393122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107953143912813832386614677 5060303620913148393122563)
                ·
                  refine ⟨7590455431369722589683845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060303620913148393122563 7590455431369722589683845)
                  ·
                    refine ⟨1423210393381822985565721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590455431369722589683845 1423210393381822985565721)
                    ·
                      rfl

theorem cell23_8315077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_8315077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315077 prefixEnd_8315077 := by exact prefixLift 8315077
  have htrace : WordTrace (prefixWord ++ tailWord_8315077) baseStart_8315077 baseEnd_8315077 := by
    simpa [prefixWord, tailWord_8315077, baseEnd_8315077] using wordTrace_append hprefix tailTrace_8315077
  have hstable : (prefixWord ++ tailWord_8315077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315077).length < 2 ^ (prefixWord ++ tailWord_8315077).sum := by decide
  have hdescent : baseEnd_8315077 < baseStart_8315077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315120 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 1, 5]
def baseStart_8315120 : Nat := 118140960795 + 8315120 * 2 ^ 59
def prefixEnd_8315120 : Nat := 4983230072969 + 3 ^ 40 * 8315120 * 2
def baseEnd_8315120 : Nat := 1423217753271204096153155

theorem tailTrace_8315120 : CollatzResearch.WordTrace tailWord_8315120 prefixEnd_8315120 1423217753271204096153155 := by
  unfold tailWord_8315120
  simp only [CollatzResearch.WordTrace]
  refine ⟨151638670817873912140211407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202184894423831882853615209 151638670817873912140211407)
  ·
    refine ⟨227458006226810868210317111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151638670817873912140211407 227458006226810868210317111)
    ·
      refine ⟨341187009340216302315475667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227458006226810868210317111 341187009340216302315475667)
      ·
        refine ⟨511780514010324453473213501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341187009340216302315475667 511780514010324453473213501)
        ·
          refine ⟨191917692753871670052455063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511780514010324453473213501 191917692753871670052455063)
          ·
            refine ⟨287876539130807505078682595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191917692753871670052455063 287876539130807505078682595)
            ·
              refine ⟨431814808696211257618023893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287876539130807505078682595 431814808696211257618023893)
              ·
                refine ⟨10120659578817451350422435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431814808696211257618023893 10120659578817451350422435)
                ·
                  refine ⟨15180989368226177025633653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10120659578817451350422435 15180989368226177025633653)
                  ·
                    refine ⟨1423217753271204096153155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15180989368226177025633653 1423217753271204096153155)
                    ·
                      rfl

theorem cell23_8315120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_8315120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315120 prefixEnd_8315120 := by exact prefixLift 8315120
  have htrace : WordTrace (prefixWord ++ tailWord_8315120) baseStart_8315120 baseEnd_8315120 := by
    simpa [prefixWord, tailWord_8315120, baseEnd_8315120] using wordTrace_append hprefix tailTrace_8315120
  have hstable : (prefixWord ++ tailWord_8315120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315120).length < 2 ^ (prefixWord ++ tailWord_8315120).sum := by decide
  have hdescent : baseEnd_8315120 < baseStart_8315120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315134 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_8315134 : Nat := 118140960795 + 8315134 * 2 ^ 59
def prefixEnd_8315134 : Nat := 4983230072969 + 3 ^ 40 * 8315134 * 2
def baseEnd_8315134 : Nat := 4269660448542775233684401

theorem tailTrace_8315134 : CollatzResearch.WordTrace tailWord_8315134 prefixEnd_8315134 4269660448542775233684401 := by
  unfold tailWord_8315134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37909731532212138083929057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202185234838464736447621637 37909731532212138083929057)
  ·
    refine ⟨28432298649159103562946793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37909731532212138083929057 28432298649159103562946793)
    ·
      refine ⟨21324223986869327672210095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28432298649159103562946793 21324223986869327672210095)
      ·
        refine ⟨31986335980303991508315143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21324223986869327672210095 31986335980303991508315143)
        ·
          refine ⟨47979503970455987262472715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31986335980303991508315143 47979503970455987262472715)
          ·
            refine ⟨71969255955683980893709073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47979503970455987262472715 71969255955683980893709073)
            ·
              refine ⟨53976941966762985670281805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71969255955683980893709073 53976941966762985670281805)
              ·
                refine ⟨20241353237536119626355677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53976941966762985670281805 20241353237536119626355677)
                ·
                  refine ⟨7590507464076044859883379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20241353237536119626355677 7590507464076044859883379)
                  ·
                    refine ⟨11385761196114067289825069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7590507464076044859883379 11385761196114067289825069)
                    ·
                      refine ⟨4269660448542775233684401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11385761196114067289825069 4269660448542775233684401)
                      ·
                        rfl

theorem cell23_8315134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_8315134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315134 prefixEnd_8315134 := by exact prefixLift 8315134
  have htrace : WordTrace (prefixWord ++ tailWord_8315134) baseStart_8315134 baseEnd_8315134 := by
    simpa [prefixWord, tailWord_8315134, baseEnd_8315134] using wordTrace_append hprefix tailTrace_8315134
  have hstable : (prefixWord ++ tailWord_8315134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315134).length < 2 ^ (prefixWord ++ tailWord_8315134).sum := by decide
  have hdescent : baseEnd_8315134 < baseStart_8315134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315163 : List Nat := [1, 1, 1, 1, 1, 1, 6, 11]
def baseStart_8315163 : Nat := 118140960795 + 8315163 * 2 ^ 59
def prefixEnd_8315163 : Nat := 4983230072969 + 3 ^ 40 * 8315163 * 2
def baseEnd_8315163 : Nat := 158136123684509467415621

theorem tailTrace_8315163 : CollatzResearch.WordTrace tailWord_8315163 prefixEnd_8315163 158136123684509467415621 := by
  unfold tailWord_8315163
  simp only [CollatzResearch.WordTrace]
  refine ⟨303278909974592042624238143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202185939983061361749492095 303278909974592042624238143)
  ·
    refine ⟨454918364961888063936357215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303278909974592042624238143 454918364961888063936357215)
    ·
      refine ⟨682377547442832095904535823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454918364961888063936357215 682377547442832095904535823)
      ·
        refine ⟨1023566321164248143856803735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682377547442832095904535823 1023566321164248143856803735)
        ·
          refine ⟨1535349481746372215785205603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023566321164248143856803735 1535349481746372215785205603)
          ·
            refine ⟨2303024222619558323677808405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535349481746372215785205603 2303024222619558323677808405)
            ·
              refine ⟨107954260435291796422397269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2303024222619558323677808405 107954260435291796422397269)
              ·
                refine ⟨158136123684509467415621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 107954260435291796422397269 158136123684509467415621)
                ·
                  rfl

theorem cell23_8315163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 11].length) (baseStart_8315163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315163 prefixEnd_8315163 := by exact prefixLift 8315163
  have htrace : WordTrace (prefixWord ++ tailWord_8315163) baseStart_8315163 baseEnd_8315163 := by
    simpa [prefixWord, tailWord_8315163, baseEnd_8315163] using wordTrace_append hprefix tailTrace_8315163
  have hstable : (prefixWord ++ tailWord_8315163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315163).length < 2 ^ (prefixWord ++ tailWord_8315163).sum := by decide
  have hdescent : baseEnd_8315163 < baseStart_8315163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315201 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 1, 6]
def baseStart_8315201 : Nat := 118140960795 + 8315201 * 2 ^ 59
def prefixEnd_8315201 : Nat := 4983230072969 + 3 ^ 40 * 8315201 * 2
def baseEnd_8315201 : Nat := 1423231617248875490515531

theorem tailTrace_8315201 : CollatzResearch.WordTrace tailWord_8315201 prefixEnd_8315201 1423231617248875490515531 := by
  unfold tailWord_8315201
  simp only [CollatzResearch.WordTrace]
  refine ⟨303280295948454375114121457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202186863965636250076080971 303280295948454375114121457)
  ·
    refine ⟨227460221961340781335591093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303280295948454375114121457 227460221961340781335591093)
    ·
      refine ⟨21324395808875698250211665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227460221961340781335591093 21324395808875698250211665)
      ·
        refine ⟨15993296856656773687658749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21324395808875698250211665 15993296856656773687658749)
        ·
          refine ⟨5997486321246290132872031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15993296856656773687658749 5997486321246290132872031)
          ·
            refine ⟨8996229481869435199308047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997486321246290132872031 8996229481869435199308047)
            ·
              refine ⟨13494344222804152798962071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996229481869435199308047 13494344222804152798962071)
              ·
                refine ⟨20241516334206229198443107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13494344222804152798962071 20241516334206229198443107)
                ·
                  refine ⟨30362274501309343797664661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20241516334206229198443107 30362274501309343797664661)
                  ·
                    refine ⟨1423231617248875490515531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30362274501309343797664661 1423231617248875490515531)
                    ·
                      rfl

theorem cell23_8315201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_8315201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315201 prefixEnd_8315201 := by exact prefixLift 8315201
  have htrace : WordTrace (prefixWord ++ tailWord_8315201) baseStart_8315201 baseEnd_8315201 := by
    simpa [prefixWord, tailWord_8315201, baseEnd_8315201] using wordTrace_append hprefix tailTrace_8315201
  have hstable : (prefixWord ++ tailWord_8315201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315201).length < 2 ^ (prefixWord ++ tailWord_8315201).sum := by decide
  have hdescent : baseEnd_8315201 < baseStart_8315201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315204 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_8315204 : Nat := 118140960795 + 8315204 * 2 ^ 59
def prefixEnd_8315204 : Nat := 4983230072969 + 3 ^ 40 * 8315204 * 2
def baseEnd_8315204 : Nat := 4269696392188589959809079

theorem tailTrace_8315204 : CollatzResearch.WordTrace tailWord_8315204 prefixEnd_8315204 4269696392188589959809079 := by
  unfold tailWord_8315204
  simp only [CollatzResearch.WordTrace]
  refine ⟨151640202683721753313240333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202186936911629004417653777 151640202683721753313240333)
  ·
    refine ⟨56865076006395657492465125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151640202683721753313240333 56865076006395657492465125)
    ·
      refine ⟨10662201751199185779837211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56865076006395657492465125 10662201751199185779837211)
      ·
        refine ⟨15993302626798778669755817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662201751199185779837211 15993302626798778669755817)
        ·
          refine ⟨11994976970099084002316863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15993302626798778669755817 11994976970099084002316863)
          ·
            refine ⟨17992465455148626003475295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11994976970099084002316863 17992465455148626003475295)
            ·
              refine ⟨26988698182722939005212943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17992465455148626003475295 26988698182722939005212943)
              ·
                refine ⟨40483047274084408507819415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26988698182722939005212943 40483047274084408507819415)
                ·
                  refine ⟨60724570911126612761729123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40483047274084408507819415 60724570911126612761729123)
                  ·
                    refine ⟨91086856366689919142593685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60724570911126612761729123 91086856366689919142593685)
                    ·
                      refine ⟨4269696392188589959809079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91086856366689919142593685 4269696392188589959809079)
                      ·
                        rfl

theorem cell23_8315204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_8315204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315204 prefixEnd_8315204 := by exact prefixLift 8315204
  have htrace : WordTrace (prefixWord ++ tailWord_8315204) baseStart_8315204 baseEnd_8315204 := by
    simpa [prefixWord, tailWord_8315204, baseEnd_8315204] using wordTrace_append hprefix tailTrace_8315204
  have hstable : (prefixWord ++ tailWord_8315204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315204).length < 2 ^ (prefixWord ++ tailWord_8315204).sum := by decide
  have hdescent : baseEnd_8315204 < baseStart_8315204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315247 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 5, 4, 2]
def baseStart_8315247 : Nat := 118140960795 + 8315247 * 2 ^ 59
def prefixEnd_8315247 : Nat := 4983230072969 + 3 ^ 40 * 8315247 * 2
def baseEnd_8315247 : Nat := 4269718471856733291571381

theorem tailTrace_8315247 : CollatzResearch.WordTrace tailWord_8315247 prefixEnd_8315247 4269718471856733291571381 := by
  unfold tailWord_8315247
  simp only [CollatzResearch.WordTrace]
  refine ⟨303281973706287724970295995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202187982470858483313530663 303281973706287724970295995)
  ·
    refine ⟨454922960559431587455443993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303281973706287724970295995 454922960559431587455443993)
    ·
      refine ⟨341192220419573690591582995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454922960559431587455443993 341192220419573690591582995)
      ·
        refine ⟨511788330629360535887374493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341192220419573690591582995 511788330629360535887374493)
        ·
          refine ⟨191920623986010200957765435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511788330629360535887374493 191920623986010200957765435)
          ·
            refine ⟨287880935979015301436648153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191920623986010200957765435 287880935979015301436648153)
            ·
              refine ⟨215910701984261476077486115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287880935979015301436648153 215910701984261476077486115)
              ·
                refine ⟨323866052976392214116229173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215910701984261476077486115 323866052976392214116229173)
                ·
                  refine ⟨30362442466536770073396485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323866052976392214116229173 30362442466536770073396485)
                  ·
                    refine ⟨5692957962475644388761841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30362442466536770073396485 5692957962475644388761841)
                    ·
                      refine ⟨4269718471856733291571381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692957962475644388761841 4269718471856733291571381)
                      ·
                        rfl

theorem cell23_8315247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4, 2].length) (baseStart_8315247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315247 prefixEnd_8315247 := by exact prefixLift 8315247
  have htrace : WordTrace (prefixWord ++ tailWord_8315247) baseStart_8315247 baseEnd_8315247 := by
    simpa [prefixWord, tailWord_8315247, baseEnd_8315247] using wordTrace_append hprefix tailTrace_8315247
  have hstable : (prefixWord ++ tailWord_8315247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315247).length < 2 ^ (prefixWord ++ tailWord_8315247).sum := by decide
  have hdescent : baseEnd_8315247 < baseStart_8315247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315298 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_8315298 : Nat := 118140960795 + 8315298 * 2 ^ 59
def prefixEnd_8315298 : Nat := 4983230072969 + 3 ^ 40 * 8315298 * 2
def baseEnd_8315298 : Nat := 4269744659370112592033647

theorem tailTrace_8315298 : CollatzResearch.WordTrace tailWord_8315298 prefixEnd_8315298 4269744659370112592033647 := by
  unfold tailWord_8315298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75820958457275740170100637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202189222552735307120268365 75820958457275740170100637)
  ·
    refine ⟨28432859421478402563787739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75820958457275740170100637 28432859421478402563787739)
    ·
      refine ⟨42649289132217603845681609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28432859421478402563787739 42649289132217603845681609)
      ·
        refine ⟨31986966849163202884261207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42649289132217603845681609 31986966849163202884261207)
        ·
          refine ⟨47980450273744804326391811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31986966849163202884261207 47980450273744804326391811)
          ·
            refine ⟨71970675410617206489587717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47980450273744804326391811 71970675410617206489587717)
            ·
              refine ⟨13494501639490726216797697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71970675410617206489587717 13494501639490726216797697)
              ·
                refine ⟨10120876229618044662598273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13494501639490726216797697 10120876229618044662598273)
                ·
                  refine ⟨7590657172213533496948705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10120876229618044662598273 7590657172213533496948705)
                  ·
                    refine ⟨5692992879160150122711529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7590657172213533496948705 5692992879160150122711529)
                    ·
                      refine ⟨4269744659370112592033647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5692992879160150122711529 4269744659370112592033647)
                      ·
                        rfl

theorem cell23_8315298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_8315298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315298 prefixEnd_8315298 := by exact prefixLift 8315298
  have htrace : WordTrace (prefixWord ++ tailWord_8315298) baseStart_8315298 baseEnd_8315298 := by
    simpa [prefixWord, tailWord_8315298, baseEnd_8315298] using wordTrace_append hprefix tailTrace_8315298
  have hstable : (prefixWord ++ tailWord_8315298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315298).length < 2 ^ (prefixWord ++ tailWord_8315298).sum := by decide
  have hdescent : baseEnd_8315298 < baseStart_8315298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315354 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2]
def baseStart_8315354 : Nat := 118140960795 + 8315354 * 2 ^ 59
def prefixEnd_8315354 : Nat := 4983230072969 + 3 ^ 40 * 8315354 * 2
def baseEnd_8315354 : Nat := 4269773414286764372933389

theorem tailTrace_8315354 : CollatzResearch.WordTrace tailWord_8315354 prefixEnd_8315354 4269773414286764372933389 := by
  unfold tailWord_8315354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75821469079225020561110279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202190584211266721496294077 75821469079225020561110279)
  ·
    refine ⟨113732203618837530841665419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75821469079225020561110279 113732203618837530841665419)
    ·
      refine ⟨170598305428256296262498129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113732203618837530841665419 170598305428256296262498129)
      ·
        refine ⟨127948729071192222196873597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170598305428256296262498129 127948729071192222196873597)
        ·
          refine ⟨47980773401697083323827599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127948729071192222196873597 47980773401697083323827599)
          ·
            refine ⟨71971160102545624985741399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47980773401697083323827599 71971160102545624985741399)
            ·
              refine ⟨107956740153818437478612099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71971160102545624985741399 107956740153818437478612099)
              ·
                refine ⟨161935110230727656217918149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107956740153818437478612099 161935110230727656217918149)
                ·
                  refine ⟨30362833168261435540859653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161935110230727656217918149 30362833168261435540859653)
                  ·
                    refine ⟨5693031219049019163911185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30362833168261435540859653 5693031219049019163911185)
                    ·
                      refine ⟨4269773414286764372933389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693031219049019163911185 4269773414286764372933389)
                      ·
                        rfl

theorem cell23_8315354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_8315354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315354 prefixEnd_8315354 := by exact prefixLift 8315354
  have htrace : WordTrace (prefixWord ++ tailWord_8315354) baseStart_8315354 baseEnd_8315354 := by
    simpa [prefixWord, tailWord_8315354, baseEnd_8315354] using wordTrace_append hprefix tailTrace_8315354
  have hstable : (prefixWord ++ tailWord_8315354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315354).length < 2 ^ (prefixWord ++ tailWord_8315354).sum := by decide
  have hdescent : baseEnd_8315354 < baseStart_8315354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315367 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_8315367 : Nat := 118140960795 + 8315367 * 2 ^ 59
def prefixEnd_8315367 : Nat := 4983230072969 + 3 ^ 40 * 8315367 * 2
def baseEnd_8315367 : Nat := 4269780089535272822070829

theorem tailTrace_8315367 : CollatzResearch.WordTrace tailWord_8315367 prefixEnd_8315367 4269780089535272822070829 := by
  unfold tailWord_8315367
  simp only [CollatzResearch.WordTrace]
  refine ⟨303286350465852985464664355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202190900310568656976442903 303286350465852985464664355)
  ·
    refine ⟨454929525698779478196996533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303286350465852985464664355 454929525698779478196996533)
    ·
      refine ⟨42649643034260576080968425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454929525698779478196996533 42649643034260576080968425)
      ·
        refine ⟨31987232275695432060726319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42649643034260576080968425 31987232275695432060726319)
        ·
          refine ⟨47980848413543148091089479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31987232275695432060726319 47980848413543148091089479)
          ·
            refine ⟨71971272620314722136634219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47980848413543148091089479 71971272620314722136634219)
            ·
              refine ⟨107956908930472083204951329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71971272620314722136634219 107956908930472083204951329)
              ·
                refine ⟨80967681697854062403713497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107956908930472083204951329 80967681697854062403713497)
                ·
                  refine ⟨60725761273390546802785123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80967681697854062403713497 60725761273390546802785123)
                  ·
                    refine ⟨91088641910085820204177685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60725761273390546802785123 91088641910085820204177685)
                    ·
                      refine ⟨4269780089535272822070829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91088641910085820204177685 4269780089535272822070829)
                      ·
                        rfl

theorem cell23_8315367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_8315367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315367 prefixEnd_8315367 := by exact prefixLift 8315367
  have htrace : WordTrace (prefixWord ++ tailWord_8315367) baseStart_8315367 baseEnd_8315367 := by
    simpa [prefixWord, tailWord_8315367, baseEnd_8315367] using wordTrace_append hprefix tailTrace_8315367
  have hstable : (prefixWord ++ tailWord_8315367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315367).length < 2 ^ (prefixWord ++ tailWord_8315367).sum := by decide
  have hdescent : baseEnd_8315367 < baseStart_8315367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315374 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_8315374 : Nat := 118140960795 + 8315374 * 2 ^ 59
def prefixEnd_8315374 : Nat := 4983230072969 + 3 ^ 40 * 8315374 * 2
def baseEnd_8315374 : Nat := 4269783683899854294683297

theorem tailTrace_8315374 : CollatzResearch.WordTrace tailWord_8315374 prefixEnd_8315374 4269783683899854294683297 := by
  unfold tailWord_8315374
  simp only [CollatzResearch.WordTrace]
  refine ⟨37910825722103453207521147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202191070517885083773446117 37910825722103453207521147)
  ·
    refine ⟨56866238583155179811281721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37910825722103453207521147 56866238583155179811281721)
    ·
      refine ⟨42649678937366384858461291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56866238583155179811281721 42649678937366384858461291)
      ·
        refine ⟨63974518406049577287691937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42649678937366384858461291 63974518406049577287691937)
        ·
          refine ⟨47980888804537182965768953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63974518406049577287691937 47980888804537182965768953)
          ·
            refine ⟨35985666603402887224326715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47980888804537182965768953 35985666603402887224326715)
            ·
              refine ⟨53978499905104330836490073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35985666603402887224326715 53978499905104330836490073)
              ·
                refine ⟨40483874928828248127367555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53978499905104330836490073 40483874928828248127367555)
                ·
                  refine ⟨60725812393242372191051333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40483874928828248127367555 60725812393242372191051333)
                  ·
                    refine ⟨11386089823732944785822125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60725812393242372191051333 11386089823732944785822125)
                    ·
                      refine ⟨4269783683899854294683297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11386089823732944785822125 4269783683899854294683297)
                      ·
                        rfl

theorem cell23_8315374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_8315374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315374 prefixEnd_8315374 := by exact prefixLift 8315374
  have htrace : WordTrace (prefixWord ++ tailWord_8315374) baseStart_8315374 baseEnd_8315374 := by
    simpa [prefixWord, tailWord_8315374, baseEnd_8315374] using wordTrace_append hprefix tailTrace_8315374
  have hstable : (prefixWord ++ tailWord_8315374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315374).length < 2 ^ (prefixWord ++ tailWord_8315374).sum := by decide
  have hdescent : baseEnd_8315374 < baseStart_8315374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315415 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 3, 4]
def baseStart_8315415 : Nat := 118140960795 + 8315415 * 2 ^ 59
def prefixEnd_8315415 : Nat := 4983230072969 + 3 ^ 40 * 8315415 * 2
def baseEnd_8315415 : Nat := 1423268245535562878090203

theorem tailTrace_8315415 : CollatzResearch.WordTrace tailWord_8315415 prefixEnd_8315415 1423268245535562878090203 := by
  unfold tailWord_8315415
  simp only [CollatzResearch.WordTrace]
  refine ⟨303288101169679089662411699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202192067446452726441607799 303288101169679089662411699)
  ·
    refine ⟨454932151754518634493617549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303288101169679089662411699 454932151754518634493617549)
    ·
      refine ⟨170599556907944487935106581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454932151754518634493617549 170599556907944487935106581)
      ·
        refine ⟨7996854230059897871958121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170599556907944487935106581 7996854230059897871958121)
        ·
          refine ⟨5997640672544923403968591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7996854230059897871958121 5997640672544923403968591)
          ·
            refine ⟨8996461008817385105952887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997640672544923403968591 8996461008817385105952887)
            ·
              refine ⟨13494691513226077658929331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996461008817385105952887 13494691513226077658929331)
              ·
                refine ⟨20242037269839116488393997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13494691513226077658929331 20242037269839116488393997)
                ·
                  refine ⟨7590763976189668683147749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20242037269839116488393997 7590763976189668683147749)
                  ·
                    refine ⟨1423268245535562878090203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590763976189668683147749 1423268245535562878090203)
                    ·
                      rfl

theorem cell23_8315415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_8315415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315415 prefixEnd_8315415 := by exact prefixLift 8315415
  have htrace : WordTrace (prefixWord ++ tailWord_8315415) baseStart_8315415 baseEnd_8315415 := by
    simpa [prefixWord, tailWord_8315415, baseEnd_8315415] using wordTrace_append hprefix tailTrace_8315415
  have hstable : (prefixWord ++ tailWord_8315415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315415).length < 2 ^ (prefixWord ++ tailWord_8315415).sum := by decide
  have hdescent : baseEnd_8315415 < baseStart_8315415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315474 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_8315474 : Nat := 118140960795 + 8315474 * 2 ^ 59
def prefixEnd_8315474 : Nat := 4983230072969 + 3 ^ 40 * 8315474 * 2
def baseEnd_8315474 : Nat := 4269835031965303903432837

theorem tailTrace_8315474 : CollatzResearch.WordTrace tailWord_8315474 prefixEnd_8315474 4269835031965303903432837 := by
  unfold tailWord_8315474
  simp only [CollatzResearch.WordTrace]
  refine ⟨75822563269116335684702369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202193502050976895159206317 75822563269116335684702369)
  ·
    refine ⟨56866922451837251763526777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75822563269116335684702369 56866922451837251763526777)
    ·
      refine ⟨42650191838877938822645083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56866922451837251763526777 42650191838877938822645083)
      ·
        refine ⟨63975287758316908233967625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42650191838877938822645083 63975287758316908233967625)
        ·
          refine ⟨47981465818737681175475719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63975287758316908233967625 47981465818737681175475719)
          ·
            refine ⟨71972198728106521763213579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47981465818737681175475719 71972198728106521763213579)
            ·
              refine ⟨107958298092159782644820369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71972198728106521763213579 107958298092159782644820369)
              ·
                refine ⟨80968723569119836983615277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107958298092159782644820369 80968723569119836983615277)
                ·
                  refine ⟨30363271338419938868855729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80968723569119836983615277 30363271338419938868855729)
                  ·
                    refine ⟨22772453503814954151641797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30363271338419938868855729 22772453503814954151641797)
                    ·
                      refine ⟨4269835031965303903432837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22772453503814954151641797 4269835031965303903432837)
                      ·
                        rfl

theorem cell23_8315474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_8315474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315474 prefixEnd_8315474 := by exact prefixLift 8315474
  have htrace : WordTrace (prefixWord ++ tailWord_8315474) baseStart_8315474 baseEnd_8315474 := by
    simpa [prefixWord, tailWord_8315474, baseEnd_8315474] using wordTrace_append hprefix tailTrace_8315474
  have hstable : (prefixWord ++ tailWord_8315474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315474).length < 2 ^ (prefixWord ++ tailWord_8315474).sum := by decide
  have hdescent : baseEnd_8315474 < baseStart_8315474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315487 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_8315487 : Nat := 118140960795 + 8315487 * 2 ^ 59
def prefixEnd_8315487 : Nat := 4983230072969 + 3 ^ 40 * 8315487 * 2
def baseEnd_8315487 : Nat := 4269841707213812352570277

theorem tailTrace_8315487 : CollatzResearch.WordTrace tailWord_8315487 prefixEnd_8315487 4269841707213812352570277 := by
  unfold tailWord_8315487
  simp only [CollatzResearch.WordTrace]
  refine ⟨303290727225418245959032715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202193818150278830639355143 303290727225418245959032715)
  ·
    refine ⟨454936090838127368938549073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303290727225418245959032715 454936090838127368938549073)
    ·
      refine ⟨341202068128595526703911805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454936090838127368938549073 341202068128595526703911805)
      ·
        refine ⟨127950775548223322513966927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341202068128595526703911805 127950775548223322513966927)
        ·
          refine ⟨191926163322334983770950391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127950775548223322513966927 191926163322334983770950391)
          ·
            refine ⟨287889244983502475656425587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191926163322334983770950391 287889244983502475656425587)
            ·
              refine ⟨431833867475253713484638381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287889244983502475656425587 431833867475253713484638381)
              ·
                refine ⟨161937700303220142556739393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431833867475253713484638381 161937700303220142556739393)
                ·
                  refine ⟨121453275227415106917554545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161937700303220142556739393 121453275227415106917554545)
                  ·
                    refine ⟨91089956420561330188165909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121453275227415106917554545 91089956420561330188165909)
                    ·
                      refine ⟨4269841707213812352570277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91089956420561330188165909 4269841707213812352570277)
                      ·
                        rfl

theorem cell23_8315487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_8315487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315487 prefixEnd_8315487 := by exact prefixLift 8315487
  have htrace : WordTrace (prefixWord ++ tailWord_8315487) baseStart_8315487 baseEnd_8315487 := by
    simpa [prefixWord, tailWord_8315487, baseEnd_8315487] using wordTrace_append hprefix tailTrace_8315487
  have hstable : (prefixWord ++ tailWord_8315487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315487).length < 2 ^ (prefixWord ++ tailWord_8315487).sum := by decide
  have hdescent : baseEnd_8315487 < baseStart_8315487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315497 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_8315497 : Nat := 118140960795 + 8315497 * 2 ^ 59
def prefixEnd_8315497 : Nat := 4983230072969 + 3 ^ 40 * 8315497 * 2
def baseEnd_8315497 : Nat := 1423282280673452437815077

theorem tailTrace_8315497 : CollatzResearch.WordTrace tailWord_8315497 prefixEnd_8315497 1423282280673452437815077 := by
  unfold tailWord_8315497
  simp only [CollatzResearch.WordTrace]
  refine ⟨303291091955382017666896745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202194061303588011777931163 303291091955382017666896745)
  ·
    refine ⟨227468318966536513250172559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303291091955382017666896745 227468318966536513250172559)
    ·
      refine ⟨341202478449804769875258839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227468318966536513250172559 341202478449804769875258839)
      ·
        refine ⟨511803717674707154812888259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341202478449804769875258839 511803717674707154812888259)
        ·
          refine ⟨767705576512060732219332389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511803717674707154812888259 767705576512060732219332389)
          ·
            refine ⟨143944795596011387291124823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 767705576512060732219332389 143944795596011387291124823)
            ·
              refine ⟨215917193394017080936687235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143944795596011387291124823 215917193394017080936687235)
              ·
                refine ⟨323875790091025621405030853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215917193394017080936687235 323875790091025621405030853)
                ·
                  refine ⟨60726710642067304013443285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323875790091025621405030853 60726710642067304013443285)
                  ·
                    refine ⟨1423282280673452437815077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60726710642067304013443285 1423282280673452437815077)
                    ·
                      rfl

theorem cell23_8315497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_8315497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315497 prefixEnd_8315497 := by exact prefixLift 8315497
  have htrace : WordTrace (prefixWord ++ tailWord_8315497) baseStart_8315497 baseEnd_8315497 := by
    simpa [prefixWord, tailWord_8315497, baseEnd_8315497] using wordTrace_append hprefix tailTrace_8315497
  have hstable : (prefixWord ++ tailWord_8315497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315497).length < 2 ^ (prefixWord ++ tailWord_8315497).sum := by decide
  have hdescent : baseEnd_8315497 < baseStart_8315497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315501 : List Nat := [1, 5, 1, 1, 3, 2, 3, 7]
def baseStart_8315501 : Nat := 118140960795 + 8315501 * 2 ^ 59
def prefixEnd_8315501 : Nat := 4983230072969 + 3 ^ 40 * 8315501 * 2
def baseEnd_8315501 : Nat := 158142551701591677696119

theorem tailTrace_8315501 : CollatzResearch.WordTrace tailWord_8315501 prefixEnd_8315501 158142551701591677696119 := by
  unfold tailWord_8315501
  simp only [CollatzResearch.WordTrace]
  refine ⟨303291237847367526350042357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202194158564911684233361571 303291237847367526350042357)
  ·
    refine ⟨28433553548190705595316471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303291237847367526350042357 28433553548190705595316471)
    ·
      refine ⟨42650330322286058392974707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28433553548190705595316471 42650330322286058392974707)
      ·
        refine ⟨63975495483429087589462061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42650330322286058392974707 63975495483429087589462061)
        ·
          refine ⟨23990810806285907846048273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63975495483429087589462061 23990810806285907846048273)
          ·
            refine ⟨17993108104714430884536205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23990810806285907846048273 17993108104714430884536205)
            ·
              refine ⟨6747415539267911581701077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17993108104714430884536205 6747415539267911581701077)
              ·
                refine ⟨158142551701591677696119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6747415539267911581701077 158142551701591677696119)
                ·
                  rfl

theorem cell23_8315501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 7].length) (baseStart_8315501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315501 prefixEnd_8315501 := by exact prefixLift 8315501
  have htrace : WordTrace (prefixWord ++ tailWord_8315501) baseStart_8315501 baseEnd_8315501 := by
    simpa [prefixWord, tailWord_8315501, baseEnd_8315501] using wordTrace_append hprefix tailTrace_8315501
  have hstable : (prefixWord ++ tailWord_8315501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315501).length < 2 ^ (prefixWord ++ tailWord_8315501).sum := by decide
  have hdescent : baseEnd_8315501 < baseStart_8315501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315522 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_8315522 : Nat := 118140960795 + 8315522 * 2 ^ 59
def prefixEnd_8315522 : Nat := 4983230072969 + 3 ^ 40 * 8315522 * 2
def baseEnd_8315522 : Nat := 1423286559678906571877539

theorem tailTrace_8315522 : CollatzResearch.WordTrace tailWord_8315522 prefixEnd_8315522 1423286559678906571877539 := by
  unfold tailWord_8315522
  simp only [CollatzResearch.WordTrace]
  refine ⟨75823000945072861734139205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202194669186860964624371213 75823000945072861734139205)
  ·
    refine ⟨14216812677201161575151101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75823000945072861734139205 14216812677201161575151101)
    ·
      refine ⟨5331304753950435590681663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14216812677201161575151101 5331304753950435590681663)
      ·
        refine ⟨7996957130925653386022495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331304753950435590681663 7996957130925653386022495)
        ·
          refine ⟨11995435696388480079033743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996957130925653386022495 11995435696388480079033743)
          ·
            refine ⟨17993153544582720118550615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995435696388480079033743 17993153544582720118550615)
            ·
              refine ⟨26989730316874080177825923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17993153544582720118550615 26989730316874080177825923)
              ·
                refine ⟨40484595475311120266738885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26989730316874080177825923 40484595475311120266738885)
                ·
                  refine ⟨7590861651620835050013541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40484595475311120266738885 7590861651620835050013541)
                  ·
                    refine ⟨1423286559678906571877539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590861651620835050013541 1423286559678906571877539)
                    ·
                      rfl

theorem cell23_8315522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_8315522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315522 prefixEnd_8315522 := by exact prefixLift 8315522
  have htrace : WordTrace (prefixWord ++ tailWord_8315522) baseStart_8315522 baseEnd_8315522 := by
    simpa [prefixWord, tailWord_8315522, baseEnd_8315522] using wordTrace_append hprefix tailTrace_8315522
  have hstable : (prefixWord ++ tailWord_8315522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315522).length < 2 ^ (prefixWord ++ tailWord_8315522).sum := by decide
  have hdescent : baseEnd_8315522 < baseStart_8315522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315544 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_8315544 : Nat := 118140960795 + 8315544 * 2 ^ 59
def prefixEnd_8315544 : Nat := 4983230072969 + 3 ^ 40 * 8315544 * 2
def baseEnd_8315544 : Nat := 1423290325203706209852505

theorem tailTrace_8315544 : CollatzResearch.WordTrace tailWord_8315544 prefixEnd_8315544 1423290325203706209852505 := by
  unfold tailWord_8315544
  simp only [CollatzResearch.WordTrace]
  refine ⟨151646403093105872346928843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202195204124141163129238457 151646403093105872346928843)
  ·
    refine ⟨227469604639658808520393265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151646403093105872346928843 227469604639658808520393265)
    ·
      refine ⟨170602203479744106390294949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227469604639658808520393265 170602203479744106390294949)
      ·
        refine ⟨31987913152452019948180303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170602203479744106390294949 31987913152452019948180303)
        ·
          refine ⟨47981869728678029922270455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31987913152452019948180303 47981869728678029922270455)
          ·
            refine ⟨71972804593017044883405683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47981869728678029922270455 71972804593017044883405683)
            ·
              refine ⟨107959206889525567325108525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71972804593017044883405683 107959206889525567325108525)
              ·
                refine ⟨40484702583572087746915697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107959206889525567325108525 40484702583572087746915697)
                ·
                  refine ⟨30363526937679065810186773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40484702583572087746915697 30363526937679065810186773)
                  ·
                    refine ⟨1423290325203706209852505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30363526937679065810186773 1423290325203706209852505)
                    ·
                      rfl

theorem cell23_8315544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_8315544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315544 prefixEnd_8315544 := by exact prefixLift 8315544
  have htrace : WordTrace (prefixWord ++ tailWord_8315544) baseStart_8315544 baseEnd_8315544 := by
    simpa [prefixWord, tailWord_8315544, baseEnd_8315544] using wordTrace_append hprefix tailTrace_8315544
  have hstable : (prefixWord ++ tailWord_8315544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315544).length < 2 ^ (prefixWord ++ tailWord_8315544).sum := by decide
  have hdescent : baseEnd_8315544 < baseStart_8315544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315602 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_8315602 : Nat := 118140960795 + 8315602 * 2 ^ 59
def prefixEnd_8315602 : Nat := 4983230072969 + 3 ^ 40 * 8315602 * 2
def baseEnd_8315602 : Nat := 4269900757489079402632249

theorem tailTrace_8315602 : CollatzResearch.WordTrace tailWord_8315602 prefixEnd_8315602 4269900757489079402632249 := by
  unfold tailWord_8315602
  simp only [CollatzResearch.WordTrace]
  refine ⟨75823730405000405149867265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202196614413334413732979373 75823730405000405149867265)
  ·
    refine ⟨56867797803750303862400449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75823730405000405149867265 56867797803750303862400449)
    ·
      refine ⟨42650848352812727896800337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56867797803750303862400449 42650848352812727896800337)
      ·
        refine ⟨31988136264609545922600253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42650848352812727896800337 31988136264609545922600253)
        ·
          refine ⟨11995551099228579720975095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31988136264609545922600253 11995551099228579720975095)
          ·
            refine ⟨17993326648842869581462643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995551099228579720975095 17993326648842869581462643)
            ·
              refine ⟨26989989973264304372193965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17993326648842869581462643 26989989973264304372193965)
              ·
                refine ⟨10121246239974114139572737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26989989973264304372193965 10121246239974114139572737)
                ·
                  refine ⟨7590934679980585604679553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10121246239974114139572737 7590934679980585604679553)
                  ·
                    refine ⟨5693201009985439203509665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7590934679980585604679553 5693201009985439203509665)
                    ·
                      refine ⟨4269900757489079402632249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693201009985439203509665 4269900757489079402632249)
                      ·
                        rfl

theorem cell23_8315602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_8315602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315602 prefixEnd_8315602 := by exact prefixLift 8315602
  have htrace : WordTrace (prefixWord ++ tailWord_8315602) baseStart_8315602 baseEnd_8315602 := by
    simpa [prefixWord, tailWord_8315602, baseEnd_8315602] using wordTrace_append hprefix tailTrace_8315602
  have hstable : (prefixWord ++ tailWord_8315602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315602).length < 2 ^ (prefixWord ++ tailWord_8315602).sum := by decide
  have hdescent : baseEnd_8315602 < baseStart_8315602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315621 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_8315621 : Nat := 118140960795 + 8315621 * 2 ^ 59
def prefixEnd_8315621 : Nat := 4983230072969 + 3 ^ 40 * 8315621 * 2
def baseEnd_8315621 : Nat := 1423303504540504942764887

theorem tailTrace_8315621 : CollatzResearch.WordTrace tailWord_8315621 prefixEnd_8315621 1423303504540504942764887 := by
  unfold tailWord_8315621
  simp only [CollatzResearch.WordTrace]
  refine ⟨303295614606932786844410717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202197076404621857896273811 303295614606932786844410717)
  ·
    refine ⟨113735855477599795066654019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303295614606932786844410717 113735855477599795066654019)
    ·
      refine ⟨170603783216399692599981029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113735855477599795066654019 170603783216399692599981029)
      ·
        refine ⟨31988209353074942362496443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170603783216399692599981029 31988209353074942362496443)
        ·
          refine ⟨47982314029612413543744665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31988209353074942362496443 47982314029612413543744665)
          ·
            refine ⟨35986735522209310157808499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47982314029612413543744665 35986735522209310157808499)
            ·
              refine ⟨53980103283313965236712749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35986735522209310157808499 53980103283313965236712749)
              ·
                refine ⟨20242538731242736963767281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53980103283313965236712749 20242538731242736963767281)
                ·
                  refine ⟨15181904048432052722825461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20242538731242736963767281 15181904048432052722825461)
                  ·
                    refine ⟨1423303504540504942764887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15181904048432052722825461 1423303504540504942764887)
                    ·
                      rfl

theorem cell23_8315621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_8315621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315621 prefixEnd_8315621 := by exact prefixLift 8315621
  have htrace : WordTrace (prefixWord ++ tailWord_8315621) baseStart_8315621 baseEnd_8315621 := by
    simpa [prefixWord, tailWord_8315621, baseEnd_8315621] using wordTrace_append hprefix tailTrace_8315621
  have hstable : (prefixWord ++ tailWord_8315621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315621).length < 2 ^ (prefixWord ++ tailWord_8315621).sum := by decide
  have hdescent : baseEnd_8315621 < baseStart_8315621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315636 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8315636 : Nat := 118140960795 + 8315636 * 2 ^ 59
def prefixEnd_8315636 : Nat := 4983230072969 + 3 ^ 40 * 8315636 * 2
def baseEnd_8315636 : Nat := 4269918215831332269607093

theorem tailTrace_8315636 : CollatzResearch.WordTrace tailWord_8315636 prefixEnd_8315636 4269918215831332269607093 := by
  unfold tailWord_8315636
  simp only [CollatzResearch.WordTrace]
  refine ⟨151648080850939222203103381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202197441134585629604137841 151648080850939222203103381)
  ·
    refine ⟨7108503789887776040770471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151648080850939222203103381 7108503789887776040770471)
    ·
      refine ⟨10662755684831664061155707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7108503789887776040770471 10662755684831664061155707)
      ·
        refine ⟨15994133527247496091733561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662755684831664061155707 15994133527247496091733561)
        ·
          refine ⟨11995600145435622068800171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15994133527247496091733561 11995600145435622068800171)
          ·
            refine ⟨17993400218153433103200257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995600145435622068800171 17993400218153433103200257)
            ·
              refine ⟨13495050163615074827400193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17993400218153433103200257 13495050163615074827400193)
              ·
                refine ⟨10121287622711306120550145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13495050163615074827400193 10121287622711306120550145)
                ·
                  refine ⟨7590965717033479590412609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10121287622711306120550145 7590965717033479590412609)
                  ·
                    refine ⟨5693224287775109692809457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7590965717033479590412609 5693224287775109692809457)
                    ·
                      refine ⟨4269918215831332269607093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693224287775109692809457 4269918215831332269607093)
                      ·
                        rfl

theorem cell23_8315636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8315636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315636 prefixEnd_8315636 := by exact prefixLift 8315636
  have htrace : WordTrace (prefixWord ++ tailWord_8315636) baseStart_8315636 baseEnd_8315636 := by
    simpa [prefixWord, tailWord_8315636, baseEnd_8315636] using wordTrace_append hprefix tailTrace_8315636
  have hstable : (prefixWord ++ tailWord_8315636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315636).length < 2 ^ (prefixWord ++ tailWord_8315636).sum := by decide
  have hdescent : baseEnd_8315636 < baseStart_8315636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315641 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 6, 2]
def baseStart_8315641 : Nat := 118140960795 + 8315641 * 2 ^ 59
def prefixEnd_8315641 : Nat := 4983230072969 + 3 ^ 40 * 8315641 * 2
def baseEnd_8315641 : Nat := 4269920783234604750044569

theorem tailTrace_8315641 : CollatzResearch.WordTrace tailWord_8315641 prefixEnd_8315641 4269920783234604750044569 := by
  unfold tailWord_8315641
  simp only [CollatzResearch.WordTrace]
  refine ⟨303296344066860330260138777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202197562711240220173425851 303296344066860330260138777)
  ·
    refine ⟨227472258050145247695104083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303296344066860330260138777 227472258050145247695104083)
    ·
      refine ⟨341208387075217871542656125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227472258050145247695104083 341208387075217871542656125)
      ·
        refine ⟨127953145153206701828496047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341208387075217871542656125 127953145153206701828496047)
        ·
          refine ⟨191929717729810052742744071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127953145153206701828496047 191929717729810052742744071)
          ·
            refine ⟨287894576594715079114116107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191929717729810052742744071 287894576594715079114116107)
            ·
              refine ⟨431841864892072618671174161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287894576594715079114116107 431841864892072618671174161)
              ·
                refine ⟨323881398669054464003380621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431841864892072618671174161 323881398669054464003380621)
                ·
                  refine ⟨121455524500895424001267733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323881398669054464003380621 121455524500895424001267733)
                  ·
                    refine ⟨5693227710979473000059425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121455524500895424001267733 5693227710979473000059425)
                    ·
                      refine ⟨4269920783234604750044569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693227710979473000059425 4269920783234604750044569)
                      ·
                        rfl

theorem cell23_8315641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_8315641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315641 prefixEnd_8315641 := by exact prefixLift 8315641
  have htrace : WordTrace (prefixWord ++ tailWord_8315641) baseStart_8315641 baseEnd_8315641 := by
    simpa [prefixWord, tailWord_8315641, baseEnd_8315641] using wordTrace_append hprefix tailTrace_8315641
  have hstable : (prefixWord ++ tailWord_8315641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315641).length < 2 ^ (prefixWord ++ tailWord_8315641).sum := by decide
  have hdescent : baseEnd_8315641 < baseStart_8315641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315651 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 3, 4]
def baseStart_8315651 : Nat := 118140960795 + 8315651 * 2 ^ 59
def prefixEnd_8315651 : Nat := 4983230072969 + 3 ^ 40 * 8315651 * 2
def baseEnd_8315651 : Nat := 1423308639347049903639841

theorem tailTrace_8315651 : CollatzResearch.WordTrace tailWord_8315651 prefixEnd_8315651 1423308639347049903639841 := by
  unfold tailWord_8315651
  simp only [CollatzResearch.WordTrace]
  refine ⟨303296708796824101968002807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202197805864549401312001871 303296708796824101968002807)
  ·
    refine ⟨454945063195236152952004211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303296708796824101968002807 454945063195236152952004211)
    ·
      refine ⟨682417594792854229428006317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454945063195236152952004211 682417594792854229428006317)
      ·
        refine ⟨255906598047320336035502369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682417594792854229428006317 255906598047320336035502369)
        ·
          refine ⟨191929948535490252026626777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255906598047320336035502369 191929948535490252026626777)
          ·
            refine ⟨143947461401617689019970083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191929948535490252026626777 143947461401617689019970083)
            ·
              refine ⟨215921192102426533529955125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143947461401617689019970083 215921192102426533529955125)
              ·
                refine ⟨20242611759602487518433293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215921192102426533529955125 20242611759602487518433293)
                ·
                  refine ⟨7590979409850932819412485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20242611759602487518433293 7590979409850932819412485)
                  ·
                    refine ⟨1423308639347049903639841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7590979409850932819412485 1423308639347049903639841)
                    ·
                      rfl

theorem cell23_8315651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 4].length) (baseStart_8315651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315651 prefixEnd_8315651 := by exact prefixLift 8315651
  have htrace : WordTrace (prefixWord ++ tailWord_8315651) baseStart_8315651 baseEnd_8315651 := by
    simpa [prefixWord, tailWord_8315651, baseEnd_8315651] using wordTrace_append hprefix tailTrace_8315651
  have hstable : (prefixWord ++ tailWord_8315651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315651).length < 2 ^ (prefixWord ++ tailWord_8315651).sum := by decide
  have hdescent : baseEnd_8315651 < baseStart_8315651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315658 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_8315658 : Nat := 118140960795 + 8315658 * 2 ^ 59
def prefixEnd_8315658 : Nat := 4983230072969 + 3 ^ 40 * 8315658 * 2
def baseEnd_8315658 : Nat := 4269929512405731183531991

theorem tailTrace_8315658 : CollatzResearch.WordTrace tailWord_8315658 prefixEnd_8315658 4269929512405731183531991 := by
  unfold tailWord_8315658
  simp only [CollatzResearch.WordTrace]
  refine ⟨75824241026949685540876907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202197976071865828109005085 75824241026949685540876907)
  ·
    refine ⟨113736361540424528311315361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75824241026949685540876907 113736361540424528311315361)
    ·
      refine ⟨85302271155318396233486521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113736361540424528311315361 85302271155318396233486521)
      ·
        refine ⟨63976703366488797175114891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85302271155318396233486521 63976703366488797175114891)
        ·
          refine ⟨95965055049733195762672337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63976703366488797175114891 95965055049733195762672337)
          ·
            refine ⟨71973791287299896822004253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95965055049733195762672337 71973791287299896822004253)
            ·
              refine ⟨26990171732737461308251595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71973791287299896822004253 26990171732737461308251595)
              ·
                refine ⟨40485257599106191962377393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26990171732737461308251595 40485257599106191962377393)
                ·
                  refine ⟨30363943199329643971783045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40485257599106191962377393 30363943199329643971783045)
                  ·
                    refine ⟨5693239349874308244709321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30363943199329643971783045 5693239349874308244709321)
                    ·
                      refine ⟨4269929512405731183531991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693239349874308244709321 4269929512405731183531991)
                      ·
                        rfl

theorem cell23_8315658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_8315658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315658 prefixEnd_8315658 := by exact prefixLift 8315658
  have htrace : WordTrace (prefixWord ++ tailWord_8315658) baseStart_8315658 baseEnd_8315658 := by
    simpa [prefixWord, tailWord_8315658, baseEnd_8315658] using wordTrace_append hprefix tailTrace_8315658
  have hstable : (prefixWord ++ tailWord_8315658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315658).length < 2 ^ (prefixWord ++ tailWord_8315658).sum := by decide
  have hdescent : baseEnd_8315658 < baseStart_8315658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315685 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_8315685 : Nat := 118140960795 + 8315685 * 2 ^ 59
def prefixEnd_8315685 : Nat := 4983230072969 + 3 ^ 40 * 8315685 * 2
def baseEnd_8315685 : Nat := 1423314458794467525964789

theorem tailTrace_8315685 : CollatzResearch.WordTrace tailWord_8315685 prefixEnd_8315685 1423314458794467525964789 := by
  unfold tailWord_8315685
  simp only [CollatzResearch.WordTrace]
  refine ⟨303297948878700925774740509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202198632585800617183160339 303297948878700925774740509)
  ·
    refine ⟨113736730829512847165527691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303297948878700925774740509 113736730829512847165527691)
    ·
      refine ⟨170605096244269270748291537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113736730829512847165527691 170605096244269270748291537)
      ·
        refine ⟨127953822183201953061218653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170605096244269270748291537 127953822183201953061218653)
        ·
          refine ⟨47982683318700732397956995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127953822183201953061218653 47982683318700732397956995)
          ·
            refine ⟨71974024978051098596935493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47982683318700732397956995 71974024978051098596935493)
            ·
              refine ⟨13495129683384580986925405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71974024978051098596935493 13495129683384580986925405)
              ·
                refine ⟨5060673631269217870097027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13495129683384580986925405 5060673631269217870097027)
                ·
                  refine ⟨7591010446903826805145541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060673631269217870097027 7591010446903826805145541)
                  ·
                    refine ⟨1423314458794467525964789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7591010446903826805145541 1423314458794467525964789)
                    ·
                      rfl

theorem cell23_8315685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_8315685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315685 prefixEnd_8315685 := by exact prefixLift 8315685
  have htrace : WordTrace (prefixWord ++ tailWord_8315685) baseStart_8315685 baseEnd_8315685 := by
    simpa [prefixWord, tailWord_8315685, baseEnd_8315685] using wordTrace_append hprefix tailTrace_8315685
  have hstable : (prefixWord ++ tailWord_8315685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315685).length < 2 ^ (prefixWord ++ tailWord_8315685).sum := by decide
  have hdescent : baseEnd_8315685 < baseStart_8315685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315701 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_8315701 : Nat := 118140960795 + 8315701 * 2 ^ 59
def prefixEnd_8315701 : Nat := 4983230072969 + 3 ^ 40 * 8315701 * 2
def baseEnd_8315701 : Nat := 4269951592073874515294293

theorem tailTrace_8315701 : CollatzResearch.WordTrace tailWord_8315701 prefixEnd_8315701 4269951592073874515294293 := by
  unfold tailWord_8315701
  simp only [CollatzResearch.WordTrace]
  refine ⟨303298532446642960507322957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202199021631095307004881971 303298532446642960507322957)
  ·
    refine ⟨113736949667491110190246109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303298532446642960507322957 113736949667491110190246109)
    ·
      refine ⟨42651356125309166321342291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113736949667491110190246109 42651356125309166321342291)
      ·
        refine ⟨63977034187963749482013437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42651356125309166321342291 63977034187963749482013437)
        ·
          refine ⟨23991387820486406055755039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63977034187963749482013437 23991387820486406055755039)
          ·
            refine ⟨35987081730729609083632559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23991387820486406055755039 35987081730729609083632559)
            ·
              refine ⟨53980622596094413625448839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35987081730729609083632559 53980622596094413625448839)
              ·
                refine ⟨80970933894141620438173259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53980622596094413625448839 80970933894141620438173259)
                ·
                  refine ⟨121456400841212430657259889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80970933894141620438173259 121456400841212430657259889)
                  ·
                    refine ⟨91092300630909322992944917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121456400841212430657259889 91092300630909322992944917)
                    ·
                      refine ⟨4269951592073874515294293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91092300630909322992944917 4269951592073874515294293)
                      ·
                        rfl

theorem cell23_8315701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_8315701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315701 prefixEnd_8315701 := by exact prefixLift 8315701
  have htrace : WordTrace (prefixWord ++ tailWord_8315701) baseStart_8315701 baseEnd_8315701 := by
    simpa [prefixWord, tailWord_8315701, baseEnd_8315701] using wordTrace_append hprefix tailTrace_8315701
  have hstable : (prefixWord ++ tailWord_8315701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315701).length < 2 ^ (prefixWord ++ tailWord_8315701).sum := by decide
  have hdescent : baseEnd_8315701 < baseStart_8315701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315702 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_8315702 : Nat := 118140960795 + 8315702 * 2 ^ 59
def prefixEnd_8315702 : Nat := 4983230072969 + 3 ^ 40 * 8315702 * 2
def baseEnd_8315702 : Nat := 1423317368518176337127263

theorem tailTrace_8315702 : CollatzResearch.WordTrace tailWord_8315702 prefixEnd_8315702 1423317368518176337127263 := by
  unfold tailWord_8315702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18956160557477458604881835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202199045946426225118739573 18956160557477458604881835)
  ·
    refine ⟨28434240836216187907322753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18956160557477458604881835 28434240836216187907322753)
    ·
      refine ⟨21325680627162140930492065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28434240836216187907322753 21325680627162140930492065)
      ·
        refine ⟨15994260470371605697869049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21325680627162140930492065 15994260470371605697869049)
        ·
          refine ⟨11995695352778704273401787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15994260470371605697869049 11995695352778704273401787)
          ·
            refine ⟨17993543029168056410102681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995695352778704273401787 17993543029168056410102681)
            ·
              refine ⟨13495157271876042307577011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17993543029168056410102681 13495157271876042307577011)
              ·
                refine ⟨20242735907814063461365517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13495157271876042307577011 20242735907814063461365517)
                ·
                  refine ⟨7591025965430273798012069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20242735907814063461365517 7591025965430273798012069)
                  ·
                    refine ⟨1423317368518176337127263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7591025965430273798012069 1423317368518176337127263)
                    ·
                      rfl

theorem cell23_8315702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_8315702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315702 prefixEnd_8315702 := by exact prefixLift 8315702
  have htrace : WordTrace (prefixWord ++ tailWord_8315702) baseStart_8315702 baseEnd_8315702 := by
    simpa [prefixWord, tailWord_8315702, baseEnd_8315702] using wordTrace_append hprefix tailTrace_8315702
  have hstable : (prefixWord ++ tailWord_8315702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315702).length < 2 ^ (prefixWord ++ tailWord_8315702).sum := by decide
  have hdescent : baseEnd_8315702 < baseStart_8315702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315731 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 4]
def baseStart_8315731 : Nat := 118140960795 + 8315731 * 2 ^ 59
def prefixEnd_8315731 : Nat := 4983230072969 + 3 ^ 40 * 8315731 * 2
def baseEnd_8315731 : Nat := 4269966996493509397919155

theorem tailTrace_8315731 : CollatzResearch.WordTrace tailWord_8315731 prefixEnd_8315731 4269966996493509397919155 := by
  unfold tailWord_8315731
  simp only [CollatzResearch.WordTrace]
  refine ⟨303299626636534275630915047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202199751091022850420610031 303299626636534275630915047)
  ·
    refine ⟨454949439954801413446372571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303299626636534275630915047 454949439954801413446372571)
    ·
      refine ⟨682424159932202120169558857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454949439954801413446372571 682424159932202120169558857)
      ·
        refine ⟨511818119949151590127169143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682424159932202120169558857 511818119949151590127169143)
        ·
          refine ⟨767727179923727385190753715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511818119949151590127169143 767727179923727385190753715)
          ·
            refine ⟨1151590769885591077786130573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767727179923727385190753715 1151590769885591077786130573)
            ·
              refine ⟨431846538707096654169798965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1151590769885591077786130573 431846538707096654169798965)
              ·
                refine ⟨40485613003790311328418653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431846538707096654169798965 40485613003790311328418653)
                ·
                  refine ⟨15182104876421366748156995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40485613003790311328418653 15182104876421366748156995)
                  ·
                    refine ⟨22773157314632050122235493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15182104876421366748156995 22773157314632050122235493)
                    ·
                      refine ⟨4269966996493509397919155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22773157314632050122235493 4269966996493509397919155)
                      ·
                        rfl

theorem cell23_8315731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_8315731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315731 prefixEnd_8315731 := by exact prefixLift 8315731
  have htrace : WordTrace (prefixWord ++ tailWord_8315731) baseStart_8315731 baseEnd_8315731 := by
    simpa [prefixWord, tailWord_8315731, baseEnd_8315731] using wordTrace_append hprefix tailTrace_8315731
  have hstable : (prefixWord ++ tailWord_8315731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315731).length < 2 ^ (prefixWord ++ tailWord_8315731).sum := by decide
  have hdescent : baseEnd_8315731 < baseStart_8315731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315761 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_8315761 : Nat := 118140960795 + 8315761 * 2 ^ 59
def prefixEnd_8315761 : Nat := 4983230072969 + 3 ^ 40 * 8315761 * 2
def baseEnd_8315761 : Nat := 4269982400913144280544017

theorem tailTrace_8315761 : CollatzResearch.WordTrace tailWord_8315761 prefixEnd_8315761 4269982400913144280544017 := by
  unfold tailWord_8315761
  simp only [CollatzResearch.WordTrace]
  refine ⟨303300720826425590754507137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202200480550950393836338091 303300720826425590754507137)
  ·
    refine ⟨227475540619819193065880353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303300720826425590754507137 227475540619819193065880353)
    ·
      refine ⟨170606655464864394799410265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227475540619819193065880353 170606655464864394799410265)
      ·
        refine ⟨127954991598648296099557699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170606655464864394799410265 127954991598648296099557699)
        ·
          refine ⟨191932487397972444149336549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127954991598648296099557699 191932487397972444149336549)
          ·
            refine ⟨35987341387119833278000603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191932487397972444149336549 35987341387119833278000603)
            ·
              refine ⟨53981012080679749917000905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35987341387119833278000603 53981012080679749917000905)
              ·
                refine ⟨40485759060509812437750679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53981012080679749917000905 40485759060509812437750679)
                ·
                  refine ⟨60728638590764718656626019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40485759060509812437750679 60728638590764718656626019)
                  ·
                    refine ⟨91092957886147077984939029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60728638590764718656626019 91092957886147077984939029)
                    ·
                      refine ⟨4269982400913144280544017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91092957886147077984939029 4269982400913144280544017)
                      ·
                        rfl

theorem cell23_8315761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_8315761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315761 prefixEnd_8315761 := by exact prefixLift 8315761
  have htrace : WordTrace (prefixWord ++ tailWord_8315761) baseStart_8315761 baseEnd_8315761 := by
    simpa [prefixWord, tailWord_8315761, baseEnd_8315761] using wordTrace_append hprefix tailTrace_8315761
  have hstable : (prefixWord ++ tailWord_8315761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315761).length < 2 ^ (prefixWord ++ tailWord_8315761).sum := by decide
  have hdescent : baseEnd_8315761 < baseStart_8315761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315775 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 2, 4]
def baseStart_8315775 : Nat := 118140960795 + 8315775 * 2 ^ 59
def prefixEnd_8315775 : Nat := 4983230072969 + 3 ^ 40 * 8315775 * 2
def baseEnd_8315775 : Nat := 1423329863214102408589651

theorem tailTrace_8315775 : CollatzResearch.WordTrace tailWord_8315775 prefixEnd_8315775 1423329863214102408589651 := by
  unfold tailWord_8315775
  simp only [CollatzResearch.WordTrace]
  refine ⟨303301231448374871145516779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202200820965583247430344519 303301231448374871145516779)
  ·
    refine ⟨454951847172562306718275169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303301231448374871145516779 454951847172562306718275169)
    ·
      refine ⟨341213885379421730038706377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454951847172562306718275169 341213885379421730038706377)
      ·
        refine ⟨255910414034566297529029783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341213885379421730038706377 255910414034566297529029783)
        ·
          refine ⟨383865621051849446293544675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255910414034566297529029783 383865621051849446293544675)
          ·
            refine ⟨575798431577774169440317013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383865621051849446293544675 575798431577774169440317013)
            ·
              refine ⟨6747637870052041048128715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 575798431577774169440317013 6747637870052041048128715)
              ·
                refine ⟨10121456805078061572193073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6747637870052041048128715 10121456805078061572193073)
                ·
                  refine ⟨7591092603808546179144805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10121456805078061572193073 7591092603808546179144805)
                  ·
                    refine ⟨1423329863214102408589651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7591092603808546179144805 1423329863214102408589651)
                    ·
                      rfl

theorem cell23_8315775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 4].length) (baseStart_8315775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315775 prefixEnd_8315775 := by exact prefixLift 8315775
  have htrace : WordTrace (prefixWord ++ tailWord_8315775) baseStart_8315775 baseEnd_8315775 := by
    simpa [prefixWord, tailWord_8315775, baseEnd_8315775] using wordTrace_append hprefix tailTrace_8315775
  have hstable : (prefixWord ++ tailWord_8315775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315775).length < 2 ^ (prefixWord ++ tailWord_8315775).sum := by decide
  have hdescent : baseEnd_8315775 < baseStart_8315775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315785 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 3]
def baseStart_8315785 : Nat := 118140960795 + 8315785 * 2 ^ 59
def prefixEnd_8315785 : Nat := 4983230072969 + 3 ^ 40 * 8315785 * 2
def baseEnd_8315785 : Nat := 4269994724448852186643907

theorem tailTrace_8315785 : CollatzResearch.WordTrace tailWord_8315785 prefixEnd_8315785 4269994724448852186643907 := by
  unfold tailWord_8315785
  simp only [CollatzResearch.WordTrace]
  refine ⟨303301596178338642853380809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202201064118892428568920539 303301596178338642853380809)
  ·
    refine ⟨227476197133753982140035607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303301596178338642853380809 227476197133753982140035607)
    ·
      refine ⟨341214295700630973210053411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227476197133753982140035607 341214295700630973210053411)
      ·
        refine ⟨511821443550946459815080117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341214295700630973210053411 511821443550946459815080117)
        ·
          refine ⟨47983260332901230607663761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 511821443550946459815080117 47983260332901230607663761)
          ·
            refine ⟨35987445249675922955747821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47983260332901230607663761 35987445249675922955747821)
            ·
              refine ⟨13495291968628471108405433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35987445249675922955747821 13495291968628471108405433)
              ·
                refine ⟨10121468976471353331304075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13495291968628471108405433 10121468976471353331304075)
                ·
                  refine ⟨15182203464707029996956113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10121468976471353331304075 15182203464707029996956113)
                  ·
                    refine ⟨11386652598530272497717085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15182203464707029996956113 11386652598530272497717085)
                    ·
                      refine ⟨4269994724448852186643907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11386652598530272497717085 4269994724448852186643907)
                      ·
                        rfl

theorem cell23_8315785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_8315785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315785 prefixEnd_8315785 := by exact prefixLift 8315785
  have htrace : WordTrace (prefixWord ++ tailWord_8315785) baseStart_8315785 baseEnd_8315785 := by
    simpa [prefixWord, tailWord_8315785, baseEnd_8315785] using wordTrace_append hprefix tailTrace_8315785
  have hstable : (prefixWord ++ tailWord_8315785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315785).length < 2 ^ (prefixWord ++ tailWord_8315785).sum := by decide
  have hdescent : baseEnd_8315785 < baseStart_8315785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315802 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5]
def baseStart_8315802 : Nat := 118140960795 + 8315802 * 2 ^ 59
def prefixEnd_8315802 : Nat := 4983230072969 + 3 ^ 40 * 8315802 * 2
def baseEnd_8315802 : Nat := 4270003453619978620131329

theorem tailTrace_8315802 : CollatzResearch.WordTrace tailWord_8315802 prefixEnd_8315802 4270003453619978620131329 := by
  unfold tailWord_8315802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75825554054819263689187415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202201477479518036504499773 75825554054819263689187415)
  ·
    refine ⟨113738331082228895533781123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75825554054819263689187415 113738331082228895533781123)
    ·
      refine ⟨170607496623343343300671685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113738331082228895533781123 170607496623343343300671685)
      ·
        refine ⟨31988905616876876868875941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170607496623343343300671685 31988905616876876868875941)
        ·
          refine ⟨5997919803164414412914239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31988905616876876868875941 5997919803164414412914239)
          ·
            refine ⟨8996879704746621619371359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997919803164414412914239 8996879704746621619371359)
            ·
              refine ⟨13495319557119932429057039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996879704746621619371359 13495319557119932429057039)
              ·
                refine ⟨20242979335679898643585559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13495319557119932429057039 20242979335679898643585559)
                ·
                  refine ⟨30364469003519847965378339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20242979335679898643585559 30364469003519847965378339)
                  ·
                    refine ⟨45546703505279771948067509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30364469003519847965378339 45546703505279771948067509)
                    ·
                      refine ⟨4270003453619978620131329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45546703505279771948067509 4270003453619978620131329)
                      ·
                        rfl

theorem cell23_8315802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_8315802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315802 prefixEnd_8315802 := by exact prefixLift 8315802
  have htrace : WordTrace (prefixWord ++ tailWord_8315802) baseStart_8315802 baseEnd_8315802 := by
    simpa [prefixWord, tailWord_8315802, baseEnd_8315802] using wordTrace_append hprefix tailTrace_8315802
  have hstable : (prefixWord ++ tailWord_8315802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315802).length < 2 ^ (prefixWord ++ tailWord_8315802).sum := by decide
  have hdescent : baseEnd_8315802 < baseStart_8315802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315811 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_8315811 : Nat := 118140960795 + 8315811 * 2 ^ 59
def prefixEnd_8315811 : Nat := 4983230072969 + 3 ^ 40 * 8315811 * 2
def baseEnd_8315811 : Nat := 4270008074945869084918787

theorem tailTrace_8315811 : CollatzResearch.WordTrace tailWord_8315811 prefixEnd_8315811 4270008074945869084918787 := by
  unfold tailWord_8315811
  simp only [CollatzResearch.WordTrace]
  refine ⟨303302544476244449293827287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202201696317496299529218191 303302544476244449293827287)
  ·
    refine ⟨454953816714366673940740931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303302544476244449293827287 454953816714366673940740931)
    ·
      refine ⟨682430725071550010911111397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454953816714366673940740931 682430725071550010911111397)
      ·
        refine ⟨127955760950915627045833387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 682430725071550010911111397 127955760950915627045833387)
        ·
          refine ⟨191933641426373440568750081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127955760950915627045833387 191933641426373440568750081)
          ·
            refine ⟨143950231069780080426562561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191933641426373440568750081 143950231069780080426562561)
            ·
              refine ⟨107962673302335060319921921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143950231069780080426562561 107962673302335060319921921)
              ·
                refine ⟨80972004976751295239941441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107962673302335060319921921 80972004976751295239941441)
                ·
                  refine ⟨60729003732563471429956081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80972004976751295239941441 60729003732563471429956081)
                  ·
                    refine ⟨45546752799422603572467061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60729003732563471429956081 45546752799422603572467061)
                    ·
                      refine ⟨4270008074945869084918787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45546752799422603572467061 4270008074945869084918787)
                      ·
                        rfl

theorem cell23_8315811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_8315811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315811 prefixEnd_8315811 := by exact prefixLift 8315811
  have htrace : WordTrace (prefixWord ++ tailWord_8315811) baseStart_8315811 baseEnd_8315811 := by
    simpa [prefixWord, tailWord_8315811, baseEnd_8315811] using wordTrace_append hprefix tailTrace_8315811
  have hstable : (prefixWord ++ tailWord_8315811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315811).length < 2 ^ (prefixWord ++ tailWord_8315811).sum := by decide
  have hdescent : baseEnd_8315811 < baseStart_8315811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315831 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 8]
def baseStart_8315831 : Nat := 118140960795 + 8315831 * 2 ^ 59
def prefixEnd_8315831 : Nat := 4983230072969 + 3 ^ 40 * 8315831 * 2
def baseEnd_8315831 : Nat := 1423339448186319668889565

theorem tailTrace_8315831 : CollatzResearch.WordTrace tailWord_8315831 prefixEnd_8315831 1423339448186319668889565 := by
  unfold tailWord_8315831
  simp only [CollatzResearch.WordTrace]
  refine ⟨303303273936171992709555347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202202182624114661806370231 303303273936171992709555347)
  ·
    refine ⟨454954910904257989064333021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303303273936171992709555347 454954910904257989064333021)
    ·
      refine ⟨170608091589096745899124883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454954910904257989064333021 170608091589096745899124883)
      ·
        refine ⟨255912137383645118848687325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170608091589096745899124883 255912137383645118848687325)
        ·
          refine ⟨95967051518866919568257747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255912137383645118848687325 95967051518866919568257747)
          ·
            refine ⟨143950577278300379352386621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95967051518866919568257747 143950577278300379352386621)
            ·
              refine ⟨53981466479362642257144983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143950577278300379352386621 53981466479362642257144983)
              ·
                refine ⟨80972199719043963385717475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53981466479362642257144983 80972199719043963385717475)
                ·
                  refine ⟨121458299578565945078576213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80972199719043963385717475 121458299578565945078576213)
                  ·
                    refine ⟨1423339448186319668889565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121458299578565945078576213 1423339448186319668889565)
                    ·
                      rfl

theorem cell23_8315831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_8315831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315831 prefixEnd_8315831 := by exact prefixLift 8315831
  have htrace : WordTrace (prefixWord ++ tailWord_8315831) baseStart_8315831 baseEnd_8315831 := by
    simpa [prefixWord, tailWord_8315831, baseEnd_8315831] using wordTrace_append hprefix tailTrace_8315831
  have hstable : (prefixWord ++ tailWord_8315831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315831).length < 2 ^ (prefixWord ++ tailWord_8315831).sum := by decide
  have hdescent : baseEnd_8315831 < baseStart_8315831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315838 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_8315838 : Nat := 118140960795 + 8315838 * 2 ^ 59
def prefixEnd_8315838 : Nat := 4983230072969 + 3 ^ 40 * 8315838 * 2
def baseEnd_8315838 : Nat := 4270021938923540479281163

theorem tailTrace_8315838 : CollatzResearch.WordTrace tailWord_8315838 prefixEnd_8315838 4270021938923540479281163 := by
  unfold tailWord_8315838
  simp only [CollatzResearch.WordTrace]
  refine ⟨37912941155893329113132521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202202352831431088603373445 37912941155893329113132521)
  ·
    refine ⟨28434705866919996834849391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37912941155893329113132521 28434705866919996834849391)
    ·
      refine ⟨42652058800379995252274087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28434705866919996834849391 42652058800379995252274087)
      ·
        refine ⟨63978088200569992878411131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42652058800379995252274087 63978088200569992878411131)
        ·
          refine ⟨95967132300854989317616697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63978088200569992878411131 95967132300854989317616697)
          ·
            refine ⟨71975349225641241988212523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95967132300854989317616697 71975349225641241988212523)
            ·
              refine ⟨107963023838461862982318785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71975349225641241988212523 107963023838461862982318785)
              ·
                refine ⟨80972267878846397236739089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107963023838461862982318785 80972267878846397236739089)
                ·
                  refine ⟨60729200909134797927554317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80972267878846397236739089 60729200909134797927554317)
                  ·
                    refine ⟨22773450340925549222832869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60729200909134797927554317 22773450340925549222832869)
                    ·
                      refine ⟨4270021938923540479281163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22773450340925549222832869 4270021938923540479281163)
                      ·
                        rfl

theorem cell23_8315838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_8315838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315838 prefixEnd_8315838 := by exact prefixLift 8315838
  have htrace : WordTrace (prefixWord ++ tailWord_8315838) baseStart_8315838 baseEnd_8315838 := by
    simpa [prefixWord, tailWord_8315838, baseEnd_8315838] using wordTrace_append hprefix tailTrace_8315838
  have hstable : (prefixWord ++ tailWord_8315838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315838).length < 2 ^ (prefixWord ++ tailWord_8315838).sum := by decide
  have hdescent : baseEnd_8315838 < baseStart_8315838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315855 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 1, 4, 2]
def baseStart_8315855 : Nat := 118140960795 + 8315855 * 2 ^ 59
def prefixEnd_8315855 : Nat := 4983230072969 + 3 ^ 40 * 8315855 * 2
def baseEnd_8315855 : Nat := 4270030668094666912768585

theorem tailTrace_8315855 : CollatzResearch.WordTrace tailWord_8315855 prefixEnd_8315855 4270030668094666912768585 := by
  unfold tailWord_8315855
  simp only [CollatzResearch.WordTrace]
  refine ⟨303304149288085044808429019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202202766192056696538952679 303304149288085044808429019)
  ·
    refine ⟨454956223932127567212643529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303304149288085044808429019 454956223932127567212643529)
    ·
      refine ⟨341217167949095675409482647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454956223932127567212643529 341217167949095675409482647)
      ·
        refine ⟨511825751923643513114223971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341217167949095675409482647 511825751923643513114223971)
        ·
          refine ⟨767738627885465269671335957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511825751923643513114223971 767738627885465269671335957)
          ·
            refine ⟨35987748182131184515843873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 767738627885465269671335957 35987748182131184515843873)
            ·
              refine ⟨26990811136598388386882905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35987748182131184515843873 26990811136598388386882905)
              ·
                refine ⟨20243108352448791290162179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26990811136598388386882905 20243108352448791290162179)
                ·
                  refine ⟨30364662528673186935243269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20243108352448791290162179 30364662528673186935243269)
                  ·
                    refine ⟨5693374224126222550358113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30364662528673186935243269 5693374224126222550358113)
                    ·
                      refine ⟨4270030668094666912768585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693374224126222550358113 4270030668094666912768585)
                      ·
                        rfl

theorem cell23_8315855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4, 2].length) (baseStart_8315855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315855 prefixEnd_8315855 := by exact prefixLift 8315855
  have htrace : WordTrace (prefixWord ++ tailWord_8315855) baseStart_8315855 baseEnd_8315855 := by
    simpa [prefixWord, tailWord_8315855, baseEnd_8315855] using wordTrace_append hprefix tailTrace_8315855
  have hstable : (prefixWord ++ tailWord_8315855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315855).length < 2 ^ (prefixWord ++ tailWord_8315855).sum := by decide
  have hdescent : baseEnd_8315855 < baseStart_8315855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315912 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 5]
def baseStart_8315912 : Nat := 118140960795 + 8315912 * 2 ^ 59
def prefixEnd_8315912 : Nat := 4983230072969 + 3 ^ 40 * 8315912 * 2
def baseEnd_8315912 : Nat := 474451104054663687750647

theorem tailTrace_8315912 : CollatzResearch.WordTrace tailWord_8315912 prefixEnd_8315912 474451104054663687750647 := by
  unfold tailWord_8315912
  simp only [CollatzResearch.WordTrace]
  refine ⟨151653114124439271771626995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202204152165919029028835993 151653114124439271771626995)
  ·
    refine ⟨227479671186658907657440493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151653114124439271771626995 227479671186658907657440493)
    ·
      refine ⟨85304876694997090371540185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227479671186658907657440493 85304876694997090371540185)
      ·
        refine ⟨63978657521247817778655139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85304876694997090371540185 63978657521247817778655139)
        ·
          refine ⟨95967986281871726667982709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63978657521247817778655139 95967986281871726667982709)
          ·
            refine ⟨8996998713925474375123379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95967986281871726667982709 8996998713925474375123379)
            ·
              refine ⟨13495498070888211562685069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996998713925474375123379 13495498070888211562685069)
              ·
                refine ⟨5060811776583079336006901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13495498070888211562685069 5060811776583079336006901)
                ·
                  refine ⟨474451104054663687750647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5060811776583079336006901 474451104054663687750647)
                  ·
                    rfl

theorem cell23_8315912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 5].length) (baseStart_8315912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315912 prefixEnd_8315912 := by exact prefixLift 8315912
  have htrace : WordTrace (prefixWord ++ tailWord_8315912) baseStart_8315912 baseEnd_8315912 := by
    simpa [prefixWord, tailWord_8315912, baseEnd_8315912] using wordTrace_append hprefix tailTrace_8315912
  have hstable : (prefixWord ++ tailWord_8315912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315912).length < 2 ^ (prefixWord ++ tailWord_8315912).sum := by decide
  have hdescent : baseEnd_8315912 < baseStart_8315912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8315925 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_8315925 : Nat := 118140960795 + 8315925 * 2 ^ 59
def prefixEnd_8315925 : Nat := 4983230072969 + 3 ^ 40 * 8315925 * 2
def baseEnd_8315925 : Nat := 1423355537246827212964421

theorem tailTrace_8315925 : CollatzResearch.WordTrace tailWord_8315925 prefixEnd_8315925 1423355537246827212964421 := by
  unfold tailWord_8315925
  simp only [CollatzResearch.WordTrace]
  refine ⟨303306702397831446763477229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202204468265220964508984819 303306702397831446763477229)
  ·
    refine ⟨113740013399186792536303961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303306702397831446763477229 113740013399186792536303961)
    ·
      refine ⟨85305010049390094402227971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113740013399186792536303961 85305010049390094402227971)
      ·
        refine ⟨127957515074085141603341957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85305010049390094402227971 127957515074085141603341957)
        ·
          refine ⟨23992034076390964050626617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127957515074085141603341957 23992034076390964050626617)
          ·
            refine ⟨17994025557293223037969963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23992034076390964050626617 17994025557293223037969963)
            ·
              refine ⟨26991038335939834556954945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17994025557293223037969963 26991038335939834556954945)
              ·
                refine ⟨20243278751954875917716209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26991038335939834556954945 20243278751954875917716209)
                ·
                  refine ⟨15182459063966156938287157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20243278751954875917716209 15182459063966156938287157)
                  ·
                    refine ⟨1423355537246827212964421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15182459063966156938287157 1423355537246827212964421)
                    ·
                      rfl

theorem cell23_8315925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_8315925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8315925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8315925 prefixEnd_8315925 := by exact prefixLift 8315925
  have htrace : WordTrace (prefixWord ++ tailWord_8315925) baseStart_8315925 baseEnd_8315925 := by
    simpa [prefixWord, tailWord_8315925, baseEnd_8315925] using wordTrace_append hprefix tailTrace_8315925
  have hstable : (prefixWord ++ tailWord_8315925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8315925).length < 2 ^ (prefixWord ++ tailWord_8315925).sum := by decide
  have hdescent : baseEnd_8315925 < baseStart_8315925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8315925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316002 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_8316002 : Nat := 118140960795 + 8316002 * 2 ^ 59
def prefixEnd_8316002 : Nat := 4983230072969 + 3 ^ 40 * 8316002 * 2
def baseEnd_8316002 : Nat := 474456238861208648625601

theorem tailTrace_8316002 : CollatzResearch.WordTrace tailWord_8316002 prefixEnd_8316002 474456238861208648625601 := by
  unfold tailWord_8316002
  simp only [CollatzResearch.WordTrace]
  refine ⟨75827377704638122228507565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202206340545701659276020173 75827377704638122228507565)
  ·
    refine ⟨28435266639239295835690337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75827377704638122228507565 28435266639239295835690337)
    ·
      refine ⟨21326449979429471876767753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28435266639239295835690337 21326449979429471876767753)
      ·
        refine ⟨15994837484572103907575815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21326449979429471876767753 15994837484572103907575815)
        ·
          refine ⟨23992256226858155861363723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15994837484572103907575815 23992256226858155861363723)
          ·
            refine ⟨35988384340287233792045585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23992256226858155861363723 35988384340287233792045585)
            ·
              refine ⟨26991288255215425344034189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35988384340287233792045585 26991288255215425344034189)
              ·
                refine ⟨10121733095705784504012821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26991288255215425344034189 10121733095705784504012821)
                ·
                  refine ⟨474456238861208648625601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10121733095705784504012821 474456238861208648625601)
                  ·
                    rfl

theorem cell23_8316002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_8316002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316002 prefixEnd_8316002 := by exact prefixLift 8316002
  have htrace : WordTrace (prefixWord ++ tailWord_8316002) baseStart_8316002 baseEnd_8316002 := by
    simpa [prefixWord, tailWord_8316002, baseEnd_8316002] using wordTrace_append hprefix tailTrace_8316002
  have hstable : (prefixWord ++ tailWord_8316002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316002).length < 2 ^ (prefixWord ++ tailWord_8316002).sum := by decide
  have hdescent : baseEnd_8316002 < baseStart_8316002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316012 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_8316012 : Nat := 118140960795 + 8316012 * 2 ^ 59
def prefixEnd_8316012 : Nat := 4983230072969 + 3 ^ 40 * 8316012 * 2
def baseEnd_8316012 : Nat := 4270111284557422798505363

theorem tailTrace_8316012 : CollatzResearch.WordTrace tailWord_8316012 prefixEnd_8316012 4270111284557422798505363 := by
  unfold tailWord_8316012
  simp only [CollatzResearch.WordTrace]
  refine ⟨151654937774258130310947145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202206583699010840414596193 151654937774258130310947145)
  ·
    refine ⟨113741203330693597733210359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151654937774258130310947145 113741203330693597733210359)
    ·
      refine ⟨170611804996040396599815539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113741203330693597733210359 170611804996040396599815539)
      ·
        refine ⟨255917707494060594899723309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170611804996040396599815539 255917707494060594899723309)
        ·
          refine ⟨95969140310272723087396241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255917707494060594899723309 95969140310272723087396241)
          ·
            refine ⟨71976855232704542315547181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95969140310272723087396241 71976855232704542315547181)
            ·
              refine ⟨26991320712264203368330193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71976855232704542315547181 26991320712264203368330193)
              ·
                refine ⟨20243490534198152526247645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26991320712264203368330193 20243490534198152526247645)
                ·
                  refine ⟨7591308950324307197342867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20243490534198152526247645 7591308950324307197342867)
                  ·
                    refine ⟨11386963425486460796014301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7591308950324307197342867 11386963425486460796014301)
                    ·
                      refine ⟨4270111284557422798505363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11386963425486460796014301 4270111284557422798505363)
                      ·
                        rfl

theorem cell23_8316012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_8316012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316012 prefixEnd_8316012 := by exact prefixLift 8316012
  have htrace : WordTrace (prefixWord ++ tailWord_8316012) baseStart_8316012 baseEnd_8316012 := by
    simpa [prefixWord, tailWord_8316012, baseEnd_8316012] using wordTrace_append hprefix tailTrace_8316012
  have hstable : (prefixWord ++ tailWord_8316012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316012).length < 2 ^ (prefixWord ++ tailWord_8316012).sum := by decide
  have hdescent : baseEnd_8316012 < baseStart_8316012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316015 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 1, 5]
def baseStart_8316015 : Nat := 118140960795 + 8316015 * 2 ^ 59
def prefixEnd_8316015 : Nat := 4983230072969 + 3 ^ 40 * 8316015 * 2
def baseEnd_8316015 : Nat := 1423370941666462095589283

theorem tailTrace_8316015 : CollatzResearch.WordTrace tailWord_8316015 prefixEnd_8316015 1423370941666462095589283 := by
  unfold tailWord_8316015
  simp only [CollatzResearch.WordTrace]
  refine ⟨303309984967505392134253499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202206656645003594756168999 303309984967505392134253499)
  ·
    refine ⟨454964977451258088201380249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303309984967505392134253499 454964977451258088201380249)
    ·
      refine ⟨341223733088443566151035187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454964977451258088201380249 341223733088443566151035187)
      ·
        refine ⟨511835599632665349226552781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341223733088443566151035187 511835599632665349226552781)
        ·
          refine ⟨191938349862249505959957293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511835599632665349226552781 191938349862249505959957293)
          ·
            refine ⟨71976881198343564734983985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191938349862249505959957293 71976881198343564734983985)
            ·
              refine ⟨53982660898757673551237989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71976881198343564734983985 53982660898757673551237989)
              ·
                refine ⟨10121748918517063790857123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53982660898757673551237989 10121748918517063790857123)
                ·
                  refine ⟨15182623377775595686285685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10121748918517063790857123 15182623377775595686285685)
                  ·
                    refine ⟨1423370941666462095589283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15182623377775595686285685 1423370941666462095589283)
                    ·
                      rfl

theorem cell23_8316015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_8316015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316015 prefixEnd_8316015 := by exact prefixLift 8316015
  have htrace : WordTrace (prefixWord ++ tailWord_8316015) baseStart_8316015 baseEnd_8316015 := by
    simpa [prefixWord, tailWord_8316015, baseEnd_8316015] using wordTrace_append hprefix tailTrace_8316015
  have hstable : (prefixWord ++ tailWord_8316015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316015).length < 2 ^ (prefixWord ++ tailWord_8316015).sum := by decide
  have hdescent : baseEnd_8316015 < baseStart_8316015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316032 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 1, 5]
def baseStart_8316032 : Nat := 118140960795 + 8316032 * 2 ^ 59
def prefixEnd_8316032 : Nat := 4983230072969 + 3 ^ 40 * 8316032 * 2
def baseEnd_8316032 : Nat := 1423373851390170906751757

theorem tailTrace_8316032 : CollatzResearch.WordTrace tailWord_8316032 prefixEnd_8316032 1423373851390170906751757 := by
  unfold tailWord_8316032
  simp only [CollatzResearch.WordTrace]
  refine ⟨151655302504221902018811175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202207070005629202691748233 151655302504221902018811175)
  ·
    refine ⟨227482953756332853028216763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151655302504221902018811175 227482953756332853028216763)
    ·
      refine ⟨341224430634499279542325145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227482953756332853028216763 341224430634499279542325145)
      ·
        refine ⟨255918322975874459656743859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341224430634499279542325145 255918322975874459656743859)
        ·
          refine ⟨383877484463811689485115789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255918322975874459656743859 383877484463811689485115789)
          ·
            refine ⟨143954056673929383556918421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383877484463811689485115789 143954056673929383556918421)
            ·
              refine ⟨6747846406590439854230551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143954056673929383556918421 6747846406590439854230551)
              ·
                refine ⟨10121769609885659781345827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6747846406590439854230551 10121769609885659781345827)
                ·
                  refine ⟨15182654414828489672018741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10121769609885659781345827 15182654414828489672018741)
                  ·
                    refine ⟨1423373851390170906751757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15182654414828489672018741 1423373851390170906751757)
                    ·
                      rfl

theorem cell23_8316032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 5].length) (baseStart_8316032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316032 prefixEnd_8316032 := by exact prefixLift 8316032
  have htrace : WordTrace (prefixWord ++ tailWord_8316032) baseStart_8316032 baseEnd_8316032 := by
    simpa [prefixWord, tailWord_8316032, baseEnd_8316032] using wordTrace_append hprefix tailTrace_8316032
  have hstable : (prefixWord ++ tailWord_8316032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316032).length < 2 ^ (prefixWord ++ tailWord_8316032).sum := by decide
  have hdescent : baseEnd_8316032 < baseStart_8316032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316046 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_8316046 : Nat := 118140960795 + 8316046 * 2 ^ 59
def prefixEnd_8316046 : Nat := 4983230072969 + 3 ^ 40 * 8316046 * 2
def baseEnd_8316046 : Nat := 4270128742899675665480207

theorem tailTrace_8316046 : CollatzResearch.WordTrace tailWord_8316046 prefixEnd_8316046 4270128742899675665480207 := by
  unfold tailWord_8316046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37913889453799135553578999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202207410420262056285754661 37913889453799135553578999)
  ·
    refine ⟨56870834180698703330368499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37913889453799135553578999 56870834180698703330368499)
    ·
      refine ⟨85306251271048054995552749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56870834180698703330368499 85306251271048054995552749)
      ·
        refine ⟨31989844226643020623332281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85306251271048054995552749 31989844226643020623332281)
        ·
          refine ⟨23992383169982265467499211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31989844226643020623332281 23992383169982265467499211)
          ·
            refine ⟨35988574754973398201248817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23992383169982265467499211 35988574754973398201248817)
            ·
              refine ⟨26991431066230048650936613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35988574754973398201248817 26991431066230048650936613)
              ·
                refine ⟨5060893324918134122050615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26991431066230048650936613 5060893324918134122050615)
                ·
                  refine ⟨7591339987377201183075923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060893324918134122050615 7591339987377201183075923)
                  ·
                    refine ⟨11387009981065801774613885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7591339987377201183075923 11387009981065801774613885)
                    ·
                      refine ⟨4270128742899675665480207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387009981065801774613885 4270128742899675665480207)
                      ·
                        rfl

theorem cell23_8316046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_8316046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316046 prefixEnd_8316046 := by exact prefixLift 8316046
  have htrace : WordTrace (prefixWord ++ tailWord_8316046) baseStart_8316046 baseEnd_8316046 := by
    simpa [prefixWord, tailWord_8316046, baseEnd_8316046] using wordTrace_append hprefix tailTrace_8316046
  have hstable : (prefixWord ++ tailWord_8316046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316046).length < 2 ^ (prefixWord ++ tailWord_8316046).sum := by decide
  have hdescent : baseEnd_8316046 < baseStart_8316046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316055 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_8316055 : Nat := 118140960795 + 8316055 * 2 ^ 59
def prefixEnd_8316055 : Nat := 4983230072969 + 3 ^ 40 * 8316055 * 2
def baseEnd_8316055 : Nat := 4270133364225566130267665

theorem tailTrace_8316055 : CollatzResearch.WordTrace tailWord_8316055 prefixEnd_8316055 4270133364225566130267665 := by
  unfold tailWord_8316055
  simp only [CollatzResearch.WordTrace]
  refine ⟨303311443887360478965709619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202207629258240319310473079 303311443887360478965709619)
  ·
    refine ⟨454967165831040718448564429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303311443887360478965709619 454967165831040718448564429)
    ·
      refine ⟨170612687186640269418211661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454967165831040718448564429 170612687186640269418211661)
      ·
        refine ⟨63979757694990101031829373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170612687186640269418211661 63979757694990101031829373)
        ·
          refine ⟨23992409135621287886936015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63979757694990101031829373 23992409135621287886936015)
          ·
            refine ⟨35988613703431931830404023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23992409135621287886936015 35988613703431931830404023)
            ·
              refine ⟨53982920555147897745606035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35988613703431931830404023 53982920555147897745606035)
              ·
                refine ⟨80974380832721846618409053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53982920555147897745606035 80974380832721846618409053)
                ·
                  refine ⟨30365392812270692481903395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80974380832721846618409053 30365392812270692481903395)
                  ·
                    refine ⟨45548089218406038722855093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30365392812270692481903395 45548089218406038722855093)
                    ·
                      refine ⟨4270133364225566130267665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45548089218406038722855093 4270133364225566130267665)
                      ·
                        rfl

theorem cell23_8316055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_8316055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316055 prefixEnd_8316055 := by exact prefixLift 8316055
  have htrace : WordTrace (prefixWord ++ tailWord_8316055) baseStart_8316055 baseEnd_8316055 := by
    simpa [prefixWord, tailWord_8316055, baseEnd_8316055] using wordTrace_append hprefix tailTrace_8316055
  have hstable : (prefixWord ++ tailWord_8316055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316055).length < 2 ^ (prefixWord ++ tailWord_8316055).sum := by decide
  have hdescent : baseEnd_8316055 < baseStart_8316055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316065 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_8316065 : Nat := 118140960795 + 8316065 * 2 ^ 59
def prefixEnd_8316065 : Nat := 4983230072969 + 3 ^ 40 * 8316065 * 2
def baseEnd_8316065 : Nat := 4270138499032111091142619

theorem tailTrace_8316065 : CollatzResearch.WordTrace tailWord_8316065 prefixEnd_8316065 4270138499032111091142619 := by
  unfold tailWord_8316065
  simp only [CollatzResearch.WordTrace]
  refine ⟨303311808617324250673573649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202207872411549500449049099 303311808617324250673573649)
  ·
    refine ⟨227483856462993188005180237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303311808617324250673573649 227483856462993188005180237)
    ·
      refine ⟨85306446173622445501942589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227483856462993188005180237 85306446173622445501942589)
      ·
        refine ⟨31989917315108417063228471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85306446173622445501942589 31989917315108417063228471)
        ·
          refine ⟨47984875972662625594842707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31989917315108417063228471 47984875972662625594842707)
          ·
            refine ⟨71977313958993938392264061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47984875972662625594842707 71977313958993938392264061)
            ·
              refine ⟨26991492734622726897099023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71977313958993938392264061 26991492734622726897099023)
              ·
                refine ⟨40487239101934090345648535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26991492734622726897099023 40487239101934090345648535)
                ·
                  refine ⟨60730858652901135518472803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40487239101934090345648535 60730858652901135518472803)
                  ·
                    refine ⟨91096287979351703277709205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60730858652901135518472803 91096287979351703277709205)
                    ·
                      refine ⟨4270138499032111091142619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91096287979351703277709205 4270138499032111091142619)
                      ·
                        rfl

theorem cell23_8316065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_8316065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316065 prefixEnd_8316065 := by exact prefixLift 8316065
  have htrace : WordTrace (prefixWord ++ tailWord_8316065) baseStart_8316065 baseEnd_8316065 := by
    simpa [prefixWord, tailWord_8316065, baseEnd_8316065] using wordTrace_append hprefix tailTrace_8316065
  have hstable : (prefixWord ++ tailWord_8316065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316065).length < 2 ^ (prefixWord ++ tailWord_8316065).sum := by decide
  have hdescent : baseEnd_8316065 < baseStart_8316065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316069 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 3, 2, 2]
def baseStart_8316069 : Nat := 118140960795 + 8316069 * 2 ^ 59
def prefixEnd_8316069 : Nat := 4983230072969 + 3 ^ 40 * 8316069 * 2
def baseEnd_8316069 : Nat := 4270140552954729075492601

theorem tailTrace_8316069 : CollatzResearch.WordTrace tailWord_8316069 prefixEnd_8316069 4270140552954729075492601 := by
  unfold tailWord_8316069
  simp only [CollatzResearch.WordTrace]
  refine ⟨303311954509309759356719261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202207969672873172904479507 303311954509309759356719261)
  ·
    refine ⟨113741982940991159758769723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303311954509309759356719261 113741982940991159758769723)
    ·
      refine ⟨170612974411486739638154585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113741982940991159758769723 170612974411486739638154585)
      ·
        refine ⟨127959730808615054728615939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170612974411486739638154585 127959730808615054728615939)
        ·
          refine ⟨191939596212922582092923909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127959730808615054728615939 191939596212922582092923909)
          ·
            refine ⟨35988674289922984142423233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191939596212922582092923909 35988674289922984142423233)
            ·
              refine ⟨26991505717442238106817425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35988674289922984142423233 26991505717442238106817425)
              ·
                refine ⟨20243629288081678580113069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26991505717442238106817425 20243629288081678580113069)
                ·
                  refine ⟨7591360983030629467542401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20243629288081678580113069 7591360983030629467542401)
                  ·
                    refine ⟨5693520737272972100656801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7591360983030629467542401 5693520737272972100656801)
                    ·
                      refine ⟨4270140552954729075492601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693520737272972100656801 4270140552954729075492601)
                      ·
                        rfl

theorem cell23_8316069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_8316069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316069 prefixEnd_8316069 := by exact prefixLift 8316069
  have htrace : WordTrace (prefixWord ++ tailWord_8316069) baseStart_8316069 baseEnd_8316069 := by
    simpa [prefixWord, tailWord_8316069, baseEnd_8316069] using wordTrace_append hprefix tailTrace_8316069
  have hstable : (prefixWord ++ tailWord_8316069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316069).length < 2 ^ (prefixWord ++ tailWord_8316069).sum := by decide
  have hdescent : baseEnd_8316069 < baseStart_8316069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316129 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_8316129 : Nat := 118140960795 + 8316129 * 2 ^ 59
def prefixEnd_8316129 : Nat := 4983230072969 + 3 ^ 40 * 8316129 * 2
def baseEnd_8316129 : Nat := 4270171361793998840742325

theorem tailTrace_8316129 : CollatzResearch.WordTrace tailWord_8316129 prefixEnd_8316129 4270171361793998840742325 := by
  unfold tailWord_8316129
  simp only [CollatzResearch.WordTrace]
  refine ⟨303314142889092389603903441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202209428592728259735935627 303314142889092389603903441)
  ·
    refine ⟨227485607166819292202927581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303314142889092389603903441 227485607166819292202927581)
    ·
      refine ⟨85307102687557234576097843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227485607166819292202927581 85307102687557234576097843)
      ·
        refine ⟨127960654031335851864146765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85307102687557234576097843 127960654031335851864146765)
        ·
          refine ⟨47985245261750944449055037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127960654031335851864146765 47985245261750944449055037)
          ·
            refine ⟨17994466973156604168395639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47985245261750944449055037 17994466973156604168395639)
            ·
              refine ⟨26991700459734906252593459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17994466973156604168395639 26991700459734906252593459)
              ·
                refine ⟨40487550689602359378890189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26991700459734906252593459 40487550689602359378890189)
                ·
                  refine ⟨15182831508600884767083821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40487550689602359378890189 15182831508600884767083821)
                  ·
                    refine ⟨5693561815725331787656433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15182831508600884767083821 5693561815725331787656433)
                    ·
                      refine ⟨4270171361793998840742325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693561815725331787656433 4270171361793998840742325)
                      ·
                        rfl

theorem cell23_8316129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_8316129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316129 prefixEnd_8316129 := by exact prefixLift 8316129
  have htrace : WordTrace (prefixWord ++ tailWord_8316129) baseStart_8316129 baseEnd_8316129 := by
    simpa [prefixWord, tailWord_8316129, baseEnd_8316129] using wordTrace_append hprefix tailTrace_8316129
  have hstable : (prefixWord ++ tailWord_8316129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316129).length < 2 ^ (prefixWord ++ tailWord_8316129).sum := by decide
  have hdescent : baseEnd_8316129 < baseStart_8316129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316165 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 7]
def baseStart_8316165 : Nat := 118140960795 + 8316165 * 2 ^ 59
def prefixEnd_8316165 : Nat := 4983230072969 + 3 ^ 40 * 8316165 * 2
def baseEnd_8316165 : Nat := 474465538566395633321351

theorem tailTrace_8316165 : CollatzResearch.WordTrace tailWord_8316165 prefixEnd_8316165 474465538566395633321351 := by
  unfold tailWord_8316165
  simp only [CollatzResearch.WordTrace]
  refine ⟨303315455916961967752213949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202210303944641311834809299 303315455916961967752213949)
  ·
    refine ⟨113743295968860737907080231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303315455916961967752213949 113743295968860737907080231)
    ·
      refine ⟨170614943953291106860620347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113743295968860737907080231 170614943953291106860620347)
      ·
        refine ⟨255922415929936660290930521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170614943953291106860620347 255922415929936660290930521)
        ·
          refine ⟨191941811947452495218197891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255922415929936660290930521 191941811947452495218197891)
          ·
            refine ⟨287912717921178742827296837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191941811947452495218197891 287912717921178742827296837)
            ·
              refine ⟨53983634610221014280118157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287912717921178742827296837 53983634610221014280118157)
              ·
                refine ⟨20243862978832880355044309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53983634610221014280118157 20243862978832880355044309)
                ·
                  refine ⟨474465538566395633321351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20243862978832880355044309 474465538566395633321351)
                  ·
                    rfl

theorem cell23_8316165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_8316165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316165 prefixEnd_8316165 := by exact prefixLift 8316165
  have htrace : WordTrace (prefixWord ++ tailWord_8316165) baseStart_8316165 baseEnd_8316165 := by
    simpa [prefixWord, tailWord_8316165, baseEnd_8316165] using wordTrace_append hprefix tailTrace_8316165
  have hstable : (prefixWord ++ tailWord_8316165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316165).length < 2 ^ (prefixWord ++ tailWord_8316165).sum := by decide
  have hdescent : baseEnd_8316165 < baseStart_8316165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316172 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_8316172 : Nat := 118140960795 + 8316172 * 2 ^ 59
def prefixEnd_8316172 : Nat := 4983230072969 + 3 ^ 40 * 8316172 * 2
def baseEnd_8316172 : Nat := 4270193441462142172504627

theorem tailTrace_8316172 : CollatzResearch.WordTrace tailWord_8316172 prefixEnd_8316172 4270193441462142172504627 := by
  unfold tailWord_8316172
  simp only [CollatzResearch.WordTrace]
  refine ⟨151657855613968303973859385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202210474151957738631812513 151657855613968303973859385)
  ·
    refine ⟨113743391710476227980394539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151657855613968303973859385 113743391710476227980394539)
    ·
      refine ⟨170615087565714341970591809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113743391710476227980394539 170615087565714341970591809)
      ·
        refine ⟨127961315674285756477943857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170615087565714341970591809 127961315674285756477943857)
        ·
          refine ⟨95970986755714317358457893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127961315674285756477943857 95970986755714317358457893)
          ·
            refine ⟨17994560016696434504710855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95970986755714317358457893 17994560016696434504710855)
            ·
              refine ⟨26991840025044651757066283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17994560016696434504710855 26991840025044651757066283)
              ·
                refine ⟨40487760037566977635599425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26991840025044651757066283 40487760037566977635599425)
                ·
                  refine ⟨30365820028175233226699569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40487760037566977635599425 30365820028175233226699569)
                  ·
                    refine ⟨22774365021131424920024677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30365820028175233226699569 22774365021131424920024677)
                    ·
                      refine ⟨4270193441462142172504627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22774365021131424920024677 4270193441462142172504627)
                      ·
                        rfl

theorem cell23_8316172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_8316172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316172 prefixEnd_8316172 := by exact prefixLift 8316172
  have htrace : WordTrace (prefixWord ++ tailWord_8316172) baseStart_8316172 baseEnd_8316172 := by
    simpa [prefixWord, tailWord_8316172, baseEnd_8316172] using wordTrace_append hprefix tailTrace_8316172
  have hstable : (prefixWord ++ tailWord_8316172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316172).length < 2 ^ (prefixWord ++ tailWord_8316172).sum := by decide
  have hdescent : baseEnd_8316172 < baseStart_8316172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316222 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_8316222 : Nat := 118140960795 + 8316222 * 2 ^ 59
def prefixEnd_8316222 : Nat := 4983230072969 + 3 ^ 40 * 8316222 * 2
def baseEnd_8316222 : Nat := 4270219115494866976879397

theorem tailTrace_8316222 : CollatzResearch.WordTrace tailWord_8316222 prefixEnd_8316222 4270219115494866976879397 := by
  unfold tailWord_8316222
  simp only [CollatzResearch.WordTrace]
  refine ⟨37914691859719433310879865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202211689918503644324692613 37914691859719433310879865)
  ·
    refine ⟨28436018894789574983159899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37914691859719433310879865 28436018894789574983159899)
    ·
      refine ⟨42654028342184362474739849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28436018894789574983159899 42654028342184362474739849)
      ·
        refine ⟨31990521256638271856054887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42654028342184362474739849 31990521256638271856054887)
        ·
          refine ⟨47985781884957407784082331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31990521256638271856054887 47985781884957407784082331)
          ·
            refine ⟨71978672827436111676123497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47985781884957407784082331 71978672827436111676123497)
            ·
              refine ⟨53984004620577083757092623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71978672827436111676123497 53984004620577083757092623)
              ·
                refine ⟨80976006930865625635638935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53984004620577083757092623 80976006930865625635638935)
                ·
                  refine ⟨121464010396298438453458403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80976006930865625635638935 121464010396298438453458403)
                  ·
                    refine ⟨182196015594447657680187605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121464010396298438453458403 182196015594447657680187605)
                    ·
                      refine ⟨4270219115494866976879397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182196015594447657680187605 4270219115494866976879397)
                      ·
                        rfl

theorem cell23_8316222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_8316222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316222 prefixEnd_8316222 := by exact prefixLift 8316222
  have htrace : WordTrace (prefixWord ++ tailWord_8316222) baseStart_8316222 baseEnd_8316222 := by
    simpa [prefixWord, tailWord_8316222, baseEnd_8316222] using wordTrace_append hprefix tailTrace_8316222
  have hstable : (prefixWord ++ tailWord_8316222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316222).length < 2 ^ (prefixWord ++ tailWord_8316222).sum := by decide
  have hdescent : baseEnd_8316222 < baseStart_8316222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316235 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_8316235 : Nat := 118140960795 + 8316235 * 2 ^ 59
def prefixEnd_8316235 : Nat := 4983230072969 + 3 ^ 40 * 8316235 * 2
def baseEnd_8316235 : Nat := 4270225790743375426016837

theorem tailTrace_8316235 : CollatzResearch.WordTrace tailWord_8316235 prefixEnd_8316235 4270225790743375426016837 := by
  unfold tailWord_8316235
  simp only [CollatzResearch.WordTrace]
  refine ⟨303318009026708369707262159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202212006017805579804841439 303318009026708369707262159)
  ·
    refine ⟨454977013540062554560893239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303318009026708369707262159 454977013540062554560893239)
    ·
      refine ⟨682465520310093831841339859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454977013540062554560893239 682465520310093831841339859)
      ·
        refine ⟨1023698280465140747762009789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682465520310093831841339859 1023698280465140747762009789)
        ·
          refine ⟨383886855174427780410753671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1023698280465140747762009789 383886855174427780410753671)
          ·
            refine ⟨575830282761641670616130507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383886855174427780410753671 575830282761641670616130507)
            ·
              refine ⟨863745424142462505924195761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575830282761641670616130507 863745424142462505924195761)
              ·
                refine ⟨647809068106846879443146821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863745424142462505924195761 647809068106846879443146821)
                ·
                  refine ⟨121464200270033789895590029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647809068106846879443146821 121464200270033789895590029)
                  ·
                    refine ⟨45549075101262671210846261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121464200270033789895590029 45549075101262671210846261)
                    ·
                      refine ⟨4270225790743375426016837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45549075101262671210846261 4270225790743375426016837)
                      ·
                        rfl

theorem cell23_8316235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_8316235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316235 prefixEnd_8316235 := by exact prefixLift 8316235
  have htrace : WordTrace (prefixWord ++ tailWord_8316235) baseStart_8316235 baseEnd_8316235 := by
    simpa [prefixWord, tailWord_8316235, baseEnd_8316235] using wordTrace_append hprefix tailTrace_8316235
  have hstable : (prefixWord ++ tailWord_8316235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316235).length < 2 ^ (prefixWord ++ tailWord_8316235).sum := by decide
  have hdescent : baseEnd_8316235 < baseStart_8316235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316266 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_8316266 : Nat := 118140960795 + 8316266 * 2 ^ 59
def prefixEnd_8316266 : Nat := 4983230072969 + 3 ^ 40 * 8316266 * 2
def baseEnd_8316266 : Nat := 4270241708643664804729195

theorem tailTrace_8316266 : CollatzResearch.WordTrace tailWord_8316266 prefixEnd_8316266 4270241708643664804729195 := by
  unfold tailWord_8316266
  simp only [CollatzResearch.WordTrace]
  refine ⟨75829784922399015500410163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202212759793064041334427101 75829784922399015500410163)
  ·
    refine ⟨113744677383598523250615245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75829784922399015500410163 113744677383598523250615245)
    ·
      refine ⟨42654254018849446218980717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113744677383598523250615245 42654254018849446218980717)
      ·
        refine ⟨15995345257068542332117769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42654254018849446218980717 15995345257068542332117769)
        ·
          refine ⟨11996508942801406749088327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15995345257068542332117769 11996508942801406749088327)
          ·
            refine ⟨17994763414202110123632491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11996508942801406749088327 17994763414202110123632491)
            ·
              refine ⟨26992145121303165185448737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17994763414202110123632491 26992145121303165185448737)
              ·
                refine ⟨20244108840977373889086553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26992145121303165185448737 20244108840977373889086553)
                ·
                  refine ⟨15183081630733030416814915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20244108840977373889086553 15183081630733030416814915)
                  ·
                    refine ⟨22774622446099545625222373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15183081630733030416814915 22774622446099545625222373)
                    ·
                      refine ⟨4270241708643664804729195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22774622446099545625222373 4270241708643664804729195)
                      ·
                        rfl

theorem cell23_8316266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_8316266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316266 prefixEnd_8316266 := by exact prefixLift 8316266
  have htrace : WordTrace (prefixWord ++ tailWord_8316266) baseStart_8316266 baseEnd_8316266 := by
    simpa [prefixWord, tailWord_8316266, baseEnd_8316266] using wordTrace_append hprefix tailTrace_8316266
  have hstable : (prefixWord ++ tailWord_8316266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316266).length < 2 ^ (prefixWord ++ tailWord_8316266).sum := by decide
  have hdescent : baseEnd_8316266 < baseStart_8316266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316269 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_8316269 : Nat := 118140960795 + 8316269 * 2 ^ 59
def prefixEnd_8316269 : Nat := 4983230072969 + 3 ^ 40 * 8316269 * 2
def baseEnd_8316269 : Nat := 4270243249085628292991681

theorem tailTrace_8316269 : CollatzResearch.WordTrace tailWord_8316269 prefixEnd_8316269 4270243249085628292991681 := by
  unfold tailWord_8316269
  simp only [CollatzResearch.WordTrace]
  refine ⟨303319249108585193513999861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202212832739056795675999907 303319249108585193513999861)
  ·
    refine ⟨28436179603929861891937487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303319249108585193513999861 28436179603929861891937487)
    ·
      refine ⟨42654269405894792837906231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28436179603929861891937487 42654269405894792837906231)
      ·
        refine ⟨63981404108842189256859347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42654269405894792837906231 63981404108842189256859347)
        ·
          refine ⟨95972106163263283885289021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63981404108842189256859347 95972106163263283885289021)
          ·
            refine ⟨35989539811223731456983383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95972106163263283885289021 35989539811223731456983383)
            ·
              refine ⟨53984309716835597185475075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35989539811223731456983383 53984309716835597185475075)
              ·
                refine ⟨80976464575253395778212613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53984309716835597185475075 80976464575253395778212613)
                ·
                  refine ⟨15183087107860011708414865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80976464575253395778212613 15183087107860011708414865)
                  ·
                    refine ⟨11387315330895008781311149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15183087107860011708414865 11387315330895008781311149)
                    ·
                      refine ⟨4270243249085628292991681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387315330895008781311149 4270243249085628292991681)
                      ·
                        rfl

theorem cell23_8316269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_8316269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316269 prefixEnd_8316269 := by exact prefixLift 8316269
  have htrace : WordTrace (prefixWord ++ tailWord_8316269) baseStart_8316269 baseEnd_8316269 := by
    simpa [prefixWord, tailWord_8316269, baseEnd_8316269] using wordTrace_append hprefix tailTrace_8316269
  have hstable : (prefixWord ++ tailWord_8316269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316269).length < 2 ^ (prefixWord ++ tailWord_8316269).sum := by decide
  have hdescent : baseEnd_8316269 < baseStart_8316269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316272 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 6]
def baseStart_8316272 : Nat := 118140960795 + 8316272 * 2 ^ 59
def prefixEnd_8316272 : Nat := 4983230072969 + 3 ^ 40 * 8316272 * 2
def baseEnd_8316272 : Nat := 474471643280843531250463

theorem tailTrace_8316272 : CollatzResearch.WordTrace tailWord_8316272 prefixEnd_8316272 474471643280843531250463 := by
  unfold tailWord_8316272
  simp only [CollatzResearch.WordTrace]
  refine ⟨151659679263787162513179535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202212905685049550017572713 151659679263787162513179535)
  ·
    refine ⟨227489518895680743769769303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151659679263787162513179535 227489518895680743769769303)
    ·
      refine ⟨341234278343521115654653955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227489518895680743769769303 341234278343521115654653955)
      ·
        refine ⟨511851417515281673481980933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341234278343521115654653955 511851417515281673481980933)
        ·
          refine ⟨95972140784115313777871425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511851417515281673481980933 95972140784115313777871425)
          ·
            refine ⟨71979105588086485333403569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95972140784115313777871425 71979105588086485333403569)
            ·
              refine ⟨53984329191064864000052677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71979105588086485333403569 53984329191064864000052677)
              ·
                refine ⟨10122061723324662000009877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53984329191064864000052677 10122061723324662000009877)
                ·
                  refine ⟨474471643280843531250463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10122061723324662000009877 474471643280843531250463)
                  ·
                    rfl

theorem cell23_8316272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_8316272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316272 prefixEnd_8316272 := by exact prefixLift 8316272
  have htrace : WordTrace (prefixWord ++ tailWord_8316272) baseStart_8316272 baseEnd_8316272 := by
    simpa [prefixWord, tailWord_8316272, baseEnd_8316272] using wordTrace_append hprefix tailTrace_8316272
  have hstable : (prefixWord ++ tailWord_8316272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316272).length < 2 ^ (prefixWord ++ tailWord_8316272).sum := by decide
  have hdescent : baseEnd_8316272 < baseStart_8316272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316299 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 3]
def baseStart_8316299 : Nat := 118140960795 + 8316299 * 2 ^ 59
def prefixEnd_8316299 : Nat := 4983230072969 + 3 ^ 40 * 8316299 * 2
def baseEnd_8316299 : Nat := 4270258653505263175616543

theorem tailTrace_8316299 : CollatzResearch.WordTrace tailWord_8316299 prefixEnd_8316299 4270258653505263175616543 := by
  unfold tailWord_8316299
  simp only [CollatzResearch.WordTrace]
  refine ⟨303320343298476508637591951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202213562198984339091727967 303320343298476508637591951)
  ·
    refine ⟨454980514947714762956387927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303320343298476508637591951 454980514947714762956387927)
    ·
      refine ⟨682470772421572144434581891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454980514947714762956387927 682470772421572144434581891)
      ·
        refine ⟨1023706158632358216651872837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682470772421572144434581891 1023706158632358216651872837)
        ·
          refine ⟨191944904743567165622226157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1023706158632358216651872837 191944904743567165622226157)
          ·
            refine ⟨71979339278837687108334809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191944904743567165622226157 71979339278837687108334809)
            ·
              refine ⟨53984504459128265331251107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71979339278837687108334809 53984504459128265331251107)
              ·
                refine ⟨80976756688692397996876661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53984504459128265331251107 80976756688692397996876661)
                ·
                  refine ⟨7591570939564912312207187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80976756688692397996876661 7591570939564912312207187)
                  ·
                    refine ⟨11387356409347368468310781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7591570939564912312207187 11387356409347368468310781)
                    ·
                      refine ⟨4270258653505263175616543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387356409347368468310781 4270258653505263175616543)
                      ·
                        rfl

theorem cell23_8316299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 3].length) (baseStart_8316299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316299 prefixEnd_8316299 := by exact prefixLift 8316299
  have htrace : WordTrace (prefixWord ++ tailWord_8316299) baseStart_8316299 baseEnd_8316299 := by
    simpa [prefixWord, tailWord_8316299, baseEnd_8316299] using wordTrace_append hprefix tailTrace_8316299
  have hstable : (prefixWord ++ tailWord_8316299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316299).length < 2 ^ (prefixWord ++ tailWord_8316299).sum := by decide
  have hdescent : baseEnd_8316299 < baseStart_8316299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316309 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_8316309 : Nat := 118140960795 + 8316309 * 2 ^ 59
def prefixEnd_8316309 : Nat := 4983230072969 + 3 ^ 40 * 8316309 * 2
def baseEnd_8316309 : Nat := 4270263788311808136491497

theorem tailTrace_8316309 : CollatzResearch.WordTrace tailWord_8316309 prefixEnd_8316309 4270263788311808136491497 := by
  unfold tailWord_8316309
  simp only [CollatzResearch.WordTrace]
  refine ⟨303320708028440280345455981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202213805352293520230303987 303320708028440280345455981)
  ·
    refine ⟨113745265510665105129545993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303320708028440280345455981 113745265510665105129545993)
    ·
      refine ⟨85308949132998828847159495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113745265510665105129545993 85308949132998828847159495)
      ·
        refine ⟨127963423699498243270739243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85308949132998828847159495 127963423699498243270739243)
        ·
          refine ⟨191945135549247364906108865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127963423699498243270739243 191945135549247364906108865)
          ·
            refine ⟨143958851661935523679581649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191945135549247364906108865 143958851661935523679581649)
            ·
              refine ⟨107969138746451642759686237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143958851661935523679581649 107969138746451642759686237)
              ·
                refine ⟨40488427029919366034882339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107969138746451642759686237 40488427029919366034882339)
                ·
                  refine ⟨60732640544879049052323509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40488427029919366034882339 60732640544879049052323509)
                  ·
                    refine ⟨5693685051082410848655329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60732640544879049052323509 5693685051082410848655329)
                    ·
                      refine ⟨4270263788311808136491497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5693685051082410848655329 4270263788311808136491497)
                      ·
                        rfl

theorem cell23_8316309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_8316309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316309 prefixEnd_8316309 := by exact prefixLift 8316309
  have htrace : WordTrace (prefixWord ++ tailWord_8316309) baseStart_8316309 baseEnd_8316309 := by
    simpa [prefixWord, tailWord_8316309, baseEnd_8316309] using wordTrace_append hprefix tailTrace_8316309
  have hstable : (prefixWord ++ tailWord_8316309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316309).length < 2 ^ (prefixWord ++ tailWord_8316309).sum := by decide
  have hdescent : baseEnd_8316309 < baseStart_8316309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316349 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_8316349 : Nat := 118140960795 + 8316349 * 2 ^ 59
def prefixEnd_8316349 : Nat := 4983230072969 + 3 ^ 40 * 8316349 * 2
def baseEnd_8316349 : Nat := 1423428109179329326663771

theorem tailTrace_8316349 : CollatzResearch.WordTrace tailWord_8316349 prefixEnd_8316349 1423428109179329326663771 := by
  unfold tailWord_8316349
  simp only [CollatzResearch.WordTrace]
  refine ⟨303322166948295367176912101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202214777965530244784608067 303322166948295367176912101)
  ·
    refine ⟨56872906302805381345671019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303322166948295367176912101 56872906302805381345671019)
    ·
      refine ⟨85309359454208072018506529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56872906302805381345671019 85309359454208072018506529)
      ·
        refine ⟨63982019590656054013879897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85309359454208072018506529 63982019590656054013879897)
        ·
          refine ⟨47986514692992040510409923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63982019590656054013879897 47986514692992040510409923)
          ·
            refine ⟨71979772039488060765614885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47986514692992040510409923 71979772039488060765614885)
            ·
              refine ⟨13496207257404011393552791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71979772039488060765614885 13496207257404011393552791)
              ·
                refine ⟨20244310886106017090329187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13496207257404011393552791 20244310886106017090329187)
                ·
                  refine ⟨30366466329159025635493781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20244310886106017090329187 30366466329159025635493781)
                  ·
                    refine ⟨1423428109179329326663771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30366466329159025635493781 1423428109179329326663771)
                    ·
                      rfl

theorem cell23_8316349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_8316349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316349 prefixEnd_8316349 := by exact prefixLift 8316349
  have htrace : WordTrace (prefixWord ++ tailWord_8316349) baseStart_8316349 baseEnd_8316349 := by
    simpa [prefixWord, tailWord_8316349, baseEnd_8316349] using wordTrace_append hprefix tailTrace_8316349
  have hstable : (prefixWord ++ tailWord_8316349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316349).length < 2 ^ (prefixWord ++ tailWord_8316349).sum := by decide
  have hdescent : baseEnd_8316349 < baseStart_8316349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316352 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_8316352 : Nat := 118140960795 + 8316352 * 2 ^ 59
def prefixEnd_8316352 : Nat := 4983230072969 + 3 ^ 40 * 8316352 * 2
def baseEnd_8316352 : Nat := 4270285867979951468253799

theorem tailTrace_8316352 : CollatzResearch.WordTrace tailWord_8316352 prefixEnd_8316352 4270285867979951468253799 := by
  unfold tailWord_8316352
  simp only [CollatzResearch.WordTrace]
  refine ⟨151661138183642249344635655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202214850911522999126180873 151661138183642249344635655)
  ·
    refine ⟨227491707275463374016953483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151661138183642249344635655 227491707275463374016953483)
    ·
      refine ⟨341237560913195061025430225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227491707275463374016953483 341237560913195061025430225)
      ·
        refine ⟨255928170684896295769072669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341237560913195061025430225 255928170684896295769072669)
        ·
          refine ⟨95973064006836110913402251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255928170684896295769072669 95973064006836110913402251)
          ·
            refine ⟨143959596010254166370103377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95973064006836110913402251 143959596010254166370103377)
            ·
              refine ⟨107969697007690624777577533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143959596010254166370103377 107969697007690624777577533)
              ·
                refine ⟨40488636377883984291591575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107969697007690624777577533 40488636377883984291591575)
                ·
                  refine ⟨60732954566825976437387363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40488636377883984291591575 60732954566825976437387363)
                  ·
                    refine ⟨91099431850238964656081045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60732954566825976437387363 91099431850238964656081045)
                    ·
                      refine ⟨4270285867979951468253799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91099431850238964656081045 4270285867979951468253799)
                      ·
                        rfl

theorem cell23_8316352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_8316352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316352 prefixEnd_8316352 := by exact prefixLift 8316352
  have htrace : WordTrace (prefixWord ++ tailWord_8316352) baseStart_8316352 baseEnd_8316352 := by
    simpa [prefixWord, tailWord_8316352, baseEnd_8316352] using wordTrace_append hprefix tailTrace_8316352
  have hstable : (prefixWord ++ tailWord_8316352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316352).length < 2 ^ (prefixWord ++ tailWord_8316352).sum := by decide
  have hdescent : baseEnd_8316352 < baseStart_8316352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316354 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_8316354 : Nat := 118140960795 + 8316354 * 2 ^ 59
def prefixEnd_8316354 : Nat := 4983230072969 + 3 ^ 40 * 8316354 * 2
def baseEnd_8316354 : Nat := 4270286894941260460428791

theorem tailTrace_8316354 : CollatzResearch.WordTrace tailWord_8316354 prefixEnd_8316354 4270286894941260460428791 := by
  unfold tailWord_8316354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75830587328319313257711029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202214899542184835353896077 75830587328319313257711029)
  ·
    refine ⟨7109117562029935617910409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75830587328319313257711029 7109117562029935617910409)
    ·
      refine ⟨5331838171522451713432807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7109117562029935617910409 5331838171522451713432807)
      ·
        refine ⟨7997757257283677570149211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331838171522451713432807 7997757257283677570149211)
        ·
          refine ⟨11996635885925516355223817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7997757257283677570149211 11996635885925516355223817)
          ·
            refine ⟨8997476914444137266417863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11996635885925516355223817 8997476914444137266417863)
            ·
              refine ⟨13496215371666205899626795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8997476914444137266417863 13496215371666205899626795)
              ·
                refine ⟨20244323057499308849440193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13496215371666205899626795 20244323057499308849440193)
                ·
                  refine ⟨15183242293124481637080145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20244323057499308849440193 15183242293124481637080145)
                  ·
                    refine ⟨11387431719843361227810109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15183242293124481637080145 11387431719843361227810109)
                    ·
                      refine ⟨4270286894941260460428791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11387431719843361227810109 4270286894941260460428791)
                      ·
                        rfl

theorem cell23_8316354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_8316354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316354 prefixEnd_8316354 := by exact prefixLift 8316354
  have htrace : WordTrace (prefixWord ++ tailWord_8316354) baseStart_8316354 baseEnd_8316354 := by
    simpa [prefixWord, tailWord_8316354, baseEnd_8316354] using wordTrace_append hprefix tailTrace_8316354
  have hstable : (prefixWord ++ tailWord_8316354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316354).length < 2 ^ (prefixWord ++ tailWord_8316354).sum := by decide
  have hdescent : baseEnd_8316354 < baseStart_8316354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8316356 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_8316356 : Nat := 118140960795 + 8316356 * 2 ^ 59
def prefixEnd_8316356 : Nat := 4983230072969 + 3 ^ 40 * 8316356 * 2
def baseEnd_8316356 : Nat := 4270287921902569452603781

theorem tailTrace_8316356 : CollatzResearch.WordTrace tailWord_8316356 prefixEnd_8316356 4270287921902569452603781 := by
  unfold tailWord_8316356
  simp only [CollatzResearch.WordTrace]
  refine ⟨151661211129635003686208461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202214948172846671581611281 151661211129635003686208461)
  ·
    refine ⟨56872954173613126382328173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151661211129635003686208461 56872954173613126382328173)
    ·
      refine ⟨21327357815104922393373065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56872954173613126382328173 21327357815104922393373065)
      ·
        refine ⟨15995518361328691795029799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21327357815104922393373065 15995518361328691795029799)
        ·
          refine ⟨23993277541993037692544699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15995518361328691795029799 23993277541993037692544699)
          ·
            refine ⟨35989916312989556538817049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23993277541993037692544699 35989916312989556538817049)
            ·
              refine ⟨26992437234742167404112787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35989916312989556538817049 26992437234742167404112787)
              ·
                refine ⟨40488655852113251106169181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26992437234742167404112787 40488655852113251106169181)
                ·
                  refine ⟨15183245944542469164813443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40488655852113251106169181 15183245944542469164813443)
                  ·
                    refine ⟨22774868916813703747220165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15183245944542469164813443 22774868916813703747220165)
                    ·
                      refine ⟨4270287921902569452603781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22774868916813703747220165 4270287921902569452603781)
                      ·
                        rfl

theorem cell23_8316356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_8316356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8316356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8316356 prefixEnd_8316356 := by exact prefixLift 8316356
  have htrace : WordTrace (prefixWord ++ tailWord_8316356) baseStart_8316356 baseEnd_8316356 := by
    simpa [prefixWord, tailWord_8316356, baseEnd_8316356] using wordTrace_append hprefix tailTrace_8316356
  have hstable : (prefixWord ++ tailWord_8316356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8316356).length < 2 ^ (prefixWord ++ tailWord_8316356).sum := by decide
  have hdescent : baseEnd_8316356 < baseStart_8316356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8316356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
