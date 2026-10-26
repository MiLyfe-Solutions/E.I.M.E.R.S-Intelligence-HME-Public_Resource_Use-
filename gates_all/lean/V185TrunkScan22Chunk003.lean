import V185TrunkScan22Chunk002

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_26473 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_26473 : Nat := 118140960795 + 26473 * 2 ^ 59
def prefixEnd_26473 : Nat := 4983230072969 + 3 ^ 40 * 26473 * 2
def baseEnd_26473 : Nat := 9062248911053438643839

theorem tailTrace_26473 : CollatzResearch.WordTrace tailWord_26473 prefixEnd_26473 9062248911053438643839 := by
  unfold tailWord_26473
  simp only [CollatzResearch.WordTrace]
  refine ⟨965549633100317073556073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 643699755400211382370715 965549633100317073556073)
  ·
    refine ⟨724162224825237805167055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 965549633100317073556073 724162224825237805167055)
    ·
      refine ⟨1086243337237856707750583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724162224825237805167055 1086243337237856707750583)
      ·
        refine ⟨1629365005856785061625875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086243337237856707750583 1629365005856785061625875)
        ·
          refine ⟨2444047508785177592438813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629365005856785061625875 2444047508785177592438813)
          ·
            refine ⟨916517815794441597164555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2444047508785177592438813 916517815794441597164555)
            ·
              refine ⟨1374776723691662395746833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916517815794441597164555 1374776723691662395746833)
              ·
                refine ⟨1031082542768746796810125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374776723691662395746833 1031082542768746796810125)
                ·
                  refine ⟨386655953538280048803797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031082542768746796810125 386655953538280048803797)
                  ·
                    refine ⟨9062248911053438643839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 386655953538280048803797 9062248911053438643839)
                    ·
                      rfl

theorem cell22_26473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_26473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26473 prefixEnd_26473 := by exact prefixLift 26473
  have htrace : WordTrace (prefixWord ++ tailWord_26473) baseStart_26473 baseEnd_26473 := by
    simpa [prefixWord, tailWord_26473, baseEnd_26473] using wordTrace_append hprefix tailTrace_26473
  have hstable : (prefixWord ++ tailWord_26473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26473).length < 2 ^ (prefixWord ++ tailWord_26473).sum := by decide
  have hdescent : baseEnd_26473 < baseStart_26473 := by decide
  rcases family_descends (prefixWord ++ tailWord_26473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26505 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_26505 : Nat := 118140960795 + 26505 * 2 ^ 59
def prefixEnd_26505 : Nat := 4983230072969 + 3 ^ 40 * 26505 * 2
def baseEnd_26505 : Nat := 9073203165016021843741

theorem tailTrace_26505 : CollatzResearch.WordTrace tailWord_26505 prefixEnd_26505 9073203165016021843741 := by
  unfold tailWord_26505
  simp only [CollatzResearch.WordTrace]
  refine ⟨966716768984386538720969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 644477845989591025813979 966716768984386538720969)
  ·
    refine ⟨725037576738289904040727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 966716768984386538720969 725037576738289904040727)
    ·
      refine ⟨1087556365107434856061091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725037576738289904040727 1087556365107434856061091)
      ·
        refine ⟨1631334547661152284091637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087556365107434856061091 1631334547661152284091637)
        ·
          refine ⟨152937613843233026633591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1631334547661152284091637 152937613843233026633591)
          ·
            refine ⟨229406420764849539950387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152937613843233026633591 229406420764849539950387)
            ·
              refine ⟨344109631147274309925581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229406420764849539950387 344109631147274309925581)
              ·
                refine ⟨129041111680227866222093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344109631147274309925581 129041111680227866222093)
                ·
                  refine ⟨48390416880085449833285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129041111680227866222093 48390416880085449833285)
                  ·
                    refine ⟨9073203165016021843741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48390416880085449833285 9073203165016021843741)
                    ·
                      rfl

theorem cell22_26505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_26505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26505 prefixEnd_26505 := by exact prefixLift 26505
  have htrace : WordTrace (prefixWord ++ tailWord_26505) baseStart_26505 baseEnd_26505 := by
    simpa [prefixWord, tailWord_26505, baseEnd_26505] using wordTrace_append hprefix tailTrace_26505
  have hstable : (prefixWord ++ tailWord_26505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26505).length < 2 ^ (prefixWord ++ tailWord_26505).sum := by decide
  have hdescent : baseEnd_26505 < baseStart_26505 := by decide
  rcases family_descends (prefixWord ++ tailWord_26505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26556 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_26556 : Nat := 118140960795 + 26556 * 2 ^ 59
def prefixEnd_26556 : Nat := 4983230072969 + 3 ^ 40 * 26556 * 2
def baseEnd_26556 : Nat := 9090661507268888818585

theorem tailTrace_26556 : CollatzResearch.WordTrace tailWord_26556 prefixEnd_26556 9090661507268888818585 := by
  unfold tailWord_26556
  simp only [CollatzResearch.WordTrace]
  refine ⟨484288445899811124413761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 645717927866414832551681 484288445899811124413761)
  ·
    refine ⟨363216334424858343310321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 484288445899811124413761 363216334424858343310321)
    ·
      refine ⟨272412250818643757482741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363216334424858343310321 272412250818643757482741)
      ·
        refine ⟨25538648514247852264007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272412250818643757482741 25538648514247852264007)
        ·
          refine ⟨38307972771371778396011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25538648514247852264007 38307972771371778396011)
          ·
            refine ⟨57461959157057667594017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38307972771371778396011 57461959157057667594017)
            ·
              refine ⟨43096469367793250695513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57461959157057667594017 43096469367793250695513)
              ·
                refine ⟨32322352025844938021635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43096469367793250695513 32322352025844938021635)
                ·
                  refine ⟨48483528038767407032453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32322352025844938021635 48483528038767407032453)
                  ·
                    refine ⟨9090661507268888818585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48483528038767407032453 9090661507268888818585)
                    ·
                      rfl

theorem cell22_26556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_26556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26556 prefixEnd_26556 := by exact prefixLift 26556
  have htrace : WordTrace (prefixWord ++ tailWord_26556) baseStart_26556 baseEnd_26556 := by
    simpa [prefixWord, tailWord_26556, baseEnd_26556] using wordTrace_append hprefix tailTrace_26556
  have hstable : (prefixWord ++ tailWord_26556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26556).length < 2 ^ (prefixWord ++ tailWord_26556).sum := by decide
  have hdescent : baseEnd_26556 < baseStart_26556 := by decide
  rcases family_descends (prefixWord ++ tailWord_26556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26588 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 6]
def baseStart_26588 : Nat := 118140960795 + 26588 * 2 ^ 59
def prefixEnd_26588 : Nat := 4983230072969 + 3 ^ 40 * 26588 * 2
def baseEnd_26588 : Nat := 3033871920410490672829

theorem tailTrace_26588 : CollatzResearch.WordTrace tailWord_26588 prefixEnd_26588 3033871920410490672829 := by
  unfold tailWord_26588
  simp only [CollatzResearch.WordTrace]
  refine ⟨484872013841845856996209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 646496018455794475994945 484872013841845856996209)
  ·
    refine ⟨363654010381384392747157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 484872013841845856996209 363654010381384392747157)
    ·
      refine ⟨17046281736627393410023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 363654010381384392747157 17046281736627393410023)
      ·
        refine ⟨25569422604941090115035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17046281736627393410023 25569422604941090115035)
        ·
          refine ⟨38354133907411635172553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25569422604941090115035 38354133907411635172553)
          ·
            refine ⟨28765600430558726379415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38354133907411635172553 28765600430558726379415)
            ·
              refine ⟨43148400645838089569123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28765600430558726379415 43148400645838089569123)
              ·
                refine ⟨64722600968757134353685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43148400645838089569123 64722600968757134353685)
                ·
                  refine ⟨3033871920410490672829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64722600968757134353685 3033871920410490672829)
                  ·
                    rfl

theorem cell22_26588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_26588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26588 prefixEnd_26588 := by exact prefixLift 26588
  have htrace : WordTrace (prefixWord ++ tailWord_26588) baseStart_26588 baseEnd_26588 := by
    simpa [prefixWord, tailWord_26588, baseEnd_26588] using wordTrace_append hprefix tailTrace_26588
  have hstable : (prefixWord ++ tailWord_26588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26588).length < 2 ^ (prefixWord ++ tailWord_26588).sum := by decide
  have hdescent : baseEnd_26588 < baseStart_26588 := by decide
  rcases family_descends (prefixWord ++ tailWord_26588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26672 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_26672 : Nat := 118140960795 + 26672 * 2 ^ 59
def prefixEnd_26672 : Nat := 4983230072969 + 3 ^ 40 * 26672 * 2
def baseEnd_26672 : Nat := 3043456892627750972743

theorem tailTrace_26672 : CollatzResearch.WordTrace tailWord_26672 prefixEnd_26672 3043456892627750972743 := by
  unfold tailWord_26672
  simp only [CollatzResearch.WordTrace]
  refine ⟨486403879689687030025135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 648538506252916040033513 486403879689687030025135)
  ·
    refine ⟨729605819534530545037703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 486403879689687030025135 729605819534530545037703)
    ·
      refine ⟨1094408729301795817556555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729605819534530545037703 1094408729301795817556555)
      ·
        refine ⟨1641613093952693726334833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094408729301795817556555 1641613093952693726334833)
        ·
          refine ⟨1231209820464520294751125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641613093952693726334833 1231209820464520294751125)
          ·
            refine ⟨57712960334274388816459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1231209820464520294751125 57712960334274388816459)
            ·
              refine ⟨86569440501411583224689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57712960334274388816459 86569440501411583224689)
              ·
                refine ⟨64927080376058687418517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86569440501411583224689 64927080376058687418517)
                ·
                  refine ⟨3043456892627750972743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64927080376058687418517 3043456892627750972743)
                  ·
                    rfl

theorem cell22_26672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_26672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26672 prefixEnd_26672 := by exact prefixLift 26672
  have htrace : WordTrace (prefixWord ++ tailWord_26672) baseStart_26672 baseEnd_26672 := by
    simpa [prefixWord, tailWord_26672, baseEnd_26672] using wordTrace_append hprefix tailTrace_26672
  have hstable : (prefixWord ++ tailWord_26672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26672).length < 2 ^ (prefixWord ++ tailWord_26672).sum := by decide
  have hdescent : baseEnd_26672 < baseStart_26672 := by decide
  rcases family_descends (prefixWord ++ tailWord_26672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26687 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 1, 5]
def baseStart_26687 : Nat := 118140960795 + 26687 * 2 ^ 59
def prefixEnd_26687 : Nat := 4983230072969 + 3 ^ 40 * 26687 * 2
def baseEnd_26687 : Nat := 9135505484428213793183

theorem tailTrace_26687 : CollatzResearch.WordTrace tailWord_26687 prefixEnd_26687 9135505484428213793183 := by
  unfold tailWord_26687
  simp only [CollatzResearch.WordTrace]
  refine ⟨973354854325031621846315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 648903236216687747897543 973354854325031621846315)
  ·
    refine ⟨1460032281487547432769473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 973354854325031621846315 1460032281487547432769473)
    ·
      refine ⟨1095024211115660574577105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460032281487547432769473 1095024211115660574577105)
      ·
        refine ⟨821268158336745430932829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1095024211115660574577105 821268158336745430932829)
        ·
          refine ⟨307975559376279536599811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 821268158336745430932829 307975559376279536599811)
          ·
            refine ⟨461963339064419304899717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307975559376279536599811 461963339064419304899717)
            ·
              refine ⟨86618126074578619668697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461963339064419304899717 86618126074578619668697)
              ·
                refine ⟨64963594555933964751523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86618126074578619668697 64963594555933964751523)
                ·
                  refine ⟨97445391833900947127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64963594555933964751523 97445391833900947127285)
                  ·
                    refine ⟨9135505484428213793183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97445391833900947127285 9135505484428213793183)
                    ·
                      rfl

theorem cell22_26687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_26687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26687 prefixEnd_26687 := by exact prefixLift 26687
  have htrace : WordTrace (prefixWord ++ tailWord_26687) baseStart_26687 baseEnd_26687 := by
    simpa [prefixWord, tailWord_26687, baseEnd_26687] using wordTrace_append hprefix tailTrace_26687
  have hstable : (prefixWord ++ tailWord_26687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26687).length < 2 ^ (prefixWord ++ tailWord_26687).sum := by decide
  have hdescent : baseEnd_26687 < baseStart_26687 := by decide
  rcases family_descends (prefixWord ++ tailWord_26687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26772 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_26772 : Nat := 118140960795 + 26772 * 2 ^ 59
def prefixEnd_26772 : Nat := 4983230072969 + 3 ^ 40 * 26772 * 2
def baseEnd_26772 : Nat := 9164602721516325417923

theorem tailTrace_26772 : CollatzResearch.WordTrace tailWord_26772 prefixEnd_26772 9164602721516325417923 := by
  unfold tailWord_26772
  simp only [CollatzResearch.WordTrace]
  refine ⟨488227529508545569345285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 650970039344727425793713 488227529508545569345285)
  ·
    refine ⟨91542661782852294252241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 488227529508545569345285 91542661782852294252241)
    ·
      refine ⟨68656996337139220689181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91542661782852294252241 68656996337139220689181)
      ·
        refine ⟨25746373626427207758443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68656996337139220689181 25746373626427207758443)
        ·
          refine ⟨38619560439640811637665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25746373626427207758443 38619560439640811637665)
          ·
            refine ⟨28964670329730608728249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38619560439640811637665 28964670329730608728249)
            ·
              refine ⟨21723502747297956546187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28964670329730608728249 21723502747297956546187)
              ·
                refine ⟨32585254120946934819281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21723502747297956546187 32585254120946934819281)
                ·
                  refine ⟨24438940590710201114461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32585254120946934819281 24438940590710201114461)
                  ·
                    refine ⟨9164602721516325417923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24438940590710201114461 9164602721516325417923)
                    ·
                      rfl

theorem cell22_26772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_26772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26772 prefixEnd_26772 := by exact prefixLift 26772
  have htrace : WordTrace (prefixWord ++ tailWord_26772) baseStart_26772 baseEnd_26772 := by
    simpa [prefixWord, tailWord_26772, baseEnd_26772] using wordTrace_append hprefix tailTrace_26772
  have hstable : (prefixWord ++ tailWord_26772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26772).length < 2 ^ (prefixWord ++ tailWord_26772).sum := by decide
  have hdescent : baseEnd_26772 < baseStart_26772 := by decide
  rcases family_descends (prefixWord ++ tailWord_26772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26777 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_26777 : Nat := 118140960795 + 26777 * 2 ^ 59
def prefixEnd_26777 : Nat := 4983230072969 + 3 ^ 40 * 26777 * 2
def baseEnd_26777 : Nat := 9166314323697979042907

theorem tailTrace_26777 : CollatzResearch.WordTrace tailWord_26777 prefixEnd_26777 9166314323697979042907 := by
  unfold tailWord_26777
  simp only [CollatzResearch.WordTrace]
  refine ⟨976637423998976992622585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 651091615999317995081723 976637423998976992622585)
  ·
    refine ⟨732478067999232744466939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 976637423998976992622585 732478067999232744466939)
    ·
      refine ⟨1098717101998849116700409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732478067999232744466939 1098717101998849116700409)
      ·
        refine ⟨824037826499136837525307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098717101998849116700409 824037826499136837525307)
        ·
          refine ⟨1236056739748705256287961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824037826499136837525307 1236056739748705256287961)
          ·
            refine ⟨927042554811528942215971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236056739748705256287961 927042554811528942215971)
            ·
              refine ⟨1390563832217293413323957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927042554811528942215971 1390563832217293413323957)
              ·
                refine ⟨130365359270371257499121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390563832217293413323957 130365359270371257499121)
                ·
                  refine ⟨97774019452778443124341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130365359270371257499121 97774019452778443124341)
                  ·
                    refine ⟨9166314323697979042907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97774019452778443124341 9166314323697979042907)
                    ·
                      rfl

theorem cell22_26777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_26777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26777 prefixEnd_26777 := by exact prefixLift 26777
  have htrace : WordTrace (prefixWord ++ tailWord_26777) baseStart_26777 baseEnd_26777 := by
    simpa [prefixWord, tailWord_26777, baseEnd_26777] using wordTrace_append hprefix tailTrace_26777
  have hstable : (prefixWord ++ tailWord_26777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26777).length < 2 ^ (prefixWord ++ tailWord_26777).sum := by decide
  have hdescent : baseEnd_26777 < baseStart_26777 := by decide
  rcases family_descends (prefixWord ++ tailWord_26777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26839 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 6, 3]
def baseStart_26839 : Nat := 118140960795 + 26839 * 2 ^ 59
def prefixEnd_26839 : Nat := 4983230072969 + 3 ^ 40 * 26839 * 2
def baseEnd_26839 : Nat := 9187538190750483992717

theorem tailTrace_26839 : CollatzResearch.WordTrace tailWord_26839 prefixEnd_26839 9187538190750483992717 := by
  unfold tailWord_26839
  simp only [CollatzResearch.WordTrace]
  refine ⟨978898749774361581379571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 652599166516241054253047 978898749774361581379571)
  ·
    refine ⟨1468348124661542372069357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 978898749774361581379571 1468348124661542372069357)
    ·
      refine ⟨550630546748078389526009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1468348124661542372069357 550630546748078389526009)
      ·
        refine ⟨412972910061058792144507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550630546748078389526009 412972910061058792144507)
        ·
          refine ⟨619459365091588188216761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412972910061058792144507 619459365091588188216761)
          ·
            refine ⟨464594523818691141162571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619459365091588188216761 464594523818691141162571)
            ·
              refine ⟨696891785728036711743857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464594523818691141162571 696891785728036711743857)
              ·
                refine ⟨522668839296027533807893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696891785728036711743857 522668839296027533807893)
                ·
                  refine ⟨24500101842001290647245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 522668839296027533807893 24500101842001290647245)
                  ·
                    refine ⟨9187538190750483992717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24500101842001290647245 9187538190750483992717)
                    ·
                      rfl

theorem cell22_26839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_26839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26839 prefixEnd_26839 := by exact prefixLift 26839
  have htrace : WordTrace (prefixWord ++ tailWord_26839) baseStart_26839 baseEnd_26839 := by
    simpa [prefixWord, tailWord_26839, baseEnd_26839] using wordTrace_append hprefix tailTrace_26839
  have hstable : (prefixWord ++ tailWord_26839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26839).length < 2 ^ (prefixWord ++ tailWord_26839).sum := by decide
  have hdescent : baseEnd_26839 < baseStart_26839 := by decide
  rcases family_descends (prefixWord ++ tailWord_26839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26901 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_26901 : Nat := 118140960795 + 26901 * 2 ^ 59
def prefixEnd_26901 : Nat := 4983230072969 + 3 ^ 40 * 26901 * 2
def baseEnd_26901 : Nat := 9208762057802988942527

theorem tailTrace_26901 : CollatzResearch.WordTrace tailWord_26901 prefixEnd_26901 9208762057802988942527 := by
  unfold tailWord_26901
  simp only [CollatzResearch.WordTrace]
  refine ⟨981160075549746170136557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 654106717033164113424371 981160075549746170136557)
  ·
    refine ⟨367935028331154813801209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 981160075549746170136557 367935028331154813801209)
    ·
      refine ⟨275951271248366110350907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367935028331154813801209 275951271248366110350907)
      ·
        refine ⟨413926906872549165526361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275951271248366110350907 413926906872549165526361)
        ·
          refine ⟨310445180154411874144771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413926906872549165526361 310445180154411874144771)
          ·
            refine ⟨465667770231617811217157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310445180154411874144771 465667770231617811217157)
            ·
              refine ⟨87312706918428339603217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465667770231617811217157 87312706918428339603217)
              ·
                refine ⟨65484530188821254702413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87312706918428339603217 65484530188821254702413)
                ·
                  refine ⟨24556698820807970513405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65484530188821254702413 24556698820807970513405)
                  ·
                    refine ⟨9208762057802988942527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24556698820807970513405 9208762057802988942527)
                    ·
                      rfl

theorem cell22_26901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_26901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26901 prefixEnd_26901 := by exact prefixLift 26901
  have htrace : WordTrace (prefixWord ++ tailWord_26901) baseStart_26901 baseEnd_26901 := by
    simpa [prefixWord, tailWord_26901, baseEnd_26901] using wordTrace_append hprefix tailTrace_26901
  have hstable : (prefixWord ++ tailWord_26901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26901).length < 2 ^ (prefixWord ++ tailWord_26901).sum := by decide
  have hdescent : baseEnd_26901 < baseStart_26901 := by decide
  rcases family_descends (prefixWord ++ tailWord_26901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26961 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_26961 : Nat := 118140960795 + 26961 * 2 ^ 59
def prefixEnd_26961 : Nat := 4983230072969 + 3 ^ 40 * 26961 * 2
def baseEnd_26961 : Nat := 9229301283982832442343

theorem tailTrace_26961 : CollatzResearch.WordTrace tailWord_26961 prefixEnd_26961 9229301283982832442343 := by
  unfold tailWord_26961
  simp only [CollatzResearch.WordTrace]
  refine ⟨983348455332376417320737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 655565636888250944880491 983348455332376417320737)
  ·
    refine ⟨737511341499282312990553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 983348455332376417320737 737511341499282312990553)
    ·
      refine ⟨553133506124461734742915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 737511341499282312990553 553133506124461734742915)
      ·
        refine ⟨829700259186692602114373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553133506124461734742915 829700259186692602114373)
        ·
          refine ⟨155568798597504862896445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 829700259186692602114373 155568798597504862896445)
          ·
            refine ⟨58338299474064323586167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155568798597504862896445 58338299474064323586167)
            ·
              refine ⟨87507449211096485379251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58338299474064323586167 87507449211096485379251)
              ·
                refine ⟨131261173816644728068877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87507449211096485379251 131261173816644728068877)
                ·
                  refine ⟨49222940181241773025829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131261173816644728068877 49222940181241773025829)
                  ·
                    refine ⟨9229301283982832442343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49222940181241773025829 9229301283982832442343)
                    ·
                      rfl

theorem cell22_26961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_26961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26961 prefixEnd_26961 := by exact prefixLift 26961
  have htrace : WordTrace (prefixWord ++ tailWord_26961) baseStart_26961 baseEnd_26961 := by
    simpa [prefixWord, tailWord_26961, baseEnd_26961] using wordTrace_append hprefix tailTrace_26961
  have hstable : (prefixWord ++ tailWord_26961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26961).length < 2 ^ (prefixWord ++ tailWord_26961).sum := by decide
  have hdescent : baseEnd_26961 < baseStart_26961 := by decide
  rcases family_descends (prefixWord ++ tailWord_26961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27004 : List Nat := [2, 2, 2, 1, 1, 1, 2, 11]
def baseStart_27004 : Nat := 118140960795 + 27004 * 2 ^ 59
def prefixEnd_27004 : Nat := 4983230072969 + 3 ^ 40 * 27004 * 2
def baseEnd_27004 : Nat := 1027113451416117068579

theorem tailTrace_27004 : CollatzResearch.WordTrace tailWord_27004 prefixEnd_27004 1027113451416117068579 := by
  unfold tailWord_27004
  simp only [CollatzResearch.WordTrace]
  refine ⟨492458397088297380568033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 656611196117729840757377 492458397088297380568033)
  ·
    refine ⟨369343797816223035426025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 492458397088297380568033 369343797816223035426025)
    ·
      refine ⟨277007848362167276569519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369343797816223035426025 277007848362167276569519)
      ·
        refine ⟨415511772543250914854279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277007848362167276569519 415511772543250914854279)
        ·
          refine ⟨623267658814876372281419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415511772543250914854279 623267658814876372281419)
          ·
            refine ⟨934901488222314558422129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623267658814876372281419 934901488222314558422129)
            ·
              refine ⟨701176116166735918816597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934901488222314558422129 701176116166735918816597)
              ·
                refine ⟨1027113451416117068579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 701176116166735918816597 1027113451416117068579)
                ·
                  rfl

theorem cell22_27004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_27004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27004 prefixEnd_27004 := by exact prefixLift 27004
  have htrace : WordTrace (prefixWord ++ tailWord_27004) baseStart_27004 baseEnd_27004 := by
    simpa [prefixWord, tailWord_27004, baseEnd_27004] using wordTrace_append hprefix tailTrace_27004
  have hstable : (prefixWord ++ tailWord_27004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27004).length < 2 ^ (prefixWord ++ tailWord_27004).sum := by decide
  have hdescent : baseEnd_27004 < baseStart_27004 := by decide
  rcases family_descends (prefixWord ++ tailWord_27004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27010 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_27010 : Nat := 118140960795 + 27010 * 2 ^ 59
def prefixEnd_27010 : Nat := 4983230072969 + 3 ^ 40 * 27010 * 2
def baseEnd_27010 : Nat := 3082024995121012655731

theorem tailTrace_27010 : CollatzResearch.WordTrace tailWord_27010 prefixEnd_27010 3082024995121012655731 := by
  unfold tailWord_27010
  simp only [CollatzResearch.WordTrace]
  refine ⟨246283908038714446463621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 656757088103238523902989 246283908038714446463621)
  ·
    refine ⟨46178232757258958711929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246283908038714446463621 46178232757258958711929)
    ·
      refine ⟨34633674567944219033947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46178232757258958711929 34633674567944219033947)
      ·
        refine ⟨51950511851916328550921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34633674567944219033947 51950511851916328550921)
        ·
          refine ⟨38962883888937246413191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51950511851916328550921 38962883888937246413191)
          ·
            refine ⟨58444325833405869619787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38962883888937246413191 58444325833405869619787)
            ·
              refine ⟨87666488750108804429681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58444325833405869619787 87666488750108804429681)
              ·
                refine ⟨65749866562581603322261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87666488750108804429681 65749866562581603322261)
                ·
                  refine ⟨3082024995121012655731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65749866562581603322261 3082024995121012655731)
                  ·
                    rfl

theorem cell22_27010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_27010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27010 prefixEnd_27010 := by exact prefixLift 27010
  have htrace : WordTrace (prefixWord ++ tailWord_27010) baseStart_27010 baseEnd_27010 := by
    simpa [prefixWord, tailWord_27010, baseEnd_27010] using wordTrace_append hprefix tailTrace_27010
  have hstable : (prefixWord ++ tailWord_27010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27010).length < 2 ^ (prefixWord ++ tailWord_27010).sum := by decide
  have hdescent : baseEnd_27010 < baseStart_27010 := by decide
  rcases family_descends (prefixWord ++ tailWord_27010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27038 : List Nat := [4, 3, 1, 2, 1, 2, 9]
def baseStart_27038 : Nat := 118140960795 + 27038 * 2 ^ 59
def prefixEnd_27038 : Nat := 4983230072969 + 3 ^ 40 * 27038 * 2
def baseEnd_27038 : Nat := 342802220651122158041

theorem tailTrace_27038 : CollatzResearch.WordTrace tailWord_27038 prefixEnd_27038 342802220651122158041 := by
  unfold tailWord_27038
  simp only [CollatzResearch.WordTrace]
  refine ⟨123269609506677320984221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 657437917368945711915845 123269609506677320984221)
  ·
    refine ⟨46226103565003995369083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123269609506677320984221 46226103565003995369083)
    ·
      refine ⟨69339155347505993053625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46226103565003995369083 69339155347505993053625)
      ·
        refine ⟨52004366510629494790219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69339155347505993053625 52004366510629494790219)
        ·
          refine ⟨78006549765944242185329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52004366510629494790219 78006549765944242185329)
          ·
            refine ⟨58504912324458181638997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78006549765944242185329 58504912324458181638997)
            ·
              refine ⟨342802220651122158041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 58504912324458181638997 342802220651122158041)
              ·
                rfl

theorem cell22_27038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 9].length) (baseStart_27038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27038 prefixEnd_27038 := by exact prefixLift 27038
  have htrace : WordTrace (prefixWord ++ tailWord_27038) baseStart_27038 baseEnd_27038 := by
    simpa [prefixWord, tailWord_27038, baseEnd_27038] using wordTrace_append hprefix tailTrace_27038
  have hstable : (prefixWord ++ tailWord_27038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27038).length < 2 ^ (prefixWord ++ tailWord_27038).sum := by decide
  have hdescent : baseEnd_27038 < baseStart_27038 := by decide
  rcases family_descends (prefixWord ++ tailWord_27038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27066 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_27066 : Nat := 118140960795 + 27066 * 2 ^ 59
def prefixEnd_27066 : Nat := 4983230072969 + 3 ^ 40 * 27066 * 2
def baseEnd_27066 : Nat := 3088414976599186189007

theorem tailTrace_27066 : CollatzResearch.WordTrace tailWord_27066 prefixEnd_27066 3088414976599186189007 := by
  unfold tailWord_27066
  simp only [CollatzResearch.WordTrace]
  refine ⟨246794529987994837473263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 658118746634652899928701 246794529987994837473263)
  ·
    refine ⟨370191794981992256209895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246794529987994837473263 370191794981992256209895)
    ·
      refine ⟨555287692472988384314843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370191794981992256209895 555287692472988384314843)
      ·
        refine ⟨832931538709482576472265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555287692472988384314843 832931538709482576472265)
        ·
          refine ⟨624698654032111932354199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832931538709482576472265 624698654032111932354199)
          ·
            refine ⟨937047981048167898531299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624698654032111932354199 937047981048167898531299)
            ·
              refine ⟨1405571971572251847796949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937047981048167898531299 1405571971572251847796949)
              ·
                refine ⟨32943093083724652682741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1405571971572251847796949 32943093083724652682741)
                ·
                  refine ⟨3088414976599186189007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32943093083724652682741 3088414976599186189007)
                  ·
                    rfl

theorem cell22_27066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_27066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27066 prefixEnd_27066 := by exact prefixLift 27066
  have htrace : WordTrace (prefixWord ++ tailWord_27066) baseStart_27066 baseEnd_27066 := by
    simpa [prefixWord, tailWord_27066, baseEnd_27066] using wordTrace_append hprefix tailTrace_27066
  have hstable : (prefixWord ++ tailWord_27066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27066).length < 2 ^ (prefixWord ++ tailWord_27066).sum := by decide
  have hdescent : baseEnd_27066 < baseStart_27066 := by decide
  rcases family_descends (prefixWord ++ tailWord_27066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27096 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_27096 : Nat := 118140960795 + 27096 * 2 ^ 59
def prefixEnd_27096 : Nat := 4983230072969 + 3 ^ 40 * 27096 * 2
def baseEnd_27096 : Nat := 9275514542887480316929

theorem tailTrace_27096 : CollatzResearch.WordTrace tailWord_27096 prefixEnd_27096 9275514542887480316929 := by
  unfold tailWord_27096
  simp only [CollatzResearch.WordTrace]
  refine ⟨494136154921647236742571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 658848206562196315656761 494136154921647236742571)
  ·
    refine ⟨741204232382470855113857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494136154921647236742571 741204232382470855113857)
    ·
      refine ⟨555903174286853141335393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 741204232382470855113857 555903174286853141335393)
      ·
        refine ⟨416927380715139856001545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555903174286853141335393 416927380715139856001545)
        ·
          refine ⟨312695535536354892001159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416927380715139856001545 312695535536354892001159)
          ·
            refine ⟨469043303304532338001739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312695535536354892001159 469043303304532338001739)
            ·
              refine ⟨703564954956798507002609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469043303304532338001739 703564954956798507002609)
              ·
                refine ⟨527673716217598880251957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703564954956798507002609 527673716217598880251957)
                ·
                  refine ⟨49469410895399895023621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527673716217598880251957 49469410895399895023621)
                  ·
                    refine ⟨9275514542887480316929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49469410895399895023621 9275514542887480316929)
                    ·
                      rfl

theorem cell22_27096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_27096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27096 prefixEnd_27096 := by exact prefixLift 27096
  have htrace : WordTrace (prefixWord ++ tailWord_27096) baseStart_27096 baseEnd_27096 := by
    simpa [prefixWord, tailWord_27096, baseEnd_27096] using wordTrace_append hprefix tailTrace_27096
  have hstable : (prefixWord ++ tailWord_27096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27096).length < 2 ^ (prefixWord ++ tailWord_27096).sum := by decide
  have hdescent : baseEnd_27096 < baseStart_27096 := by decide
  rcases family_descends (prefixWord ++ tailWord_27096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27117 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 5]
def baseStart_27117 : Nat := 118140960795 + 27117 * 2 ^ 59
def prefixEnd_27117 : Nat := 4983230072969 + 3 ^ 40 * 27117 * 2
def baseEnd_27117 : Nat := 3094234424016808513955

theorem tailTrace_27117 : CollatzResearch.WordTrace tailWord_27117 prefixEnd_27117 3094234424016808513955 := by
  unfold tailWord_27117
  simp only [CollatzResearch.WordTrace]
  refine ⟨989038242767215059999605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 659358828511476706666403 989038242767215059999605)
  ·
    refine ⟨92722335259426411874963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 989038242767215059999605 92722335259426411874963)
    ·
      refine ⟨139083502889139617812445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92722335259426411874963 139083502889139617812445)
      ·
        refine ⟨52156313583427356679667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139083502889139617812445 52156313583427356679667)
        ·
          refine ⟨78234470375141035019501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52156313583427356679667 78234470375141035019501)
          ·
            refine ⟨29337926390677888132313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78234470375141035019501 29337926390677888132313)
            ·
              refine ⟨22003444793008416099235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29337926390677888132313 22003444793008416099235)
              ·
                refine ⟨33005167189512624148853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22003444793008416099235 33005167189512624148853)
                ·
                  refine ⟨3094234424016808513955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33005167189512624148853 3094234424016808513955)
                  ·
                    rfl

theorem cell22_27117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_27117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27117 prefixEnd_27117 := by exact prefixLift 27117
  have htrace : WordTrace (prefixWord ++ tailWord_27117) baseStart_27117 baseEnd_27117 := by
    simpa [prefixWord, tailWord_27117, baseEnd_27117] using wordTrace_append hprefix tailTrace_27117
  have hstable : (prefixWord ++ tailWord_27117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27117).length < 2 ^ (prefixWord ++ tailWord_27117).sum := by decide
  have hdescent : baseEnd_27117 < baseStart_27117 := by decide
  rcases family_descends (prefixWord ++ tailWord_27117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27141 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_27141 : Nat := 118140960795 + 27141 * 2 ^ 59
def prefixEnd_27141 : Nat := 4983230072969 + 3 ^ 40 * 27141 * 2
def baseEnd_27141 : Nat := 9290918962522362941791

theorem tailTrace_27141 : CollatzResearch.WordTrace tailWord_27141 prefixEnd_27141 9290918962522362941791 := by
  unfold tailWord_27141
  simp only [CollatzResearch.WordTrace]
  refine ⟨989913594680267158873277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 659942396453511439248851 989913594680267158873277)
  ·
    refine ⟨371217598005100184577479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 989913594680267158873277 371217598005100184577479)
    ·
      refine ⟨556826397007650276866219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371217598005100184577479 556826397007650276866219)
      ·
        refine ⟨835239595511475415299329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556826397007650276866219 835239595511475415299329)
        ·
          refine ⟨626429696633606561474497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835239595511475415299329 626429696633606561474497)
          ·
            refine ⟨469822272475204921105873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626429696633606561474497 469822272475204921105873)
            ·
              refine ⟨352366704356403690829405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469822272475204921105873 352366704356403690829405)
              ·
                refine ⟨132137514133651384061027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352366704356403690829405 132137514133651384061027)
                ·
                  refine ⟨198206271200477076091541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132137514133651384061027 198206271200477076091541)
                  ·
                    refine ⟨9290918962522362941791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 198206271200477076091541 9290918962522362941791)
                    ·
                      rfl

theorem cell22_27141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_27141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27141 prefixEnd_27141 := by exact prefixLift 27141
  have htrace : WordTrace (prefixWord ++ tailWord_27141) baseStart_27141 baseEnd_27141 := by
    simpa [prefixWord, tailWord_27141, baseEnd_27141] using wordTrace_append hprefix tailTrace_27141
  have hstable : (prefixWord ++ tailWord_27141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27141).length < 2 ^ (prefixWord ++ tailWord_27141).sum := by decide
  have hdescent : baseEnd_27141 < baseStart_27141 := by decide
  rcases family_descends (prefixWord ++ tailWord_27141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27160 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_27160 : Nat := 118140960795 + 27160 * 2 ^ 59
def prefixEnd_27160 : Nat := 4983230072969 + 3 ^ 40 * 27160 * 2
def baseEnd_27160 : Nat := 9297423050812646716733

theorem tailTrace_27160 : CollatzResearch.WordTrace tailWord_27160 prefixEnd_27160 9297423050812646716733 := by
  unfold tailWord_27160
  simp only [CollatzResearch.WordTrace]
  refine ⟨495303290805716701907467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 660404387740955602543289 495303290805716701907467)
  ·
    refine ⟨742954936208575052861201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 495303290805716701907467 742954936208575052861201)
    ·
      refine ⟨557216202156431289645901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742954936208575052861201 557216202156431289645901)
      ·
        refine ⟨208956075808661733617213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557216202156431289645901 208956075808661733617213)
        ·
          refine ⟨78358528428248150106455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208956075808661733617213 78358528428248150106455)
          ·
            refine ⟨117537792642372225159683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78358528428248150106455 117537792642372225159683)
            ·
              refine ⟨176306688963558337739525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117537792642372225159683 176306688963558337739525)
              ·
                refine ⟨33057504180667188326161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176306688963558337739525 33057504180667188326161)
                ·
                  refine ⟨24793128135500391244621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33057504180667188326161 24793128135500391244621)
                  ·
                    refine ⟨9297423050812646716733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24793128135500391244621 9297423050812646716733)
                    ·
                      rfl

theorem cell22_27160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_27160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27160 prefixEnd_27160 := by exact prefixLift 27160
  have htrace : WordTrace (prefixWord ++ tailWord_27160) baseStart_27160 baseEnd_27160 := by
    simpa [prefixWord, tailWord_27160, baseEnd_27160] using wordTrace_append hprefix tailTrace_27160
  have hstable : (prefixWord ++ tailWord_27160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27160).length < 2 ^ (prefixWord ++ tailWord_27160).sum := by decide
  have hdescent : baseEnd_27160 < baseStart_27160 := by decide
  rcases family_descends (prefixWord ++ tailWord_27160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27218 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_27218 : Nat := 118140960795 + 27218 * 2 ^ 59
def prefixEnd_27218 : Nat := 4983230072969 + 3 ^ 40 * 27218 * 2
def baseEnd_27218 : Nat := 3105759212039942922185

theorem tailTrace_27218 : CollatzResearch.WordTrace tailWord_27218 prefixEnd_27218 3105759212039942922185 := by
  unfold tailWord_27218
  simp only [CollatzResearch.WordTrace]
  refine ⟨248180503850327327356577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 661814676934206206284205 248180503850327327356577)
  ·
    refine ⟨186135377887745495517433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248180503850327327356577 186135377887745495517433)
    ·
      refine ⟨139601533415809121638075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186135377887745495517433 139601533415809121638075)
      ·
        refine ⟨209402300123713682457113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139601533415809121638075 209402300123713682457113)
        ·
          refine ⟨157051725092785261842835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209402300123713682457113 157051725092785261842835)
          ·
            refine ⟨235577587639177892764253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157051725092785261842835 235577587639177892764253)
            ·
              refine ⟨88341595364691709786595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235577587639177892764253 88341595364691709786595)
              ·
                refine ⟨132512393047037564679893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88341595364691709786595 132512393047037564679893)
                ·
                  refine ⟨3105759212039942922185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 132512393047037564679893 3105759212039942922185)
                  ·
                    rfl

theorem cell22_27218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_27218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27218 prefixEnd_27218 := by exact prefixLift 27218
  have htrace : WordTrace (prefixWord ++ tailWord_27218) baseStart_27218 baseEnd_27218 := by
    simpa [prefixWord, tailWord_27218, baseEnd_27218] using wordTrace_append hprefix tailTrace_27218
  have hstable : (prefixWord ++ tailWord_27218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27218).length < 2 ^ (prefixWord ++ tailWord_27218).sum := by decide
  have hdescent : baseEnd_27218 < baseStart_27218 := by decide
  rcases family_descends (prefixWord ++ tailWord_27218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27233 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_27233 : Nat := 118140960795 + 27233 * 2 ^ 59
def prefixEnd_27233 : Nat := 4983230072969 + 3 ^ 40 * 27233 * 2
def baseEnd_27233 : Nat := 9322412442664789641509

theorem tailTrace_27233 : CollatzResearch.WordTrace tailWord_27233 prefixEnd_27233 9322412442664789641509 := by
  unfold tailWord_27233
  simp only [CollatzResearch.WordTrace]
  refine ⟨993269110346966871222353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 662179406897977914148235 993269110346966871222353)
  ·
    refine ⟨744951832760225153416765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 993269110346966871222353 744951832760225153416765)
    ·
      refine ⟨279356937285084432531287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 744951832760225153416765 279356937285084432531287)
      ·
        refine ⟨419035405927626648796931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279356937285084432531287 419035405927626648796931)
        ·
          refine ⟨628553108891439973195397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419035405927626648796931 628553108891439973195397)
          ·
            refine ⟨117853707917144994974137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 628553108891439973195397 117853707917144994974137)
            ·
              refine ⟨88390280937858746230603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117853707917144994974137 88390280937858746230603)
              ·
                refine ⟨132585421406788119345905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88390280937858746230603 132585421406788119345905)
                ·
                  refine ⟨99439066055091089509429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132585421406788119345905 99439066055091089509429)
                  ·
                    refine ⟨9322412442664789641509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99439066055091089509429 9322412442664789641509)
                    ·
                      rfl

theorem cell22_27233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_27233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27233 prefixEnd_27233 := by exact prefixLift 27233
  have htrace : WordTrace (prefixWord ++ tailWord_27233) baseStart_27233 baseEnd_27233 := by
    simpa [prefixWord, tailWord_27233, baseEnd_27233] using wordTrace_append hprefix tailTrace_27233
  have hstable : (prefixWord ++ tailWord_27233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27233).length < 2 ^ (prefixWord ++ tailWord_27233).sum := by decide
  have hdescent : baseEnd_27233 < baseStart_27233 := by decide
  rcases family_descends (prefixWord ++ tailWord_27233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27235 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 5]
def baseStart_27235 : Nat := 118140960795 + 27235 * 2 ^ 59
def prefixEnd_27235 : Nat := 4983230072969 + 3 ^ 40 * 27235 * 2
def baseEnd_27235 : Nat := 3107699027845817030501

theorem tailTrace_27235 : CollatzResearch.WordTrace tailWord_27235 prefixEnd_27235 3107699027845817030501 := by
  unfold tailWord_27235
  simp only [CollatzResearch.WordTrace]
  refine ⟨993342056339721212795159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 662228037559814141863439 993342056339721212795159)
  ·
    refine ⟨1490013084509581819192739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993342056339721212795159 1490013084509581819192739)
    ·
      refine ⟨2235019626764372728789109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490013084509581819192739 2235019626764372728789109)
      ·
        refine ⟨209533090009159943323979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2235019626764372728789109 209533090009159943323979)
        ·
          refine ⟨314299635013739914985969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209533090009159943323979 314299635013739914985969)
          ·
            refine ⟨235724726260304936239477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314299635013739914985969 235724726260304936239477)
            ·
              refine ⟨22099193086903587772451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235724726260304936239477 22099193086903587772451)
              ·
                refine ⟨33148789630355381658677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22099193086903587772451 33148789630355381658677)
                ·
                  refine ⟨3107699027845817030501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33148789630355381658677 3107699027845817030501)
                  ·
                    rfl

theorem cell22_27235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 5].length) (baseStart_27235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27235 prefixEnd_27235 := by exact prefixLift 27235
  have htrace : WordTrace (prefixWord ++ tailWord_27235) baseStart_27235 baseEnd_27235 := by
    simpa [prefixWord, tailWord_27235, baseEnd_27235] using wordTrace_append hprefix tailTrace_27235
  have hstable : (prefixWord ++ tailWord_27235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27235).length < 2 ^ (prefixWord ++ tailWord_27235).sum := by decide
  have hdescent : baseEnd_27235 < baseStart_27235 := by decide
  rcases family_descends (prefixWord ++ tailWord_27235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27265 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_27265 : Nat := 118140960795 + 27265 * 2 ^ 59
def prefixEnd_27265 : Nat := 4983230072969 + 3 ^ 40 * 27265 * 2
def baseEnd_27265 : Nat := 9333366696627372841411

theorem tailTrace_27265 : CollatzResearch.WordTrace tailWord_27265 prefixEnd_27265 9333366696627372841411 := by
  unfold tailWord_27265
  simp only [CollatzResearch.WordTrace]
  refine ⟨994436246231036336387249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 662957497487357557591499 994436246231036336387249)
  ·
    refine ⟨745827184673277252290437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 994436246231036336387249 745827184673277252290437)
    ·
      refine ⟨139842597126239484804457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 745827184673277252290437 139842597126239484804457)
      ·
        refine ⟨104881947844679613603343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139842597126239484804457 104881947844679613603343)
        ·
          refine ⟨157322921767019420405015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104881947844679613603343 157322921767019420405015)
          ·
            refine ⟨235984382650529130607523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157322921767019420405015 235984382650529130607523)
            ·
              refine ⟨353976573975793695911285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235984382650529130607523 353976573975793695911285)
              ·
                refine ⟨33185303810230658991683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353976573975793695911285 33185303810230658991683)
                ·
                  refine ⟨49777955715345988487525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33185303810230658991683 49777955715345988487525)
                  ·
                    refine ⟨9333366696627372841411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49777955715345988487525 9333366696627372841411)
                    ·
                      rfl

theorem cell22_27265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_27265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27265 prefixEnd_27265 := by exact prefixLift 27265
  have htrace : WordTrace (prefixWord ++ tailWord_27265) baseStart_27265 baseEnd_27265 := by
    simpa [prefixWord, tailWord_27265, baseEnd_27265] using wordTrace_append hprefix tailTrace_27265
  have hstable : (prefixWord ++ tailWord_27265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27265).length < 2 ^ (prefixWord ++ tailWord_27265).sum := by decide
  have hdescent : baseEnd_27265 < baseStart_27265 := by decide
  rcases family_descends (prefixWord ++ tailWord_27265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27293 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_27293 : Nat := 118140960795 + 27293 * 2 ^ 59
def prefixEnd_27293 : Nat := 4983230072969 + 3 ^ 40 * 27293 * 2
def baseEnd_27293 : Nat := 9342951668844633141325

theorem tailTrace_27293 : CollatzResearch.WordTrace tailWord_27293 prefixEnd_27293 9342951668844633141325 := by
  unfold tailWord_27293
  simp only [CollatzResearch.WordTrace]
  refine ⟨995457490129597118406533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 663638326753064745604355 995457490129597118406533)
  ·
    refine ⟨186648279399299459701225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 995457490129597118406533 186648279399299459701225)
    ·
      refine ⟨139986209549474594775919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186648279399299459701225 139986209549474594775919)
      ·
        refine ⟨209979314324211892163879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139986209549474594775919 209979314324211892163879)
        ·
          refine ⟨314968971486317838245819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209979314324211892163879 314968971486317838245819)
          ·
            refine ⟨472453457229476757368729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314968971486317838245819 472453457229476757368729)
            ·
              refine ⟨354340092922107568026547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472453457229476757368729 354340092922107568026547)
              ·
                refine ⟨531510139383161352039821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354340092922107568026547 531510139383161352039821)
                ·
                  refine ⟨199316302268685507014933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531510139383161352039821 199316302268685507014933)
                  ·
                    refine ⟨9342951668844633141325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 199316302268685507014933 9342951668844633141325)
                    ·
                      rfl

theorem cell22_27293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_27293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27293 prefixEnd_27293 := by exact prefixLift 27293
  have htrace : WordTrace (prefixWord ++ tailWord_27293) baseStart_27293 baseEnd_27293 := by
    simpa [prefixWord, tailWord_27293, baseEnd_27293] using wordTrace_append hprefix tailTrace_27293
  have hstable : (prefixWord ++ tailWord_27293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27293).length < 2 ^ (prefixWord ++ tailWord_27293).sum := by decide
  have hdescent : baseEnd_27293 < baseStart_27293 := by decide
  rcases family_descends (prefixWord ++ tailWord_27293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27374 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_27374 : Nat := 118140960795 + 27374 * 2 ^ 59
def prefixEnd_27374 : Nat := 4983230072969 + 3 ^ 40 * 27374 * 2
def baseEnd_27374 : Nat := 9370679624187421866077

theorem tailTrace_27374 : CollatzResearch.WordTrace tailWord_27374 prefixEnd_27374 9370679624187421866077 := by
  unfold tailWord_27374
  simp only [CollatzResearch.WordTrace]
  refine ⟨124801475354518494013147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 665607868557431968070117 124801475354518494013147)
  ·
    refine ⟨187202213031777741019721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124801475354518494013147 187202213031777741019721)
    ·
      refine ⟨140401659773833305764791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187202213031777741019721 140401659773833305764791)
      ·
        refine ⟨210602489660749958647187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140401659773833305764791 210602489660749958647187)
        ·
          refine ⟨315903734491124937970781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210602489660749958647187 315903734491124937970781)
          ·
            refine ⟨118463900434171851739043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315903734491124937970781 118463900434171851739043)
            ·
              refine ⟨177695850651257777608565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118463900434171851739043 177695850651257777608565)
              ·
                refine ⟨16658985998555416650803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177695850651257777608565 16658985998555416650803)
                ·
                  refine ⟨24988478997833124976205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16658985998555416650803 24988478997833124976205)
                  ·
                    refine ⟨9370679624187421866077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24988478997833124976205 9370679624187421866077)
                    ·
                      rfl

theorem cell22_27374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_27374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27374 prefixEnd_27374 := by exact prefixLift 27374
  have htrace : WordTrace (prefixWord ++ tailWord_27374) baseStart_27374 baseEnd_27374 := by
    simpa [prefixWord, tailWord_27374, baseEnd_27374] using wordTrace_append hprefix tailTrace_27374
  have hstable : (prefixWord ++ tailWord_27374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27374).length < 2 ^ (prefixWord ++ tailWord_27374).sum := by decide
  have hdescent : baseEnd_27374 < baseStart_27374 := by decide
  rcases family_descends (prefixWord ++ tailWord_27374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27380 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_27380 : Nat := 118140960795 + 27380 * 2 ^ 59
def prefixEnd_27380 : Nat := 4983230072969 + 3 ^ 40 * 27380 * 2
def baseEnd_27380 : Nat := 9372733546805406216059

theorem tailTrace_27380 : CollatzResearch.WordTrace tailWord_27380 prefixEnd_27380 9372733546805406216059 := by
  unfold tailWord_27380
  simp only [CollatzResearch.WordTrace]
  refine ⟨499315320407205488411797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 665753760542940651215729 499315320407205488411797)
  ·
    refine ⟨23405405644087757269303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 499315320407205488411797 23405405644087757269303)
    ·
      refine ⟨35108108466131635903955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23405405644087757269303 35108108466131635903955)
      ·
        refine ⟨52662162699197453855933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35108108466131635903955 52662162699197453855933)
        ·
          refine ⟨19748311012199045195975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52662162699197453855933 19748311012199045195975)
          ·
            refine ⟨29622466518298567793963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19748311012199045195975 29622466518298567793963)
            ·
              refine ⟨44433699777447851690945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29622466518298567793963 44433699777447851690945)
              ·
                refine ⟨33325274833085888768209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44433699777447851690945 33325274833085888768209)
                ·
                  refine ⟨24993956124814416576157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33325274833085888768209 24993956124814416576157)
                  ·
                    refine ⟨9372733546805406216059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24993956124814416576157 9372733546805406216059)
                    ·
                      rfl

theorem cell22_27380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_27380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27380 prefixEnd_27380 := by exact prefixLift 27380
  have htrace : WordTrace (prefixWord ++ tailWord_27380) baseStart_27380 baseEnd_27380 := by
    simpa [prefixWord, tailWord_27380, baseEnd_27380] using wordTrace_append hprefix tailTrace_27380
  have hstable : (prefixWord ++ tailWord_27380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27380).length < 2 ^ (prefixWord ++ tailWord_27380).sum := by decide
  have hdescent : baseEnd_27380 < baseStart_27380 := by decide
  rcases family_descends (prefixWord ++ tailWord_27380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27447 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 2, 3]
def baseStart_27447 : Nat := 118140960795 + 27447 * 2 ^ 59
def prefixEnd_27447 : Nat := 4983230072969 + 3 ^ 40 * 27447 * 2
def baseEnd_27447 : Nat := 9395669016039564790853

theorem tailTrace_27447 : CollatzResearch.WordTrace tailWord_27447 prefixEnd_27447 9395669016039564790853 := by
  unfold tailWord_27447
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001074331571681419512595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 667382887714454279675063 1001074331571681419512595)
  ·
    refine ⟨1501611497357522129268893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001074331571681419512595 1501611497357522129268893)
    ·
      refine ⟨563104311509070798475835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1501611497357522129268893 563104311509070798475835)
      ·
        refine ⟨844656467263606197713753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563104311509070798475835 844656467263606197713753)
        ·
          refine ⟨633492350447704648285315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 844656467263606197713753 633492350447704648285315)
          ·
            refine ⟨950238525671556972427973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633492350447704648285315 950238525671556972427973)
            ·
              refine ⟨178169723563416932330245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 950238525671556972427973 178169723563416932330245)
              ·
                refine ⟨33406823168140674811921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178169723563416932330245 33406823168140674811921)
                ·
                  refine ⟨25055117376105506108941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33406823168140674811921 25055117376105506108941)
                  ·
                    refine ⟨9395669016039564790853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25055117376105506108941 9395669016039564790853)
                    ·
                      rfl

theorem cell22_27447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_27447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27447 prefixEnd_27447 := by exact prefixLift 27447
  have htrace : WordTrace (prefixWord ++ tailWord_27447) baseStart_27447 baseEnd_27447 := by
    simpa [prefixWord, tailWord_27447, baseEnd_27447] using wordTrace_append hprefix tailTrace_27447
  have hstable : (prefixWord ++ tailWord_27447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27447).length < 2 ^ (prefixWord ++ tailWord_27447).sum := by decide
  have hdescent : baseEnd_27447 < baseStart_27447 := by decide
  rcases family_descends (prefixWord ++ tailWord_27447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27633 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 2, 3]
def baseStart_27633 : Nat := 118140960795 + 27633 * 2 ^ 59
def prefixEnd_27633 : Nat := 4983230072969 + 3 ^ 40 * 27633 * 2
def baseEnd_27633 : Nat := 9459340617197079640283

theorem tailTrace_27633 : CollatzResearch.WordTrace tailWord_27633 prefixEnd_27633 9459340617197079640283 := by
  unfold tailWord_27633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007858308897835185783553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 671905539265223457189035 1007858308897835185783553)
  ·
    refine ⟨755893731673376389337665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1007858308897835185783553 755893731673376389337665)
    ·
      refine ⟨566920298755032292003249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755893731673376389337665 566920298755032292003249)
      ·
        refine ⟨425190224066274219002437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566920298755032292003249 425190224066274219002437)
        ·
          refine ⟨79723167012426416062957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425190224066274219002437 79723167012426416062957)
          ·
            refine ⟨29896187629659906023609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79723167012426416062957 29896187629659906023609)
            ·
              refine ⟨22422140722244929517707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29896187629659906023609 22422140722244929517707)
              ·
                refine ⟨33633211083367394276561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22422140722244929517707 33633211083367394276561)
                ·
                  refine ⟨25224908312525545707421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33633211083367394276561 25224908312525545707421)
                  ·
                    refine ⟨9459340617197079640283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25224908312525545707421 9459340617197079640283)
                    ·
                      rfl

theorem cell22_27633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_27633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27633 prefixEnd_27633 := by exact prefixLift 27633
  have htrace : WordTrace (prefixWord ++ tailWord_27633) baseStart_27633 baseEnd_27633 := by
    simpa [prefixWord, tailWord_27633, baseEnd_27633] using wordTrace_append hprefix tailTrace_27633
  have hstable : (prefixWord ++ tailWord_27633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27633).length < 2 ^ (prefixWord ++ tailWord_27633).sum := by decide
  have hdescent : baseEnd_27633 < baseStart_27633 := by decide
  rcases family_descends (prefixWord ++ tailWord_27633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27674 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_27674 : Nat := 118140960795 + 27674 * 2 ^ 59
def prefixEnd_27674 : Nat := 4983230072969 + 3 ^ 40 * 27674 * 2
def baseEnd_27674 : Nat := 3157791918362213121719

theorem tailTrace_27674 : CollatzResearch.WordTrace tailWord_27674 prefixEnd_27674 3157791918362213121719 := by
  unfold tailWord_27674
  simp only [CollatzResearch.WordTrace]
  refine ⟨252338425437324797006519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 672902467832866125350717 252338425437324797006519)
  ·
    refine ⟨378507638155987195509779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252338425437324797006519 378507638155987195509779)
    ·
      refine ⟨567761457233980793264669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378507638155987195509779 567761457233980793264669)
      ·
        refine ⟨212910546462742797474251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 567761457233980793264669 212910546462742797474251)
        ·
          refine ⟨319365819694114196211377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212910546462742797474251 319365819694114196211377)
          ·
            refine ⟨239524364770585647158533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319365819694114196211377 239524364770585647158533)
            ·
              refine ⟨44910818394484808842225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239524364770585647158533 44910818394484808842225)
              ·
                refine ⟨33683113795863606631669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44910818394484808842225 33683113795863606631669)
                ·
                  refine ⟨3157791918362213121719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33683113795863606631669 3157791918362213121719)
                  ·
                    rfl

theorem cell22_27674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_27674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27674 prefixEnd_27674 := by exact prefixLift 27674
  have htrace : WordTrace (prefixWord ++ tailWord_27674) baseStart_27674 baseEnd_27674 := by
    simpa [prefixWord, tailWord_27674, baseEnd_27674] using wordTrace_append hprefix tailTrace_27674
  have hstable : (prefixWord ++ tailWord_27674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27674).length < 2 ^ (prefixWord ++ tailWord_27674).sum := by decide
  have hdescent : baseEnd_27674 < baseStart_27674 := by decide
  rcases family_descends (prefixWord ++ tailWord_27674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27704 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_27704 : Nat := 118140960795 + 27704 * 2 ^ 59
def prefixEnd_27704 : Nat := 4983230072969 + 3 ^ 40 * 27704 * 2
def baseEnd_27704 : Nat := 9483645368176561115065

theorem tailTrace_27704 : CollatzResearch.WordTrace tailWord_27704 prefixEnd_27704 9483645368176561115065 := by
  unfold tailWord_27704
  simp only [CollatzResearch.WordTrace]
  refine ⟨505223945820307155809083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 673631927760409541078777 505223945820307155809083)
  ·
    refine ⟨757835918730460733713625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 505223945820307155809083 757835918730460733713625)
    ·
      refine ⟨568376939047845550285219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 757835918730460733713625 568376939047845550285219)
      ·
        refine ⟨852565408571768325427829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568376939047845550285219 852565408571768325427829)
        ·
          refine ⟨79928007053603280508859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 852565408571768325427829 79928007053603280508859)
          ·
            refine ⟨119892010580404920763289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79928007053603280508859 119892010580404920763289)
            ·
              refine ⟨89919007935303690572467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119892010580404920763289 89919007935303690572467)
              ·
                refine ⟨134878511902955535858701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89919007935303690572467 134878511902955535858701)
                ·
                  refine ⟨50579441963608325947013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134878511902955535858701 50579441963608325947013)
                  ·
                    refine ⟨9483645368176561115065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50579441963608325947013 9483645368176561115065)
                    ·
                      rfl

theorem cell22_27704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_27704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27704 prefixEnd_27704 := by exact prefixLift 27704
  have htrace : WordTrace (prefixWord ++ tailWord_27704) baseStart_27704 baseEnd_27704 := by
    simpa [prefixWord, tailWord_27704, baseEnd_27704] using wordTrace_append hprefix tailTrace_27704
  have hstable : (prefixWord ++ tailWord_27704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27704).length < 2 ^ (prefixWord ++ tailWord_27704).sum := by decide
  have hdescent : baseEnd_27704 < baseStart_27704 := by decide
  rcases family_descends (prefixWord ++ tailWord_27704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27747 : List Nat := [1, 1, 1, 5, 1, 1, 1, 11]
def baseStart_27747 : Nat := 118140960795 + 27747 * 2 ^ 59
def prefixEnd_27747 : Nat := 4983230072969 + 3 ^ 40 * 27747 * 2
def baseEnd_27747 : Nat := 1055373905215420254437

theorem tailTrace_27747 : CollatzResearch.WordTrace tailWord_27747 prefixEnd_27747 1055373905215420254437 := by
  unfold tailWord_27747
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012016230484832655433495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 674677486989888436955663 1012016230484832655433495)
  ·
    refine ⟨1518024345727248983150243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012016230484832655433495 1518024345727248983150243)
    ·
      refine ⟨2277036518590873474725365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518024345727248983150243 2277036518590873474725365)
      ·
        refine ⟨213472173617894388255503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2277036518590873474725365 213472173617894388255503)
        ·
          refine ⟨320208260426841582383255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213472173617894388255503 320208260426841582383255)
          ·
            refine ⟨480312390640262373574883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320208260426841582383255 480312390640262373574883)
            ·
              refine ⟨720468585960393560362325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480312390640262373574883 720468585960393560362325)
              ·
                refine ⟨1055373905215420254437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 720468585960393560362325 1055373905215420254437)
                ·
                  rfl

theorem cell22_27747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 11].length) (baseStart_27747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27747 prefixEnd_27747 := by exact prefixLift 27747
  have htrace : WordTrace (prefixWord ++ tailWord_27747) baseStart_27747 baseEnd_27747 := by
    simpa [prefixWord, tailWord_27747, baseEnd_27747] using wordTrace_append hprefix tailTrace_27747
  have hstable : (prefixWord ++ tailWord_27747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27747).length < 2 ^ (prefixWord ++ tailWord_27747).sum := by decide
  have hdescent : baseEnd_27747 < baseStart_27747 := by decide
  rcases family_descends (prefixWord ++ tailWord_27747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27751 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 1, 5]
def baseStart_27751 : Nat := 118140960795 + 27751 * 2 ^ 59
def prefixEnd_27751 : Nat := 4983230072969 + 3 ^ 40 * 27751 * 2
def baseEnd_27751 : Nat := 9499734428684105189921

theorem tailTrace_27751 : CollatzResearch.WordTrace tailWord_27751 prefixEnd_27751 9499734428684105189921 := by
  unfold tailWord_27751
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012162122470341338579107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 674774748313560892386071 1012162122470341338579107)
  ·
    refine ⟨1518243183705512007868661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012162122470341338579107 1518243183705512007868661)
    ·
      refine ⟨142335298472391750737687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1518243183705512007868661 142335298472391750737687)
      ·
        refine ⟨213502947708587626106531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142335298472391750737687 213502947708587626106531)
        ·
          refine ⟨320254421562881439159797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213502947708587626106531 320254421562881439159797)
          ·
            refine ⟨30023852021520134921231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320254421562881439159797 30023852021520134921231)
            ·
              refine ⟨45035778032280202381847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30023852021520134921231 45035778032280202381847)
              ·
                refine ⟨67553667048420303572771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45035778032280202381847 67553667048420303572771)
                ·
                  refine ⟨101330500572630455359157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67553667048420303572771 101330500572630455359157)
                  ·
                    refine ⟨9499734428684105189921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101330500572630455359157 9499734428684105189921)
                    ·
                      rfl

theorem cell22_27751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_27751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27751 prefixEnd_27751 := by exact prefixLift 27751
  have htrace : WordTrace (prefixWord ++ tailWord_27751) baseStart_27751 baseEnd_27751 := by
    simpa [prefixWord, tailWord_27751, baseEnd_27751] using wordTrace_append hprefix tailTrace_27751
  have hstable : (prefixWord ++ tailWord_27751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27751).length < 2 ^ (prefixWord ++ tailWord_27751).sum := by decide
  have hdescent : baseEnd_27751 < baseStart_27751 := by decide
  rcases family_descends (prefixWord ++ tailWord_27751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27766 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_27766 : Nat := 118140960795 + 27766 * 2 ^ 59
def prefixEnd_27766 : Nat := 4983230072969 + 3 ^ 40 * 27766 * 2
def baseEnd_27766 : Nat := 9504869235229066064875

theorem tailTrace_27766 : CollatzResearch.WordTrace tailWord_27766 prefixEnd_27766 9504869235229066064875 := by
  unfold tailWord_27766
  simp only [CollatzResearch.WordTrace]
  refine ⟨63294326088499931273447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 675139478277332600250101 63294326088499931273447)
  ·
    refine ⟨94941489132749896910171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63294326088499931273447 94941489132749896910171)
    ·
      refine ⟨142412233699124845365257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94941489132749896910171 142412233699124845365257)
      ·
        refine ⟨106809175274343634023943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142412233699124845365257 106809175274343634023943)
        ·
          refine ⟨160213762911515451035915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106809175274343634023943 160213762911515451035915)
          ·
            refine ⟨240320644367273176553873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160213762911515451035915 240320644367273176553873)
            ·
              refine ⟨180240483275454882415405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240320644367273176553873 180240483275454882415405)
              ·
                refine ⟨67590181228295580905777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180240483275454882415405 67590181228295580905777)
                ·
                  refine ⟨50692635921221685679333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67590181228295580905777 50692635921221685679333)
                  ·
                    refine ⟨9504869235229066064875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50692635921221685679333 9504869235229066064875)
                    ·
                      rfl

theorem cell22_27766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_27766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27766 prefixEnd_27766 := by exact prefixLift 27766
  have htrace : WordTrace (prefixWord ++ tailWord_27766) baseStart_27766 baseEnd_27766 := by
    simpa [prefixWord, tailWord_27766, baseEnd_27766] using wordTrace_append hprefix tailTrace_27766
  have hstable : (prefixWord ++ tailWord_27766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27766).length < 2 ^ (prefixWord ++ tailWord_27766).sum := by decide
  have hdescent : baseEnd_27766 < baseStart_27766 := by decide
  rcases family_descends (prefixWord ++ tailWord_27766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27781 : List Nat := [1, 3, 1, 1, 7, 1, 8]
def baseStart_27781 : Nat := 118140960795 + 27781 * 2 ^ 59
def prefixEnd_27781 : Nat := 4983230072969 + 3 ^ 40 * 27781 * 2
def baseEnd_27781 : Nat := 352222371917556553327

theorem tailTrace_27781 : CollatzResearch.WordTrace tailWord_27781 prefixEnd_27781 352222371917556553327 := by
  unfold tailWord_27781
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013256312361656462171197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 675504208241104308114131 1013256312361656462171197)
  ·
    refine ⟨379971117135621173314199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1013256312361656462171197 379971117135621173314199)
    ·
      refine ⟨569956675703431759971299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379971117135621173314199 569956675703431759971299)
      ·
        refine ⟨854935013555147639956949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569956675703431759971299 854935013555147639956949)
        ·
          refine ⟨20037539380198772811491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 854935013555147639956949 20037539380198772811491)
          ·
            refine ⟨30056309070298159217237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20037539380198772811491 30056309070298159217237)
            ·
              refine ⟨352222371917556553327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 30056309070298159217237 352222371917556553327)
              ·
                rfl

theorem cell22_27781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 8].length) (baseStart_27781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27781 prefixEnd_27781 := by exact prefixLift 27781
  have htrace : WordTrace (prefixWord ++ tailWord_27781) baseStart_27781 baseEnd_27781 := by
    simpa [prefixWord, tailWord_27781, baseEnd_27781] using wordTrace_append hprefix tailTrace_27781
  have hstable : (prefixWord ++ tailWord_27781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27781).length < 2 ^ (prefixWord ++ tailWord_27781).sum := by decide
  have hdescent : baseEnd_27781 < baseStart_27781 := by decide
  rcases family_descends (prefixWord ++ tailWord_27781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27886 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_27886 : Nat := 118140960795 + 27886 * 2 ^ 59
def prefixEnd_27886 : Nat := 4983230072969 + 3 ^ 40 * 27886 * 2
def baseEnd_27886 : Nat := 9545947687588753064507

theorem tailTrace_27886 : CollatzResearch.WordTrace tailWord_27886 prefixEnd_27886 9545947687588753064507 := by
  unfold tailWord_27886
  simp only [CollatzResearch.WordTrace]
  refine ⟨127135747122657424342939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 678057317987506263162341 127135747122657424342939)
  ·
    refine ⟨190703620683986136514409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127135747122657424342939 190703620683986136514409)
    ·
      refine ⟨143027715512989602385807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190703620683986136514409 143027715512989602385807)
      ·
        refine ⟨214541573269484403578711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143027715512989602385807 214541573269484403578711)
        ·
          refine ⟨321812359904226605368067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214541573269484403578711 321812359904226605368067)
          ·
            refine ⟨482718539856339908052101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321812359904226605368067 482718539856339908052101)
            ·
              refine ⟨90509726223063732759769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 482718539856339908052101 90509726223063732759769)
              ·
                refine ⟨67882294667297799569827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90509726223063732759769 67882294667297799569827)
                ·
                  refine ⟨101823442000946699354741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67882294667297799569827 101823442000946699354741)
                  ·
                    refine ⟨9545947687588753064507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101823442000946699354741 9545947687588753064507)
                    ·
                      rfl

theorem cell22_27886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_27886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27886 prefixEnd_27886 := by exact prefixLift 27886
  have htrace : WordTrace (prefixWord ++ tailWord_27886) baseStart_27886 baseEnd_27886 := by
    simpa [prefixWord, tailWord_27886, baseEnd_27886] using wordTrace_append hprefix tailTrace_27886
  have hstable : (prefixWord ++ tailWord_27886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27886).length < 2 ^ (prefixWord ++ tailWord_27886).sum := by decide
  have hdescent : baseEnd_27886 < baseStart_27886 := by decide
  rcases family_descends (prefixWord ++ tailWord_27886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27903 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 2, 3]
def baseStart_27903 : Nat := 118140960795 + 27903 * 2 ^ 59
def prefixEnd_27903 : Nat := 4983230072969 + 3 ^ 40 * 27903 * 2
def baseEnd_27903 : Nat := 9551767135006375389455

theorem tailTrace_27903 : CollatzResearch.WordTrace tailWord_27903 prefixEnd_27903 9551767135006375389455 := by
  unfold tailWord_27903
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017706017919671298112363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 678470678613114198741575 1017706017919671298112363)
  ·
    refine ⟨1526559026879506947168545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1017706017919671298112363 1526559026879506947168545)
    ·
      refine ⟨1144919270159630210376409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1526559026879506947168545 1144919270159630210376409)
      ·
        refine ⟨858689452619722657782307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1144919270159630210376409 858689452619722657782307)
        ·
          refine ⟨1288034178929583986673461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858689452619722657782307 1288034178929583986673461)
          ·
            refine ⟨120753204274648498750637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1288034178929583986673461 120753204274648498750637)
            ·
              refine ⟨45282451602993187031489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120753204274648498750637 45282451602993187031489)
              ·
                refine ⟨33961838702244890273617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45282451602993187031489 33961838702244890273617)
                ·
                  refine ⟨25471379026683667705213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33961838702244890273617 25471379026683667705213)
                  ·
                    refine ⟨9551767135006375389455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25471379026683667705213 9551767135006375389455)
                    ·
                      rfl

theorem cell22_27903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_27903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27903 prefixEnd_27903 := by exact prefixLift 27903
  have htrace : WordTrace (prefixWord ++ tailWord_27903) baseStart_27903 baseEnd_27903 := by
    simpa [prefixWord, tailWord_27903, baseEnd_27903] using wordTrace_append hprefix tailTrace_27903
  have hstable : (prefixWord ++ tailWord_27903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27903).length < 2 ^ (prefixWord ++ tailWord_27903).sum := by decide
  have hdescent : baseEnd_27903 < baseStart_27903 := by decide
  rcases family_descends (prefixWord ++ tailWord_27903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27933 : List Nat := [1, 4, 2, 3, 1, 1, 4, 6]
def baseStart_27933 : Nat := 118140960795 + 27933 * 2 ^ 59
def prefixEnd_27933 : Nat := 4983230072969 + 3 ^ 40 * 27933 * 2
def baseEnd_27933 : Nat := 1062448527566255237707

theorem tailTrace_27933 : CollatzResearch.WordTrace tailWord_27933 prefixEnd_27933 1062448527566255237707 := by
  unfold tailWord_27933
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018800207810986421704453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 679200138540657614469635 1018800207810986421704453)
  ·
    refine ⟨191025038964559954069585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1018800207810986421704453 191025038964559954069585)
    ·
      refine ⟨143268779223419965552189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191025038964559954069585 143268779223419965552189)
      ·
        refine ⟨53725792208782487082071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143268779223419965552189 53725792208782487082071)
        ·
          refine ⟨80588688313173730623107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53725792208782487082071 80588688313173730623107)
          ·
            refine ⟨120883032469760595934661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80588688313173730623107 120883032469760595934661)
            ·
              refine ⟨22665568588080111737749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120883032469760595934661 22665568588080111737749)
              ·
                refine ⟨1062448527566255237707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22665568588080111737749 1062448527566255237707)
                ·
                  rfl

theorem cell22_27933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 6].length) (baseStart_27933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_27933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_27933 prefixEnd_27933 := by exact prefixLift 27933
  have htrace : WordTrace (prefixWord ++ tailWord_27933) baseStart_27933 baseEnd_27933 := by
    simpa [prefixWord, tailWord_27933, baseEnd_27933] using wordTrace_append hprefix tailTrace_27933
  have hstable : (prefixWord ++ tailWord_27933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27933).length < 2 ^ (prefixWord ++ tailWord_27933).sum := by decide
  have hdescent : baseEnd_27933 < baseStart_27933 := by decide
  rcases family_descends (prefixWord ++ tailWord_27933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28023 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 4]
def baseStart_28023 : Nat := 118140960795 + 28023 * 2 ^ 59
def prefixEnd_28023 : Nat := 4983230072969 + 3 ^ 40 * 28023 * 2
def baseEnd_28023 : Nat := 3197615195788687463029

theorem tailTrace_28023 : CollatzResearch.WordTrace tailWord_28023 prefixEnd_28023 3197615195788687463029 := by
  unfold tailWord_28023
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022082777484931792480723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 681388518323287861653815 1022082777484931792480723)
  ·
    refine ⟨1533124166227397688721085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022082777484931792480723 1533124166227397688721085)
    ·
      refine ⟨574921562335274133270407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1533124166227397688721085 574921562335274133270407)
      ·
        refine ⟨862382343502911199905611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574921562335274133270407 862382343502911199905611)
        ·
          refine ⟨1293573515254366799858417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862382343502911199905611 1293573515254366799858417)
          ·
            refine ⟨970180136440775099893813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293573515254366799858417 970180136440775099893813)
            ·
              refine ⟨90954387791322665615045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 970180136440775099893813 90954387791322665615045)
              ·
                refine ⟨17053947710872999802821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90954387791322665615045 17053947710872999802821)
                ·
                  refine ⟨3197615195788687463029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17053947710872999802821 3197615195788687463029)
                  ·
                    rfl

theorem cell22_28023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 4].length) (baseStart_28023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28023 prefixEnd_28023 := by exact prefixLift 28023
  have htrace : WordTrace (prefixWord ++ tailWord_28023) baseStart_28023 baseEnd_28023 := by
    simpa [prefixWord, tailWord_28023, baseEnd_28023] using wordTrace_append hprefix tailTrace_28023
  have hstable : (prefixWord ++ tailWord_28023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28023).length < 2 ^ (prefixWord ++ tailWord_28023).sum := by decide
  have hdescent : baseEnd_28023 < baseStart_28023 := by decide
  rcases family_descends (prefixWord ++ tailWord_28023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28053 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_28053 : Nat := 118140960795 + 28053 * 2 ^ 59
def prefixEnd_28053 : Nat := 4983230072969 + 3 ^ 40 * 28053 * 2
def baseEnd_28053 : Nat := 9603115200455984138995

theorem tailTrace_28053 : CollatzResearch.WordTrace tailWord_28053 prefixEnd_28053 9603115200455984138995 := by
  unfold tailWord_28053
  simp only [CollatzResearch.WordTrace]
  refine ⟨1023176967376246916072813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 682117978250831277381875 1023176967376246916072813)
  ·
    refine ⟨383691362766092593527305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1023176967376246916072813 383691362766092593527305)
    ·
      refine ⟨287768522074569445145479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383691362766092593527305 287768522074569445145479)
      ·
        refine ⟨431652783111854167718219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287768522074569445145479 431652783111854167718219)
        ·
          refine ⟨647479174667781251577329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431652783111854167718219 647479174667781251577329)
          ·
            refine ⟨485609381000835938682997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647479174667781251577329 485609381000835938682997)
            ·
              refine ⟨45525879468828369251531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 485609381000835938682997 45525879468828369251531)
              ·
                refine ⟨68288819203242553877297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45525879468828369251531 68288819203242553877297)
                ·
                  refine ⟨51216614402431915407973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68288819203242553877297 51216614402431915407973)
                  ·
                    refine ⟨9603115200455984138995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51216614402431915407973 9603115200455984138995)
                    ·
                      rfl

theorem cell22_28053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_28053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28053 prefixEnd_28053 := by exact prefixLift 28053
  have htrace : WordTrace (prefixWord ++ tailWord_28053) baseStart_28053 baseEnd_28053 := by
    simpa [prefixWord, tailWord_28053, baseEnd_28053] using wordTrace_append hprefix tailTrace_28053
  have hstable : (prefixWord ++ tailWord_28053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28053).length < 2 ^ (prefixWord ++ tailWord_28053).sum := by decide
  have hdescent : baseEnd_28053 < baseStart_28053 := by decide
  rcases family_descends (prefixWord ++ tailWord_28053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28072 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_28072 : Nat := 118140960795 + 28072 * 2 ^ 59
def prefixEnd_28072 : Nat := 4983230072969 + 3 ^ 40 * 28072 * 2
def baseEnd_28072 : Nat := 9609619288746267913937

theorem tailTrace_28072 : CollatzResearch.WordTrace tailWord_28072 prefixEnd_28072 9609619288746267913937 := by
  unfold tailWord_28072
  simp only [CollatzResearch.WordTrace]
  refine ⟨511934977153706580507235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 682579969538275440676313 511934977153706580507235)
  ·
    refine ⟨767902465730559870760853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511934977153706580507235 767902465730559870760853)
    ·
      refine ⟨35995428081119993941915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 767902465730559870760853 35995428081119993941915)
      ·
        refine ⟨53993142121679990912873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35995428081119993941915 53993142121679990912873)
        ·
          refine ⟨40494856591259993184655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53993142121679990912873 40494856591259993184655)
          ·
            refine ⟨60742284886889989776983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40494856591259993184655 60742284886889989776983)
            ·
              refine ⟨91113427330334984665475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60742284886889989776983 91113427330334984665475)
              ·
                refine ⟨136670140995502476998213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91113427330334984665475 136670140995502476998213)
                ·
                  refine ⟨25625651436656714437165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136670140995502476998213 25625651436656714437165)
                  ·
                    refine ⟨9609619288746267913937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25625651436656714437165 9609619288746267913937)
                    ·
                      rfl

theorem cell22_28072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_28072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28072 prefixEnd_28072 := by exact prefixLift 28072
  have htrace : WordTrace (prefixWord ++ tailWord_28072) baseStart_28072 baseEnd_28072 := by
    simpa [prefixWord, tailWord_28072, baseEnd_28072] using wordTrace_append hprefix tailTrace_28072
  have hstable : (prefixWord ++ tailWord_28072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28072).length < 2 ^ (prefixWord ++ tailWord_28072).sum := by decide
  have hdescent : baseEnd_28072 < baseStart_28072 := by decide
  rcases family_descends (prefixWord ++ tailWord_28072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28111 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_28111 : Nat := 118140960795 + 28111 * 2 ^ 59
def prefixEnd_28111 : Nat := 4983230072969 + 3 ^ 40 * 28111 * 2
def baseEnd_28111 : Nat := 9622969785763166188817

theorem tailTrace_28111 : CollatzResearch.WordTrace tailWord_28111 prefixEnd_28111 9622969785763166188817 := by
  unfold tailWord_28111
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025292401166122821684187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 683528267444081881122791 1025292401166122821684187)
  ·
    refine ⟨1537938601749184232526281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025292401166122821684187 1537938601749184232526281)
    ·
      refine ⟨1153453951311888174394711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1537938601749184232526281 1153453951311888174394711)
      ·
        refine ⟨1730180926967832261592067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153453951311888174394711 1730180926967832261592067)
        ·
          refine ⟨2595271390451748392388101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730180926967832261592067 2595271390451748392388101)
          ·
            refine ⟨486613385709702823572769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2595271390451748392388101 486613385709702823572769)
            ·
              refine ⟨364960039282277117679577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486613385709702823572769 364960039282277117679577)
              ·
                refine ⟨273720029461707838259683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364960039282277117679577 273720029461707838259683)
                ·
                  refine ⟨410580044192561757389525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273720029461707838259683 410580044192561757389525)
                  ·
                    refine ⟨9622969785763166188817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 410580044192561757389525 9622969785763166188817)
                    ·
                      rfl

theorem cell22_28111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_28111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28111 prefixEnd_28111 := by exact prefixLift 28111
  have htrace : WordTrace (prefixWord ++ tailWord_28111) baseStart_28111 baseEnd_28111 := by
    simpa [prefixWord, tailWord_28111, baseEnd_28111] using wordTrace_append hprefix tailTrace_28111
  have hstable : (prefixWord ++ tailWord_28111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28111).length < 2 ^ (prefixWord ++ tailWord_28111).sum := by decide
  have hdescent : baseEnd_28111 < baseStart_28111 := by decide
  rcases family_descends (prefixWord ++ tailWord_28111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28192 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 4]
def baseStart_28192 : Nat := 118140960795 + 28192 * 2 ^ 59
def prefixEnd_28192 : Nat := 4983230072969 + 3 ^ 40 * 28192 * 2
def baseEnd_28192 : Nat := 3216899247035318304523

theorem tailTrace_28192 : CollatzResearch.WordTrace tailWord_28192 prefixEnd_28192 3216899247035318304523 := by
  unfold tailWord_28192
  simp only [CollatzResearch.WordTrace]
  refine ⟨514123356936336827691415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 685497809248449103588553 514123356936336827691415)
  ·
    refine ⟨771185035404505241537123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 514123356936336827691415 771185035404505241537123)
    ·
      refine ⟨1156777553106757862305685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771185035404505241537123 1156777553106757862305685)
      ·
        refine ⟨54223947801879274795579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1156777553106757862305685 54223947801879274795579)
        ·
          refine ⟨81335921702818912193369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54223947801879274795579 81335921702818912193369)
          ·
            refine ⟨61001941277114184145027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81335921702818912193369 61001941277114184145027)
            ·
              refine ⟨91502911915671276217541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61001941277114184145027 91502911915671276217541)
              ·
                refine ⟨17156795984188364290789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91502911915671276217541 17156795984188364290789)
                ·
                  refine ⟨3216899247035318304523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17156795984188364290789 3216899247035318304523)
                  ·
                    rfl

theorem cell22_28192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_28192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28192 prefixEnd_28192 := by exact prefixLift 28192
  have htrace : WordTrace (prefixWord ++ tailWord_28192) baseStart_28192 baseEnd_28192 := by
    simpa [prefixWord, tailWord_28192, baseEnd_28192] using wordTrace_append hprefix tailTrace_28192
  have hstable : (prefixWord ++ tailWord_28192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28192).length < 2 ^ (prefixWord ++ tailWord_28192).sum := by decide
  have hdescent : baseEnd_28192 < baseStart_28192 := by decide
  rcases family_descends (prefixWord ++ tailWord_28192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28252 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_28252 : Nat := 118140960795 + 28252 * 2 ^ 59
def prefixEnd_28252 : Nat := 4983230072969 + 3 ^ 40 * 28252 * 2
def baseEnd_28252 : Nat := 9671236967285798413385

theorem tailTrace_28252 : CollatzResearch.WordTrace tailWord_28252 prefixEnd_28252 9671236967285798413385 := by
  unfold tailWord_28252
  simp only [CollatzResearch.WordTrace]
  refine ⟨515217546827651951283505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 686956729103535935044673 515217546827651951283505)
  ·
    refine ⟨386413160120738963462629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 515217546827651951283505 386413160120738963462629)
    ·
      refine ⟨72452467522638555649243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386413160120738963462629 72452467522638555649243)
      ·
        refine ⟨108678701283957833473865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72452467522638555649243 108678701283957833473865)
        ·
          refine ⟨81509025962968375105399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108678701283957833473865 81509025962968375105399)
          ·
            refine ⟨122263538944452562658099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81509025962968375105399 122263538944452562658099)
            ·
              refine ⟨183395308416678843987149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122263538944452562658099 183395308416678843987149)
              ·
                refine ⟨68773240656254566495181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183395308416678843987149 68773240656254566495181)
                ·
                  refine ⟨25789965246095462435693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68773240656254566495181 25789965246095462435693)
                  ·
                    refine ⟨9671236967285798413385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25789965246095462435693 9671236967285798413385)
                    ·
                      rfl

theorem cell22_28252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_28252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28252 prefixEnd_28252 := by exact prefixLift 28252
  have htrace : WordTrace (prefixWord ++ tailWord_28252) baseStart_28252 baseEnd_28252 := by
    simpa [prefixWord, tailWord_28252, baseEnd_28252] using wordTrace_append hprefix tailTrace_28252
  have hstable : (prefixWord ++ tailWord_28252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28252).length < 2 ^ (prefixWord ++ tailWord_28252).sum := by decide
  have hdescent : baseEnd_28252 < baseStart_28252 := by decide
  rcases family_descends (prefixWord ++ tailWord_28252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28316 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 5]
def baseStart_28316 : Nat := 118140960795 + 28316 * 2 ^ 59
def prefixEnd_28316 : Nat := 4983230072969 + 3 ^ 40 * 28316 * 2
def baseEnd_28316 : Nat := 3231048491736988271063

theorem tailTrace_28316 : CollatzResearch.WordTrace tailWord_28316 prefixEnd_28316 3231048491736988271063 := by
  unfold tailWord_28316
  simp only [CollatzResearch.WordTrace]
  refine ⟨516384682711721416448401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 688512910282295221931201 516384682711721416448401)
  ·
    refine ⟨387288512033791062336301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 516384682711721416448401 387288512033791062336301)
    ·
      refine ⟨145233192012671648376113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387288512033791062336301 145233192012671648376113)
      ·
        refine ⟨108924894009503736282085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145233192012671648376113 108924894009503736282085)
        ·
          refine ⟨20423417626781950552891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108924894009503736282085 20423417626781950552891)
          ·
            refine ⟨30635126440172925829337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20423417626781950552891 30635126440172925829337)
            ·
              refine ⟨22976344830129694372003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30635126440172925829337 22976344830129694372003)
              ·
                refine ⟨34464517245194541558005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22976344830129694372003 34464517245194541558005)
                ·
                  refine ⟨3231048491736988271063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34464517245194541558005 3231048491736988271063)
                  ·
                    rfl

theorem cell22_28316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_28316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28316 prefixEnd_28316 := by exact prefixLift 28316
  have htrace : WordTrace (prefixWord ++ tailWord_28316) baseStart_28316 baseEnd_28316 := by
    simpa [prefixWord, tailWord_28316, baseEnd_28316] using wordTrace_append hprefix tailTrace_28316
  have hstable : (prefixWord ++ tailWord_28316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28316).length < 2 ^ (prefixWord ++ tailWord_28316).sum := by decide
  have hdescent : baseEnd_28316 < baseStart_28316 := by decide
  rcases family_descends (prefixWord ++ tailWord_28316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28354 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_28354 : Nat := 118140960795 + 28354 * 2 ^ 59
def prefixEnd_28354 : Nat := 4983230072969 + 3 ^ 40 * 28354 * 2
def baseEnd_28354 : Nat := 9706153651791532363073

theorem tailTrace_28354 : CollatzResearch.WordTrace tailWord_28354 prefixEnd_28354 9706153651791532363073 := by
  unfold tailWord_28354
  simp only [CollatzResearch.WordTrace]
  refine ⟨258538834821443830695029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 689436892857183548520077 258538834821443830695029)
  ·
    refine ⟨24238015764510359127659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258538834821443830695029 24238015764510359127659)
    ·
      refine ⟨36357023646765538691489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24238015764510359127659 36357023646765538691489)
      ·
        refine ⟨27267767735074154018617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36357023646765538691489 27267767735074154018617)
        ·
          refine ⟨20450825801305615513963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27267767735074154018617 20450825801305615513963)
          ·
            refine ⟨30676238701958423270945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20450825801305615513963 30676238701958423270945)
            ·
              refine ⟨23007179026468817453209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30676238701958423270945 23007179026468817453209)
              ·
                refine ⟨17255384269851613089907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23007179026468817453209 17255384269851613089907)
                ·
                  refine ⟨25883076404777419634861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17255384269851613089907 25883076404777419634861)
                  ·
                    refine ⟨9706153651791532363073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25883076404777419634861 9706153651791532363073)
                    ·
                      rfl

theorem cell22_28354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_28354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28354 prefixEnd_28354 := by exact prefixLift 28354
  have htrace : WordTrace (prefixWord ++ tailWord_28354) baseStart_28354 baseEnd_28354 := by
    simpa [prefixWord, tailWord_28354, baseEnd_28354] using wordTrace_append hprefix tailTrace_28354
  have hstable : (prefixWord ++ tailWord_28354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28354).length < 2 ^ (prefixWord ++ tailWord_28354).sum := by decide
  have hdescent : baseEnd_28354 < baseStart_28354 := by decide
  rcases family_descends (prefixWord ++ tailWord_28354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28372 : List Nat := [2, 4, 1, 3, 1, 1, 3, 7]
def baseStart_28372 : Nat := 118140960795 + 28372 * 2 ^ 59
def prefixEnd_28372 : Nat := 4983230072969 + 3 ^ 40 * 28372 * 2
def baseEnd_28372 : Nat := 1079146157738387268113

theorem tailTrace_28372 : CollatzResearch.WordTrace tailWord_28372 prefixEnd_28372 1079146157738387268113 := by
  unfold tailWord_28372
  simp only [CollatzResearch.WordTrace]
  refine ⟨517405926610282198467685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 689874568813709597956913 517405926610282198467685)
  ·
    refine ⟨97013611239427912212691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 517405926610282198467685 97013611239427912212691)
    ·
      refine ⟨145520416859141868319037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97013611239427912212691 145520416859141868319037)
      ·
        refine ⟨54570156322178200619639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145520416859141868319037 54570156322178200619639)
        ·
          refine ⟨81855234483267300929459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54570156322178200619639 81855234483267300929459)
          ·
            refine ⟨122782851724900951394189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81855234483267300929459 122782851724900951394189)
            ·
              refine ⟨46043569396837856772821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122782851724900951394189 46043569396837856772821)
              ·
                refine ⟨1079146157738387268113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46043569396837856772821 1079146157738387268113)
                ·
                  rfl

theorem cell22_28372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_28372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28372 prefixEnd_28372 := by exact prefixLift 28372
  have htrace : WordTrace (prefixWord ++ tailWord_28372) baseStart_28372 baseEnd_28372 := by
    simpa [prefixWord, tailWord_28372, baseEnd_28372] using wordTrace_append hprefix tailTrace_28372
  have hstable : (prefixWord ++ tailWord_28372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28372).length < 2 ^ (prefixWord ++ tailWord_28372).sum := by decide
  have hdescent : baseEnd_28372 < baseStart_28372 := by decide
  rcases family_descends (prefixWord ++ tailWord_28372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28391 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 2, 4]
def baseStart_28391 : Nat := 118140960795 + 28391 * 2 ^ 59
def prefixEnd_28391 : Nat := 4983230072969 + 3 ^ 40 * 28391 * 2
def baseEnd_28391 : Nat := 9718819507935769187959

theorem tailTrace_28391 : CollatzResearch.WordTrace tailWord_28391 prefixEnd_28391 9718819507935769187959 := by
  unfold tailWord_28391
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035504840151730641877027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 690336560101153761251351 1035504840151730641877027)
  ·
    refine ⟨1553257260227595962815541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035504840151730641877027 1553257260227595962815541)
    ·
      refine ⟨145617868146337121513957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1553257260227595962815541 145617868146337121513957)
      ·
        refine ⟨27303350277438210283867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145617868146337121513957 27303350277438210283867)
        ·
          refine ⟨40955025416157315425801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27303350277438210283867 40955025416157315425801)
          ·
            refine ⟨30716269062117986569351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40955025416157315425801 30716269062117986569351)
            ·
              refine ⟨46074403593176979854027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30716269062117986569351 46074403593176979854027)
              ·
                refine ⟨69111605389765469781041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46074403593176979854027 69111605389765469781041)
                ·
                  refine ⟨51833704042324102335781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69111605389765469781041 51833704042324102335781)
                  ·
                    refine ⟨9718819507935769187959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51833704042324102335781 9718819507935769187959)
                    ·
                      rfl

theorem cell22_28391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_28391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28391 prefixEnd_28391 := by exact prefixLift 28391
  have htrace : WordTrace (prefixWord ++ tailWord_28391) baseStart_28391 baseEnd_28391 := by
    simpa [prefixWord, tailWord_28391, baseEnd_28391] using wordTrace_append hprefix tailTrace_28391
  have hstable : (prefixWord ++ tailWord_28391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28391).length < 2 ^ (prefixWord ++ tailWord_28391).sum := by decide
  have hdescent : baseEnd_28391 < baseStart_28391 := by decide
  rcases family_descends (prefixWord ++ tailWord_28391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28415 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_28415 : Nat := 118140960795 + 28415 * 2 ^ 59
def prefixEnd_28415 : Nat := 4983230072969 + 3 ^ 40 * 28415 * 2
def baseEnd_28415 : Nat := 9727035198407706587885

theorem tailTrace_28415 : CollatzResearch.WordTrace tailWord_28415 prefixEnd_28415 9727035198407706587885 := by
  unfold tailWord_28415
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036380192064782740750699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 690920128043188493833799 1036380192064782740750699)
  ·
    refine ⟨1554570288097174111126049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1036380192064782740750699 1554570288097174111126049)
    ·
      refine ⟨1165927716072880583344537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1554570288097174111126049 1165927716072880583344537)
      ·
        refine ⟨874445787054660437508403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1165927716072880583344537 874445787054660437508403)
        ·
          refine ⟨1311668680581990656262605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874445787054660437508403 1311668680581990656262605)
          ·
            refine ⟨491875755218246496098477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1311668680581990656262605 491875755218246496098477)
            ·
              refine ⟨184453408206842436036929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491875755218246496098477 184453408206842436036929)
              ·
                refine ⟨138340056155131827027697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184453408206842436036929 138340056155131827027697)
                ·
                  refine ⟨103755042116348870270773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138340056155131827027697 103755042116348870270773)
                  ·
                    refine ⟨9727035198407706587885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103755042116348870270773 9727035198407706587885)
                    ·
                      rfl

theorem cell22_28415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_28415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28415 prefixEnd_28415 := by exact prefixLift 28415
  have htrace : WordTrace (prefixWord ++ tailWord_28415) baseStart_28415 baseEnd_28415 := by
    simpa [prefixWord, tailWord_28415, baseEnd_28415] using wordTrace_append hprefix tailTrace_28415
  have hstable : (prefixWord ++ tailWord_28415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28415).length < 2 ^ (prefixWord ++ tailWord_28415).sum := by decide
  have hdescent : baseEnd_28415 < baseStart_28415 := by decide
  rcases family_descends (prefixWord ++ tailWord_28415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28417 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 5]
def baseStart_28417 : Nat := 118140960795 + 28417 * 2 ^ 59
def prefixEnd_28417 : Nat := 4983230072969 + 3 ^ 40 * 28417 * 2
def baseEnd_28417 : Nat := 3242573279760122679293

theorem tailTrace_28417 : CollatzResearch.WordTrace tailWord_28417 prefixEnd_28417 3242573279760122679293 := by
  unfold tailWord_28417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036453138057537082323505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 690968758705024721549003 1036453138057537082323505)
  ·
    refine ⟨777339853543152811742629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1036453138057537082323505 777339853543152811742629)
    ·
      refine ⟨145751222539341152201743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 777339853543152811742629 145751222539341152201743)
      ·
        refine ⟨218626833809011728302615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145751222539341152201743 218626833809011728302615)
        ·
          refine ⟨327940250713517592453923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218626833809011728302615 327940250713517592453923)
          ·
            refine ⟨491910376070276388680885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327940250713517592453923 491910376070276388680885)
            ·
              refine ⟨46116597756588411438833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491910376070276388680885 46116597756588411438833)
              ·
                refine ⟨34587448317441308579125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46116597756588411438833 34587448317441308579125)
                ·
                  refine ⟨3242573279760122679293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34587448317441308579125 3242573279760122679293)
                  ·
                    rfl

theorem cell22_28417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_28417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28417 prefixEnd_28417 := by exact prefixLift 28417
  have htrace : WordTrace (prefixWord ++ tailWord_28417) baseStart_28417 baseEnd_28417 := by
    simpa [prefixWord, tailWord_28417, baseEnd_28417] using wordTrace_append hprefix tailTrace_28417
  have hstable : (prefixWord ++ tailWord_28417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28417).length < 2 ^ (prefixWord ++ tailWord_28417).sum := by decide
  have hdescent : baseEnd_28417 < baseStart_28417 := by decide
  rcases family_descends (prefixWord ++ tailWord_28417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28479 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 6]
def baseStart_28479 : Nat := 118140960795 + 28479 * 2 ^ 59
def prefixEnd_28479 : Nat := 4983230072969 + 3 ^ 40 * 28479 * 2
def baseEnd_28479 : Nat := 3249647902110957662563

theorem tailTrace_28479 : CollatzResearch.WordTrace tailWord_28479 prefixEnd_28479 3249647902110957662563 := by
  unfold tailWord_28479
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038714463832921671080491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 692476309221947780720327 1038714463832921671080491)
  ·
    refine ⟨1558071695749382506620737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1038714463832921671080491 1558071695749382506620737)
    ·
      refine ⟨1168553771812036879965553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1558071695749382506620737 1168553771812036879965553)
      ·
        refine ⟨876415328859027659974165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168553771812036879965553 876415328859027659974165)
        ·
          refine ⟨41081968540266921561289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 876415328859027659974165 41081968540266921561289)
          ·
            refine ⟨30811476405200191170967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41081968540266921561289 30811476405200191170967)
            ·
              refine ⟨46217214607800286756451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30811476405200191170967 46217214607800286756451)
              ·
                refine ⟨69325821911700430134677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46217214607800286756451 69325821911700430134677)
                ·
                  refine ⟨3249647902110957662563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69325821911700430134677 3249647902110957662563)
                  ·
                    rfl

theorem cell22_28479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 6].length) (baseStart_28479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28479 prefixEnd_28479 := by exact prefixLift 28479
  have htrace : WordTrace (prefixWord ++ tailWord_28479) baseStart_28479 baseEnd_28479 := by
    simpa [prefixWord, tailWord_28479, baseEnd_28479] using wordTrace_append hprefix tailTrace_28479
  have hstable : (prefixWord ++ tailWord_28479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28479).length < 2 ^ (prefixWord ++ tailWord_28479).sum := by decide
  have hdescent : baseEnd_28479 < baseStart_28479 := by decide
  rcases family_descends (prefixWord ++ tailWord_28479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28573 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_28573 : Nat := 118140960795 + 28573 * 2 ^ 59
def prefixEnd_28573 : Nat := 4983230072969 + 3 ^ 40 * 28573 * 2
def baseEnd_28573 : Nat := 9781121827347961137401

theorem tailTrace_28573 : CollatzResearch.WordTrace tailWord_28573 prefixEnd_28573 9781121827347961137401 := by
  unfold tailWord_28573
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042142925492375725002373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 694761950328250483334915 1042142925492375725002373)
  ·
    refine ⟨195401798529820448437945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1042142925492375725002373 195401798529820448437945)
    ·
      refine ⟨146551348897365336328459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195401798529820448437945 146551348897365336328459)
      ·
        refine ⟨219827023346048004492689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146551348897365336328459 219827023346048004492689)
        ·
          refine ⟨164870267509536003369517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219827023346048004492689 164870267509536003369517)
          ·
            refine ⟨61826350316076001263569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164870267509536003369517 61826350316076001263569)
            ·
              refine ⟨46369762737057000947677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61826350316076001263569 46369762737057000947677)
              ·
                refine ⟨17388661026396375355379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46369762737057000947677 17388661026396375355379)
                ·
                  refine ⟨26082991539594563033069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17388661026396375355379 26082991539594563033069)
                  ·
                    refine ⟨9781121827347961137401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26082991539594563033069 9781121827347961137401)
                    ·
                      rfl

theorem cell22_28573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_28573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28573 prefixEnd_28573 := by exact prefixLift 28573
  have htrace : WordTrace (prefixWord ++ tailWord_28573) baseStart_28573 baseEnd_28573 := by
    simpa [prefixWord, tailWord_28573, baseEnd_28573] using wordTrace_append hprefix tailTrace_28573
  have hstable : (prefixWord ++ tailWord_28573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28573).length < 2 ^ (prefixWord ++ tailWord_28573).sum := by decide
  have hdescent : baseEnd_28573 < baseStart_28573 := by decide
  rcases family_descends (prefixWord ++ tailWord_28573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28616 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_28616 : Nat := 118140960795 + 28616 * 2 ^ 59
def prefixEnd_28616 : Nat := 4983230072969 + 3 ^ 40 * 28616 * 2
def baseEnd_28616 : Nat := 9795841606110182312269

theorem tailTrace_28616 : CollatzResearch.WordTrace tailWord_28616 prefixEnd_28616 9795841606110182312269 := by
  unfold tailWord_28616
  simp only [CollatzResearch.WordTrace]
  refine ⟨521855632168297034408851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 695807509557729379211801 521855632168297034408851)
  ·
    refine ⟨782783448252445551613277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 521855632168297034408851 782783448252445551613277)
    ·
      refine ⟨293543793094667081854979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 782783448252445551613277 293543793094667081854979)
      ·
        refine ⟨440315689642000622782469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293543793094667081854979 440315689642000622782469)
        ·
          refine ⟨82559191807875116771713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 440315689642000622782469 82559191807875116771713)
          ·
            refine ⟨61919393855906337578785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82559191807875116771713 61919393855906337578785)
            ·
              refine ⟨46439545391929753184089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61919393855906337578785 46439545391929753184089)
              ·
                refine ⟨34829659043947314888067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46439545391929753184089 34829659043947314888067)
                ·
                  refine ⟨52244488565920972332101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34829659043947314888067 52244488565920972332101)
                  ·
                    refine ⟨9795841606110182312269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52244488565920972332101 9795841606110182312269)
                    ·
                      rfl

theorem cell22_28616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_28616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28616 prefixEnd_28616 := by exact prefixLift 28616
  have htrace : WordTrace (prefixWord ++ tailWord_28616) baseStart_28616 baseEnd_28616 := by
    simpa [prefixWord, tailWord_28616, baseEnd_28616] using wordTrace_append hprefix tailTrace_28616
  have hstable : (prefixWord ++ tailWord_28616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28616).length < 2 ^ (prefixWord ++ tailWord_28616).sum := by decide
  have hdescent : baseEnd_28616 < baseStart_28616 := by decide
  rcases family_descends (prefixWord ++ tailWord_28616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28644 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_28644 : Nat := 118140960795 + 28644 * 2 ^ 59
def prefixEnd_28644 : Nat := 4983230072969 + 3 ^ 40 * 28644 * 2
def baseEnd_28644 : Nat := 9805426578327442612183

theorem tailTrace_28644 : CollatzResearch.WordTrace tailWord_28644 prefixEnd_28644 9805426578327442612183 := by
  unfold tailWord_28644
  simp only [CollatzResearch.WordTrace]
  refine ⟨522366254117577425418493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 696488338823436567224657 522366254117577425418493)
  ·
    refine ⟨195887345294091534531935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 522366254117577425418493 195887345294091534531935)
    ·
      refine ⟨293831017941137301797903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195887345294091534531935 293831017941137301797903)
      ·
        refine ⟨440746526911705952696855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293831017941137301797903 440746526911705952696855)
        ·
          refine ⟨661119790367558929045283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440746526911705952696855 661119790367558929045283)
          ·
            refine ⟨991679685551338393567925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661119790367558929045283 991679685551338393567925)
            ·
              refine ⟨92969970520437974396993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 991679685551338393567925 92969970520437974396993)
              ·
                refine ⟨69727477890328480797745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92969970520437974396993 69727477890328480797745)
                ·
                  refine ⟨52295608417746360598309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69727477890328480797745 52295608417746360598309)
                  ·
                    refine ⟨9805426578327442612183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52295608417746360598309 9805426578327442612183)
                    ·
                      rfl

theorem cell22_28644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_28644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28644 prefixEnd_28644 := by exact prefixLift 28644
  have htrace : WordTrace (prefixWord ++ tailWord_28644) baseStart_28644 baseEnd_28644 := by
    simpa [prefixWord, tailWord_28644, baseEnd_28644] using wordTrace_append hprefix tailTrace_28644
  have hstable : (prefixWord ++ tailWord_28644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28644).length < 2 ^ (prefixWord ++ tailWord_28644).sum := by decide
  have hdescent : baseEnd_28644 < baseStart_28644 := by decide
  rcases family_descends (prefixWord ++ tailWord_28644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28672 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_28672 : Nat := 118140960795 + 28672 * 2 ^ 59
def prefixEnd_28672 : Nat := 4983230072969 + 3 ^ 40 * 28672 * 2
def baseEnd_28672 : Nat := 9815011550544702912097

theorem tailTrace_28672 : CollatzResearch.WordTrace tailWord_28672 prefixEnd_28672 9815011550544702912097 := by
  unfold tailWord_28672
  simp only [CollatzResearch.WordTrace]
  refine ⟨522876876066857816428135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 697169168089143755237513 522876876066857816428135)
  ·
    refine ⟨784315314100286724642203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 522876876066857816428135 784315314100286724642203)
    ·
      refine ⟨1176472971150430086963305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784315314100286724642203 1176472971150430086963305)
      ·
        refine ⟨882354728362822565222479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176472971150430086963305 882354728362822565222479)
        ·
          refine ⟨1323532092544233847833719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882354728362822565222479 1323532092544233847833719)
          ·
            refine ⟨1985298138816350771750579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323532092544233847833719 1985298138816350771750579)
            ·
              refine ⟨2977947208224526157625869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985298138816350771750579 2977947208224526157625869)
              ·
                refine ⟨1116730203084197309109701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2977947208224526157625869 1116730203084197309109701)
                ·
                  refine ⟨209386913078286995458069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116730203084197309109701 209386913078286995458069)
                  ·
                    refine ⟨9815011550544702912097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 209386913078286995458069 9815011550544702912097)
                    ·
                      rfl

theorem cell22_28672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_28672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28672 prefixEnd_28672 := by exact prefixLift 28672
  have htrace : WordTrace (prefixWord ++ tailWord_28672) baseStart_28672 baseEnd_28672 := by
    simpa [prefixWord, tailWord_28672, baseEnd_28672] using wordTrace_append hprefix tailTrace_28672
  have hstable : (prefixWord ++ tailWord_28672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28672).length < 2 ^ (prefixWord ++ tailWord_28672).sum := by decide
  have hdescent : baseEnd_28672 < baseStart_28672 := by decide
  rcases family_descends (prefixWord ++ tailWord_28672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28742 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_28742 : Nat := 118140960795 + 28742 * 2 ^ 59
def prefixEnd_28742 : Nat := 4983230072969 + 3 ^ 40 * 28742 * 2
def baseEnd_28742 : Nat := 9838973981087853661883

theorem tailTrace_28742 : CollatzResearch.WordTrace tailWord_28742 prefixEnd_28742 9838973981087853661883 := by
  unfold tailWord_28742
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759589433753674622015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 698871241253411725269653 32759589433753674622015)
  ·
    refine ⟨49139384150630511933023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32759589433753674622015 49139384150630511933023)
    ·
      refine ⟨73709076225945767899535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49139384150630511933023 73709076225945767899535)
      ·
        refine ⟨110563614338918651849303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73709076225945767899535 110563614338918651849303)
        ·
          refine ⟨165845421508377977773955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110563614338918651849303 165845421508377977773955)
          ·
            refine ⟨248768132262566966660933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165845421508377977773955 248768132262566966660933)
            ·
              refine ⟨46644024799231306248925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248768132262566966660933 46644024799231306248925)
              ·
                refine ⟨17491509299711739843347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46644024799231306248925 17491509299711739843347)
                ·
                  refine ⟨26237263949567609765021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17491509299711739843347 26237263949567609765021)
                  ·
                    refine ⟨9838973981087853661883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26237263949567609765021 9838973981087853661883)
                    ·
                      rfl

theorem cell22_28742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_28742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28742 prefixEnd_28742 := by exact prefixLift 28742
  have htrace : WordTrace (prefixWord ++ tailWord_28742) baseStart_28742 baseEnd_28742 := by
    simpa [prefixWord, tailWord_28742, baseEnd_28742] using wordTrace_append hprefix tailTrace_28742
  have hstable : (prefixWord ++ tailWord_28742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28742).length < 2 ^ (prefixWord ++ tailWord_28742).sum := by decide
  have hdescent : baseEnd_28742 < baseStart_28742 := by decide
  rcases family_descends (prefixWord ++ tailWord_28742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28901 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 8]
def baseStart_28901 : Nat := 118140960795 + 28901 * 2 ^ 59
def prefixEnd_28901 : Nat := 4983230072969 + 3 ^ 40 * 28901 * 2
def baseEnd_28901 : Nat := 3297800976821479645465

theorem tailTrace_28901 : CollatzResearch.WordTrace tailWord_28901 prefixEnd_28901 3297800976821479645465 := by
  unfold tailWord_28901
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054106068304087742942557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 702737378869391828628371 1054106068304087742942557)
  ·
    refine ⟨395289775614032903603459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1054106068304087742942557 395289775614032903603459)
    ·
      refine ⟨592934663421049355405189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395289775614032903603459 592934663421049355405189)
      ·
        refine ⟨111175249391446754138473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 592934663421049355405189 111175249391446754138473)
        ·
          refine ⟨83381437043585065603855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111175249391446754138473 83381437043585065603855)
          ·
            refine ⟨125072155565377598405783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83381437043585065603855 125072155565377598405783)
            ·
              refine ⟨187608233348066397608675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125072155565377598405783 187608233348066397608675)
              ·
                refine ⟨281412350022099596413013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187608233348066397608675 281412350022099596413013)
                ·
                  refine ⟨3297800976821479645465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 281412350022099596413013 3297800976821479645465)
                  ·
                    rfl

theorem cell22_28901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_28901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28901 prefixEnd_28901 := by exact prefixLift 28901
  have htrace : WordTrace (prefixWord ++ tailWord_28901) baseStart_28901 baseEnd_28901 := by
    simpa [prefixWord, tailWord_28901, baseEnd_28901] using wordTrace_append hprefix tailTrace_28901
  have hstable : (prefixWord ++ tailWord_28901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28901).length < 2 ^ (prefixWord ++ tailWord_28901).sum := by decide
  have hdescent : baseEnd_28901 < baseStart_28901 := by decide
  rcases family_descends (prefixWord ++ tailWord_28901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28903 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 3, 4]
def baseStart_28903 : Nat := 118140960795 + 28903 * 2 ^ 59
def prefixEnd_28903 : Nat := 4983230072969 + 3 ^ 40 * 28903 * 2
def baseEnd_28903 : Nat := 9894087571337100386389

theorem tailTrace_28903 : CollatzResearch.WordTrace tailWord_28903 prefixEnd_28903 9894087571337100386389 := by
  unfold tailWord_28903
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054179014296842084515363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 702786009531228056343575 1054179014296842084515363)
  ·
    refine ⟨1581268521445263126773045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054179014296842084515363 1581268521445263126773045)
    ·
      refine ⟨148243923885493418134973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1581268521445263126773045 148243923885493418134973)
      ·
        refine ⟨55591471457060031800615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148243923885493418134973 55591471457060031800615)
        ·
          refine ⟨83387207185590047700923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55591471457060031800615 83387207185590047700923)
          ·
            refine ⟨125080810778385071551385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83387207185590047700923 125080810778385071551385)
            ·
              refine ⟨93810608083788803663539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125080810778385071551385 93810608083788803663539)
              ·
                refine ⟨140715912125683205495309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93810608083788803663539 140715912125683205495309)
                ·
                  refine ⟨52768467047131202060741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140715912125683205495309 52768467047131202060741)
                  ·
                    refine ⟨9894087571337100386389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52768467047131202060741 9894087571337100386389)
                    ·
                      rfl

theorem cell22_28903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_28903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28903 prefixEnd_28903 := by exact prefixLift 28903
  have htrace : WordTrace (prefixWord ++ tailWord_28903) baseStart_28903 baseEnd_28903 := by
    simpa [prefixWord, tailWord_28903, baseEnd_28903] using wordTrace_append hprefix tailTrace_28903
  have hstable : (prefixWord ++ tailWord_28903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28903).length < 2 ^ (prefixWord ++ tailWord_28903).sum := by decide
  have hdescent : baseEnd_28903 < baseStart_28903 := by decide
  rcases family_descends (prefixWord ++ tailWord_28903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28931 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 4, 4]
def baseStart_28931 : Nat := 118140960795 + 28931 * 2 ^ 59
def prefixEnd_28931 : Nat := 4983230072969 + 3 ^ 40 * 28931 * 2
def baseEnd_28931 : Nat := 9903672543554360686303

theorem tailTrace_28931 : CollatzResearch.WordTrace tailWord_28931 prefixEnd_28931 9903672543554360686303 := by
  unfold tailWord_28931
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055200258195402866534647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 703466838796935244356431 1055200258195402866534647)
  ·
    refine ⟨1582800387293104299801971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055200258195402866534647 1582800387293104299801971)
    ·
      refine ⟨2374200580939656449702957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582800387293104299801971 2374200580939656449702957)
      ·
        refine ⟨890325217852371168638609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2374200580939656449702957 890325217852371168638609)
        ·
          refine ⟨667743913389278376478957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890325217852371168638609 667743913389278376478957)
          ·
            refine ⟨250403967520979391179609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667743913389278376478957 250403967520979391179609)
            ·
              refine ⟨187802975640734543384707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250403967520979391179609 187802975640734543384707)
              ·
                refine ⟨281704463461101815077061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187802975640734543384707 281704463461101815077061)
                ·
                  refine ⟨52819586898956590326949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281704463461101815077061 52819586898956590326949)
                  ·
                    refine ⟨9903672543554360686303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52819586898956590326949 9903672543554360686303)
                    ·
                      rfl

theorem cell22_28931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_28931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28931 prefixEnd_28931 := by exact prefixLift 28931
  have htrace : WordTrace (prefixWord ++ tailWord_28931) baseStart_28931 baseEnd_28931 := by
    simpa [prefixWord, tailWord_28931, baseEnd_28931] using wordTrace_append hprefix tailTrace_28931
  have hstable : (prefixWord ++ tailWord_28931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28931).length < 2 ^ (prefixWord ++ tailWord_28931).sum := by decide
  have hdescent : baseEnd_28931 < baseStart_28931 := by decide
  rcases family_descends (prefixWord ++ tailWord_28931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28933 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_28933 : Nat := 118140960795 + 28933 * 2 ^ 59
def prefixEnd_28933 : Nat := 4983230072969 + 3 ^ 40 * 28933 * 2
def baseEnd_28933 : Nat := 9904357184427022136297

theorem tailTrace_28933 : CollatzResearch.WordTrace tailWord_28933 prefixEnd_28933 9904357184427022136297 := by
  unfold tailWord_28933
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055273204188157208107453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 703515469458771472071635 1055273204188157208107453)
  ·
    refine ⟨395727451570558953040295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1055273204188157208107453 395727451570558953040295)
    ·
      refine ⟨593591177355838429560443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395727451570558953040295 593591177355838429560443)
      ·
        refine ⟨890386766033757644340665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593591177355838429560443 890386766033757644340665)
        ·
          refine ⟨667790074525318233255499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890386766033757644340665 667790074525318233255499)
          ·
            refine ⟨1001685111787977349883249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667790074525318233255499 1001685111787977349883249)
            ·
              refine ⟨751263833840983012412437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001685111787977349883249 751263833840983012412437)
              ·
                refine ⟨35215492211296078706833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 751263833840983012412437 35215492211296078706833)
                ·
                  refine ⟨26411619158472059030125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35215492211296078706833 26411619158472059030125)
                  ·
                    refine ⟨9904357184427022136297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26411619158472059030125 9904357184427022136297)
                    ·
                      rfl

theorem cell22_28933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_28933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28933 prefixEnd_28933 := by exact prefixLift 28933
  have htrace : WordTrace (prefixWord ++ tailWord_28933) baseStart_28933 baseEnd_28933 := by
    simpa [prefixWord, tailWord_28933, baseEnd_28933] using wordTrace_append hprefix tailTrace_28933
  have hstable : (prefixWord ++ tailWord_28933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28933).length < 2 ^ (prefixWord ++ tailWord_28933).sum := by decide
  have hdescent : baseEnd_28933 < baseStart_28933 := by decide
  rcases family_descends (prefixWord ++ tailWord_28933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28935 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 6]
def baseStart_28935 : Nat := 118140960795 + 28935 * 2 ^ 59
def prefixEnd_28935 : Nat := 4983230072969 + 3 ^ 40 * 28935 * 2
def baseEnd_28935 : Nat := 3301680608433227862097

theorem tailTrace_28935 : CollatzResearch.WordTrace tailWord_28935 prefixEnd_28935 3301680608433227862097 := by
  unfold tailWord_28935
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055346150180911549680259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 703564100120607699786839 1055346150180911549680259)
  ·
    refine ⟨1583019225271367324520389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055346150180911549680259 1583019225271367324520389)
    ·
      refine ⟨296816104738381373347573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1583019225271367324520389 296816104738381373347573)
      ·
        refine ⟨27826509819223253751335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296816104738381373347573 27826509819223253751335)
        ·
          refine ⟨41739764728834880627003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27826509819223253751335 41739764728834880627003)
          ·
            refine ⟨62609647093252320940505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41739764728834880627003 62609647093252320940505)
            ·
              refine ⟨46957235319939240705379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62609647093252320940505 46957235319939240705379)
              ·
                refine ⟨70435852979908861058069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46957235319939240705379 70435852979908861058069)
                ·
                  refine ⟨3301680608433227862097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70435852979908861058069 3301680608433227862097)
                  ·
                    rfl

theorem cell22_28935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 6].length) (baseStart_28935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28935 prefixEnd_28935 := by exact prefixLift 28935
  have htrace : WordTrace (prefixWord ++ tailWord_28935) baseStart_28935 baseEnd_28935 := by
    simpa [prefixWord, tailWord_28935, baseEnd_28935] using wordTrace_append hprefix tailTrace_28935
  have hstable : (prefixWord ++ tailWord_28935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28935).length < 2 ^ (prefixWord ++ tailWord_28935).sum := by decide
  have hdescent : baseEnd_28935 < baseStart_28935 := by decide
  rcases family_descends (prefixWord ++ tailWord_28935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28991 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 7]
def baseStart_28991 : Nat := 118140960795 + 28991 * 2 ^ 59
def prefixEnd_28991 : Nat := 4983230072969 + 3 ^ 40 * 28991 * 2
def baseEnd_28991 : Nat := 3308070589911401395373

theorem tailTrace_28991 : CollatzResearch.WordTrace tailWord_28991 prefixEnd_28991 3308070589911401395373 := by
  unfold tailWord_28991
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057388637978033113718827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 704925758652022075812551 1057388637978033113718827)
  ·
    refine ⟨1586082956967049670578241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057388637978033113718827 1586082956967049670578241)
    ·
      refine ⟨1189562217725287252933681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1586082956967049670578241 1189562217725287252933681)
      ·
        refine ⟨892171663293965439700261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189562217725287252933681 892171663293965439700261)
        ·
          refine ⟨167282186867618519943799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 892171663293965439700261 167282186867618519943799)
          ·
            refine ⟨250923280301427779915699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167282186867618519943799 250923280301427779915699)
            ·
              refine ⟨376384920452141669873549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250923280301427779915699 376384920452141669873549)
              ·
                refine ⟨141144345169553126202581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376384920452141669873549 141144345169553126202581)
                ·
                  refine ⟨3308070589911401395373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141144345169553126202581 3308070589911401395373)
                  ·
                    rfl

theorem cell22_28991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_28991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28991 prefixEnd_28991 := by exact prefixLift 28991
  have htrace : WordTrace (prefixWord ++ tailWord_28991) baseStart_28991 baseEnd_28991 := by
    simpa [prefixWord, tailWord_28991, baseEnd_28991] using wordTrace_append hprefix tailTrace_28991
  have hstable : (prefixWord ++ tailWord_28991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28991).length < 2 ^ (prefixWord ++ tailWord_28991).sum := by decide
  have hdescent : baseEnd_28991 < baseStart_28991 := by decide
  rcases family_descends (prefixWord ++ tailWord_28991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28995 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 1, 3]
def baseStart_28995 : Nat := 118140960795 + 28995 * 2 ^ 59
def prefixEnd_28995 : Nat := 4983230072969 + 3 ^ 40 * 28995 * 2
def baseEnd_28995 : Nat := 9925581051479527086107

theorem tailTrace_28995 : CollatzResearch.WordTrace tailWord_28995 prefixEnd_28995 9925581051479527086107 := by
  unfold tailWord_28995
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057534529963541796864439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 705023019975694531242959 1057534529963541796864439)
  ·
    refine ⟨1586301794945312695296659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057534529963541796864439 1586301794945312695296659)
    ·
      refine ⟨2379452692417969042944989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586301794945312695296659 2379452692417969042944989)
      ·
        refine ⟨892294759656738391104371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2379452692417969042944989 892294759656738391104371)
        ·
          refine ⟨1338442139485107586656557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892294759656738391104371 1338442139485107586656557)
          ·
            refine ⟨501915802306915344996209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1338442139485107586656557 501915802306915344996209)
            ·
              refine ⟨376436851730186508747157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501915802306915344996209 376436851730186508747157)
              ·
                refine ⟨17645477424852492597523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376436851730186508747157 17645477424852492597523)
                ·
                  refine ⟨26468216137278738896285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17645477424852492597523 26468216137278738896285)
                  ·
                    refine ⟨9925581051479527086107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26468216137278738896285 9925581051479527086107)
                    ·
                      rfl

theorem cell22_28995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 3].length) (baseStart_28995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_28995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_28995 prefixEnd_28995 := by exact prefixLift 28995
  have htrace : WordTrace (prefixWord ++ tailWord_28995) baseStart_28995 baseEnd_28995 := by
    simpa [prefixWord, tailWord_28995, baseEnd_28995] using wordTrace_append hprefix tailTrace_28995
  have hstable : (prefixWord ++ tailWord_28995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28995).length < 2 ^ (prefixWord ++ tailWord_28995).sum := by decide
  have hdescent : baseEnd_28995 < baseStart_28995 := by decide
  rcases family_descends (prefixWord ++ tailWord_28995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29008 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_29008 : Nat := 118140960795 + 29008 * 2 ^ 59
def prefixEnd_29008 : Nat := 4983230072969 + 3 ^ 40 * 29008 * 2
def baseEnd_29008 : Nat := 3310010405717275503689

theorem tailTrace_29008 : CollatzResearch.WordTrace tailWord_29008 prefixEnd_29008 3310010405717275503689 := by
  unfold tailWord_29008
  simp only [CollatzResearch.WordTrace]
  refine ⟨529004339458222508543839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 705339119277630011391785 529004339458222508543839)
  ·
    refine ⟨793506509187333762815759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 529004339458222508543839 793506509187333762815759)
    ·
      refine ⟨1190259763781000644223639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793506509187333762815759 1190259763781000644223639)
      ·
        refine ⟨1785389645671500966335459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190259763781000644223639 1785389645671500966335459)
        ·
          refine ⟨2678084468507251449503189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785389645671500966335459 2678084468507251449503189)
          ·
            refine ⟨62767604730638705847731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2678084468507251449503189 62767604730638705847731)
            ·
              refine ⟨94151407095958058771597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62767604730638705847731 94151407095958058771597)
              ·
                refine ⟨35306777660984272039349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94151407095958058771597 35306777660984272039349)
                ·
                  refine ⟨3310010405717275503689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35306777660984272039349 3310010405717275503689)
                  ·
                    rfl

theorem cell22_29008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_29008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29008 prefixEnd_29008 := by exact prefixLift 29008
  have htrace : WordTrace (prefixWord ++ tailWord_29008) baseStart_29008 baseEnd_29008 := by
    simpa [prefixWord, tailWord_29008, baseEnd_29008] using wordTrace_append hprefix tailTrace_29008
  have hstable : (prefixWord ++ tailWord_29008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29008).length < 2 ^ (prefixWord ++ tailWord_29008).sum := by decide
  have hdescent : baseEnd_29008 < baseStart_29008 := by decide
  rcases family_descends (prefixWord ++ tailWord_29008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29046 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_29046 : Nat := 118140960795 + 29046 * 2 ^ 59
def prefixEnd_29046 : Nat := 4983230072969 + 3 ^ 40 * 29046 * 2
def baseEnd_29046 : Nat := 9943039393732394060951

theorem tailTrace_29046 : CollatzResearch.WordTrace tailWord_29046 prefixEnd_29046 9943039393732394060951 := by
  unfold tailWord_29046
  simp only [CollatzResearch.WordTrace]
  refine ⟨66212165798673594185687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 706263101852518337980661 66212165798673594185687)
  ·
    refine ⟨99318248698010391278531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66212165798673594185687 99318248698010391278531)
    ·
      refine ⟨148977373047015586917797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99318248698010391278531 148977373047015586917797)
      ·
        refine ⟨27933257446315422547087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148977373047015586917797 27933257446315422547087)
        ·
          refine ⟨41899886169473133820631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27933257446315422547087 41899886169473133820631)
          ·
            refine ⟨62849829254209700730947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41899886169473133820631 62849829254209700730947)
            ·
              refine ⟨94274743881314551096421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62849829254209700730947 94274743881314551096421)
              ·
                refine ⟨17676514477746478330579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94274743881314551096421 17676514477746478330579)
                ·
                  refine ⟨26514771716619717495869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17676514477746478330579 26514771716619717495869)
                  ·
                    refine ⟨9943039393732394060951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26514771716619717495869 9943039393732394060951)
                    ·
                      rfl

theorem cell22_29046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_29046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29046 prefixEnd_29046 := by exact prefixLift 29046
  have htrace : WordTrace (prefixWord ++ tailWord_29046) baseStart_29046 baseEnd_29046 := by
    simpa [prefixWord, tailWord_29046, baseEnd_29046] using wordTrace_append hprefix tailTrace_29046
  have hstable : (prefixWord ++ tailWord_29046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29046).length < 2 ^ (prefixWord ++ tailWord_29046).sum := by decide
  have hdescent : baseEnd_29046 < baseStart_29046 := by decide
  rcases family_descends (prefixWord ++ tailWord_29046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29068 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_29068 : Nat := 118140960795 + 29068 * 2 ^ 59
def prefixEnd_29068 : Nat := 4983230072969 + 3 ^ 40 * 29068 * 2
def baseEnd_29068 : Nat := 9950570443331670010883

theorem tailTrace_29068 : CollatzResearch.WordTrace tailWord_29068 prefixEnd_29068 9950570443331670010883 := by
  unfold tailWord_29068
  simp only [CollatzResearch.WordTrace]
  refine ⟨530098529349537632135929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 706798039132716842847905 530098529349537632135929)
  ·
    refine ⟨397573897012153224101947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 530098529349537632135929 397573897012153224101947)
    ·
      refine ⟨596360845518229836152921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397573897012153224101947 596360845518229836152921)
      ·
        refine ⟨447270634138672377114691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596360845518229836152921 447270634138672377114691)
        ·
          refine ⟨670905951208008565672037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447270634138672377114691 670905951208008565672037)
          ·
            refine ⟨125794865851501606063507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670905951208008565672037 125794865851501606063507)
            ·
              refine ⟨188692298777252409095261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125794865851501606063507 188692298777252409095261)
              ·
                refine ⟨70759612041469653410723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188692298777252409095261 70759612041469653410723)
                ·
                  refine ⟨106139418062204480116085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70759612041469653410723 106139418062204480116085)
                  ·
                    refine ⟨9950570443331670010883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106139418062204480116085 9950570443331670010883)
                    ·
                      rfl

theorem cell22_29068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_29068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29068 prefixEnd_29068 := by exact prefixLift 29068
  have htrace : WordTrace (prefixWord ++ tailWord_29068) baseStart_29068 baseEnd_29068 := by
    simpa [prefixWord, tailWord_29068, baseEnd_29068] using wordTrace_append hprefix tailTrace_29068
  have hstable : (prefixWord ++ tailWord_29068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29068).length < 2 ^ (prefixWord ++ tailWord_29068).sum := by decide
  have hdescent : baseEnd_29068 < baseStart_29068 := by decide
  rcases family_descends (prefixWord ++ tailWord_29068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29070 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_29070 : Nat := 118140960795 + 29070 * 2 ^ 59
def prefixEnd_29070 : Nat := 4983230072969 + 3 ^ 40 * 29070 * 2
def baseEnd_29070 : Nat := 3317085028068110486959

theorem tailTrace_29070 : CollatzResearch.WordTrace tailWord_29070 prefixEnd_29070 3317085028068110486959 := by
  unfold tailWord_29070
  simp only [CollatzResearch.WordTrace]
  refine ⟨132533750586478700730583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 706846669794553070563109 132533750586478700730583)
  ·
    refine ⟨198800625879718051095875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132533750586478700730583 198800625879718051095875)
    ·
      refine ⟨298200938819577076643813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198800625879718051095875 298200938819577076643813)
      ·
        refine ⟨55912676028670701870715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298200938819577076643813 55912676028670701870715)
        ·
          refine ⟨83869014043006052806073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55912676028670701870715 83869014043006052806073)
          ·
            refine ⟨62901760532254539604555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83869014043006052806073 62901760532254539604555)
            ·
              refine ⟨94352640798381809406833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62901760532254539604555 94352640798381809406833)
              ·
                refine ⟨70764480598786357055125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94352640798381809406833 70764480598786357055125)
                ·
                  refine ⟨3317085028068110486959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70764480598786357055125 3317085028068110486959)
                  ·
                    rfl

theorem cell22_29070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_29070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29070 prefixEnd_29070 := by exact prefixLift 29070
  have htrace : WordTrace (prefixWord ++ tailWord_29070) baseStart_29070 baseEnd_29070 := by
    simpa [prefixWord, tailWord_29070, baseEnd_29070] using wordTrace_append hprefix tailTrace_29070
  have hstable : (prefixWord ++ tailWord_29070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29070).length < 2 ^ (prefixWord ++ tailWord_29070).sum := by decide
  have hdescent : baseEnd_29070 < baseStart_29070 := by decide
  rcases family_descends (prefixWord ++ tailWord_29070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29130 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_29130 : Nat := 118140960795 + 29130 * 2 ^ 59
def prefixEnd_29130 : Nat := 4983230072969 + 3 ^ 40 * 29130 * 2
def baseEnd_29130 : Nat := 9971794310384174960693

theorem tailTrace_29130 : CollatzResearch.WordTrace tailWord_29130 prefixEnd_29130 9971794310384174960693 := by
  unfold tailWord_29130
  simp only [CollatzResearch.WordTrace]
  refine ⟨265614596118614963257211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 708305589649639902019229 265614596118614963257211)
  ·
    refine ⟨398421894177922444885817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265614596118614963257211 398421894177922444885817)
    ·
      refine ⟨298816420633441833664363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398421894177922444885817 298816420633441833664363)
      ·
        refine ⟨448224630950162750496545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298816420633441833664363 448224630950162750496545)
        ·
          refine ⟨336168473212622062872409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448224630950162750496545 336168473212622062872409)
          ·
            refine ⟨252126354909466547154307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336168473212622062872409 252126354909466547154307)
            ·
              refine ⟨378189532364199820731461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252126354909466547154307 378189532364199820731461)
              ·
                refine ⟨70910537318287466387149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378189532364199820731461 70910537318287466387149)
                ·
                  refine ⟨26591451494357799895181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70910537318287466387149 26591451494357799895181)
                  ·
                    refine ⟨9971794310384174960693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26591451494357799895181 9971794310384174960693)
                    ·
                      rfl

theorem cell22_29130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_29130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29130 prefixEnd_29130 := by exact prefixLift 29130
  have htrace : WordTrace (prefixWord ++ tailWord_29130) baseStart_29130 baseEnd_29130 := by
    simpa [prefixWord, tailWord_29130, baseEnd_29130] using wordTrace_append hprefix tailTrace_29130
  have hstable : (prefixWord ++ tailWord_29130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29130).length < 2 ^ (prefixWord ++ tailWord_29130).sum := by decide
  have hdescent : baseEnd_29130 < baseStart_29130 := by decide
  rcases family_descends (prefixWord ++ tailWord_29130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29132 : List Nat := [2, 2, 1, 4, 3, 2, 2, 6]
def baseStart_29132 : Nat := 118140960795 + 29132 * 2 ^ 59
def prefixEnd_29132 : Nat := 4983230072969 + 3 ^ 40 * 29132 * 2
def baseEnd_29132 : Nat := 1108053216806315156743

theorem tailTrace_29132 : CollatzResearch.WordTrace tailWord_29132 prefixEnd_29132 1108053216806315156743 := by
  unfold tailWord_29132
  simp only [CollatzResearch.WordTrace]
  refine ⟨531265665233607097300825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 708354220311476129734433 531265665233607097300825)
  ·
    refine ⟨398449248925205322975619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 531265665233607097300825 398449248925205322975619)
    ·
      refine ⟨597673873387807984463429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398449248925205322975619 597673873387807984463429)
      ·
        refine ⟨112063851260213997086893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 597673873387807984463429 112063851260213997086893)
        ·
          refine ⟨42023944222580248907585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112063851260213997086893 42023944222580248907585)
          ·
            refine ⟨31517958166935186680689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42023944222580248907585 31517958166935186680689)
            ·
              refine ⟨23638468625201390010517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31517958166935186680689 23638468625201390010517)
              ·
                refine ⟨1108053216806315156743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23638468625201390010517 1108053216806315156743)
                ·
                  rfl

theorem cell22_29132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 6].length) (baseStart_29132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29132 prefixEnd_29132 := by exact prefixLift 29132
  have htrace : WordTrace (prefixWord ++ tailWord_29132) baseStart_29132 baseEnd_29132 := by
    simpa [prefixWord, tailWord_29132, baseEnd_29132] using wordTrace_append hprefix tailTrace_29132
  have hstable : (prefixWord ++ tailWord_29132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29132).length < 2 ^ (prefixWord ++ tailWord_29132).sum := by decide
  have hdescent : baseEnd_29132 < baseStart_29132 := by decide
  rcases family_descends (prefixWord ++ tailWord_29132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29164 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_29164 : Nat := 118140960795 + 29164 * 2 ^ 59
def prefixEnd_29164 : Nat := 4983230072969 + 3 ^ 40 * 29164 * 2
def baseEnd_29164 : Nat := 9983433205219419610589

theorem tailTrace_29164 : CollatzResearch.WordTrace tailWord_29164 prefixEnd_29164 9983433205219419610589 := by
  unfold tailWord_29164
  simp only [CollatzResearch.WordTrace]
  refine ⟨531849233175641829883273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 709132310900855773177697 531849233175641829883273)
  ·
    refine ⟨398886924881731372412455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 531849233175641829883273 398886924881731372412455)
    ·
      refine ⟨598330387322597058618683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398886924881731372412455 598330387322597058618683)
      ·
        refine ⟨897495580983895587928025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598330387322597058618683 897495580983895587928025)
        ·
          refine ⟨673121685737921690946019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897495580983895587928025 673121685737921690946019)
          ·
            refine ⟨1009682528606882536419029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673121685737921690946019 1009682528606882536419029)
            ·
              refine ⟨23664434264223809447321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1009682528606882536419029 23664434264223809447321)
              ·
                refine ⟨17748325698167857085491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23664434264223809447321 17748325698167857085491)
                ·
                  refine ⟨26622488547251785628237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17748325698167857085491 26622488547251785628237)
                  ·
                    refine ⟨9983433205219419610589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26622488547251785628237 9983433205219419610589)
                    ·
                      rfl

theorem cell22_29164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_29164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29164 prefixEnd_29164 := by exact prefixLift 29164
  have htrace : WordTrace (prefixWord ++ tailWord_29164) baseStart_29164 baseEnd_29164 := by
    simpa [prefixWord, tailWord_29164, baseEnd_29164] using wordTrace_append hprefix tailTrace_29164
  have hstable : (prefixWord ++ tailWord_29164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29164).length < 2 ^ (prefixWord ++ tailWord_29164).sum := by decide
  have hdescent : baseEnd_29164 < baseStart_29164 := by decide
  rcases family_descends (prefixWord ++ tailWord_29164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29237 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_29237 : Nat := 118140960795 + 29237 * 2 ^ 59
def prefixEnd_29237 : Nat := 4983230072969 + 3 ^ 40 * 29237 * 2
def baseEnd_29237 : Nat := 10008422597071562535365

theorem tailTrace_29237 : CollatzResearch.WordTrace tailWord_29237 prefixEnd_29237 10008422597071562535365 := by
  unfold tailWord_29237
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066360995086817127173965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 710907330057878084782643 1066360995086817127173965)
  ·
    refine ⟨399885373157556422690237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1066360995086817127173965 399885373157556422690237)
    ·
      refine ⟨149957014934083658508839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399885373157556422690237 149957014934083658508839)
      ·
        refine ⟨224935522401125487763259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149957014934083658508839 224935522401125487763259)
        ·
          refine ⟨337403283601688231644889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224935522401125487763259 337403283601688231644889)
          ·
            refine ⟨253052462701266173733667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337403283601688231644889 253052462701266173733667)
            ·
              refine ⟨379578694051899260600501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253052462701266173733667 379578694051899260600501)
              ·
                refine ⟨35585502567365555681297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379578694051899260600501 35585502567365555681297)
                ·
                  refine ⟨26689126925524166760973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35585502567365555681297 26689126925524166760973)
                  ·
                    refine ⟨10008422597071562535365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26689126925524166760973 10008422597071562535365)
                    ·
                      rfl

theorem cell22_29237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_29237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29237 prefixEnd_29237 := by exact prefixLift 29237
  have htrace : WordTrace (prefixWord ++ tailWord_29237) baseStart_29237 baseEnd_29237 := by
    simpa [prefixWord, tailWord_29237, baseEnd_29237] using wordTrace_append hprefix tailTrace_29237
  have hstable : (prefixWord ++ tailWord_29237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29237).length < 2 ^ (prefixWord ++ tailWord_29237).sum := by decide
  have hdescent : baseEnd_29237 < baseStart_29237 := by decide
  rcases family_descends (prefixWord ++ tailWord_29237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29254 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_29254 : Nat := 118140960795 + 29254 * 2 ^ 59
def prefixEnd_29254 : Nat := 4983230072969 + 3 ^ 40 * 29254 * 2
def baseEnd_29254 : Nat := 10014242044489184860313

theorem tailTrace_29254 : CollatzResearch.WordTrace tailWord_29254 prefixEnd_29254 10014242044489184860313 := by
  unfold tailWord_29254
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343157375788407204463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 711320690683486020361877 33343157375788407204463)
  ·
    refine ⟨50014736063682610806695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33343157375788407204463 50014736063682610806695)
    ·
      refine ⟨75022104095523916210043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50014736063682610806695 75022104095523916210043)
      ·
        refine ⟨112533156143285874315065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75022104095523916210043 112533156143285874315065)
        ·
          refine ⟨84399867107464405736299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112533156143285874315065 84399867107464405736299)
          ·
            refine ⟨126599800661196608604449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84399867107464405736299 126599800661196608604449)
            ·
              refine ⟨94949850495897456453337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126599800661196608604449 94949850495897456453337)
              ·
                refine ⟨71212387871923092340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94949850495897456453337 71212387871923092340003)
                ·
                  refine ⟨106818581807884638510005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71212387871923092340003 106818581807884638510005)
                  ·
                    refine ⟨10014242044489184860313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106818581807884638510005 10014242044489184860313)
                    ·
                      rfl

theorem cell22_29254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_29254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29254 prefixEnd_29254 := by exact prefixLift 29254
  have htrace : WordTrace (prefixWord ++ tailWord_29254) baseStart_29254 baseEnd_29254 := by
    simpa [prefixWord, tailWord_29254, baseEnd_29254] using wordTrace_append hprefix tailTrace_29254
  have hstable : (prefixWord ++ tailWord_29254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29254).length < 2 ^ (prefixWord ++ tailWord_29254).sum := by decide
  have hdescent : baseEnd_29254 < baseStart_29254 := by decide
  rcases family_descends (prefixWord ++ tailWord_29254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29295 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 5]
def baseStart_29295 : Nat := 118140960795 + 29295 * 2 ^ 59
def prefixEnd_29295 : Nat := 4983230072969 + 3 ^ 40 * 29295 * 2
def baseEnd_29295 : Nat := 3342759060792914861729

theorem tailTrace_29295 : CollatzResearch.WordTrace tailWord_29295 prefixEnd_29295 3342759060792914861729 := by
  unfold tailWord_29295
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068476428876693032785339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 712317619251128688523559 1068476428876693032785339)
  ·
    refine ⟨1602714643315039549178009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068476428876693032785339 1602714643315039549178009)
    ·
      refine ⟨1202035982486279661883507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1602714643315039549178009 1202035982486279661883507)
      ·
        refine ⟨1803053973729419492825261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202035982486279661883507 1803053973729419492825261)
        ·
          refine ⟨676145240148532309809473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1803053973729419492825261 676145240148532309809473)
          ·
            refine ⟨507108930111399232357105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676145240148532309809473 507108930111399232357105)
            ·
              refine ⟨380331697583549424267829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507108930111399232357105 380331697583549424267829)
              ·
                refine ⟨35656096648457758525109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380331697583549424267829 35656096648457758525109)
                ·
                  refine ⟨3342759060792914861729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35656096648457758525109 3342759060792914861729)
                  ·
                    rfl

theorem cell22_29295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 5].length) (baseStart_29295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29295 prefixEnd_29295 := by exact prefixLift 29295
  have htrace : WordTrace (prefixWord ++ tailWord_29295) baseStart_29295 baseEnd_29295 := by
    simpa [prefixWord, tailWord_29295, baseEnd_29295] using wordTrace_append hprefix tailTrace_29295
  have hstable : (prefixWord ++ tailWord_29295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29295).length < 2 ^ (prefixWord ++ tailWord_29295).sum := by decide
  have hdescent : baseEnd_29295 < baseStart_29295 := by decide
  rcases family_descends (prefixWord ++ tailWord_29295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29301 : List Nat := [1, 3, 4, 2, 3, 1, 2, 6]
def baseStart_29301 : Nat := 118140960795 + 29301 * 2 ^ 59
def prefixEnd_29301 : Nat := 4983230072969 + 3 ^ 40 * 29301 * 2
def baseEnd_29301 : Nat := 1114481233888525437241

theorem tailTrace_29301 : CollatzResearch.WordTrace tailWord_29301 prefixEnd_29301 1114481233888525437241 := by
  unfold tailWord_29301
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068695266854956057503757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 712463511236637371669171 1068695266854956057503757)
  ·
    refine ⟨400760725070608521563909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1068695266854956057503757 400760725070608521563909)
    ·
      refine ⟨75142635950739097793233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400760725070608521563909 75142635950739097793233)
      ·
        refine ⟨56356976963054323344925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75142635950739097793233 56356976963054323344925)
        ·
          refine ⟨21133866361145371254347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56356976963054323344925 21133866361145371254347)
          ·
            refine ⟨31700799541718056881521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133866361145371254347 31700799541718056881521)
            ·
              refine ⟨23775599656288542661141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31700799541718056881521 23775599656288542661141)
              ·
                refine ⟨1114481233888525437241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23775599656288542661141 1114481233888525437241)
                ·
                  rfl

theorem cell22_29301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 6].length) (baseStart_29301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29301 prefixEnd_29301 := by exact prefixLift 29301
  have htrace : WordTrace (prefixWord ++ tailWord_29301) baseStart_29301 baseEnd_29301 := by
    simpa [prefixWord, tailWord_29301, baseEnd_29301] using wordTrace_append hprefix tailTrace_29301
  have hstable : (prefixWord ++ tailWord_29301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29301).length < 2 ^ (prefixWord ++ tailWord_29301).sum := by decide
  have hdescent : baseEnd_29301 < baseStart_29301 := by decide
  rcases family_descends (prefixWord ++ tailWord_29301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29316 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_29316 : Nat := 118140960795 + 29316 * 2 ^ 59
def prefixEnd_29316 : Nat := 4983230072969 + 3 ^ 40 * 29316 * 2
def baseEnd_29316 : Nat := 10035465911541689810123

theorem tailTrace_29316 : CollatzResearch.WordTrace tailWord_29316 prefixEnd_29316 10035465911541689810123 := by
  unfold tailWord_29316
  simp only [CollatzResearch.WordTrace]
  refine ⟨534621180900306809649901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 712828241200409079533201 534621180900306809649901)
  ·
    refine ⟨200482942837615053618713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 534621180900306809649901 200482942837615053618713)
    ·
      refine ⟨150362207128211290214035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200482942837615053618713 150362207128211290214035)
      ·
        refine ⟨225543310692316935321053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150362207128211290214035 225543310692316935321053)
        ·
          refine ⟨84578741509618850745395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225543310692316935321053 84578741509618850745395)
          ·
            refine ⟨126868112264428276118093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84578741509618850745395 126868112264428276118093)
            ·
              refine ⟨47575542099160603544285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126868112264428276118093 47575542099160603544285)
              ·
                refine ⟨17840828287185226329107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47575542099160603544285 17840828287185226329107)
                ·
                  refine ⟨26761242430777839493661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17840828287185226329107 26761242430777839493661)
                  ·
                    refine ⟨10035465911541689810123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26761242430777839493661 10035465911541689810123)
                    ·
                      rfl

theorem cell22_29316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_29316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29316 prefixEnd_29316 := by exact prefixLift 29316
  have htrace : WordTrace (prefixWord ++ tailWord_29316) baseStart_29316 baseEnd_29316 := by
    simpa [prefixWord, tailWord_29316, baseEnd_29316] using wordTrace_append hprefix tailTrace_29316
  have hstable : (prefixWord ++ tailWord_29316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29316).length < 2 ^ (prefixWord ++ tailWord_29316).sum := by decide
  have hdescent : baseEnd_29316 < baseStart_29316 := by decide
  rcases family_descends (prefixWord ++ tailWord_29316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29359 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 1, 4]
def baseStart_29359 : Nat := 118140960795 + 29359 * 2 ^ 59
def prefixEnd_29359 : Nat := 4983230072969 + 3 ^ 40 * 29359 * 2
def baseEnd_29359 : Nat := 10050185690303910984991

theorem tailTrace_29359 : CollatzResearch.WordTrace tailWord_29359 prefixEnd_29359 10050185690303910984991 := by
  unfold tailWord_29359
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070810700644831963115131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 713873800429887975410087 1070810700644831963115131)
  ·
    refine ⟨1606216050967247944672697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070810700644831963115131 1606216050967247944672697)
    ·
      refine ⟨1204662038225435958504523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1606216050967247944672697 1204662038225435958504523)
      ·
        refine ⟨1806993057338153937756785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204662038225435958504523 1806993057338153937756785)
        ·
          refine ⟨1355244793003615453317589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806993057338153937756785 1355244793003615453317589)
          ·
            refine ⟨31763549836022237187131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1355244793003615453317589 31763549836022237187131)
            ·
              refine ⟨47645324754033355780697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31763549836022237187131 47645324754033355780697)
              ·
                refine ⟨35733993565525016835523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47645324754033355780697 35733993565525016835523)
                ·
                  refine ⟨53600990348287525253285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35733993565525016835523 53600990348287525253285)
                  ·
                    refine ⟨10050185690303910984991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53600990348287525253285 10050185690303910984991)
                    ·
                      rfl

theorem cell22_29359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_29359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29359 prefixEnd_29359 := by exact prefixLift 29359
  have htrace : WordTrace (prefixWord ++ tailWord_29359) baseStart_29359 baseEnd_29359 := by
    simpa [prefixWord, tailWord_29359, baseEnd_29359] using wordTrace_append hprefix tailTrace_29359
  have hstable : (prefixWord ++ tailWord_29359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29359).length < 2 ^ (prefixWord ++ tailWord_29359).sum := by decide
  have hdescent : baseEnd_29359 < baseStart_29359 := by decide
  rcases family_descends (prefixWord ++ tailWord_29359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29372 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_29372 : Nat := 118140960795 + 29372 * 2 ^ 59
def prefixEnd_29372 : Nat := 4983230072969 + 3 ^ 40 * 29372 * 2
def baseEnd_29372 : Nat := 10054635855976210409951

theorem tailTrace_29372 : CollatzResearch.WordTrace tailWord_29372 prefixEnd_29372 10054635855976210409951 := by
  unfold tailWord_29372
  simp only [CollatzResearch.WordTrace]
  refine ⟨535642424798867591669185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 714189899731823455558913 535642424798867591669185)
  ·
    refine ⟨401731818599150693751889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 535642424798867591669185 401731818599150693751889)
    ·
      refine ⟨301298863949363020313917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401731818599150693751889 301298863949363020313917)
      ·
        refine ⟨112987073981011132617719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301298863949363020313917 112987073981011132617719)
        ·
          refine ⟨169480610971516698926579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112987073981011132617719 169480610971516698926579)
          ·
            refine ⟨254220916457275048389869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169480610971516698926579 254220916457275048389869)
            ·
              refine ⟨95332843671478143146201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254220916457275048389869 95332843671478143146201)
              ·
                refine ⟨71499632753608607359651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95332843671478143146201 71499632753608607359651)
                ·
                  refine ⟨107249449130412911039477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71499632753608607359651 107249449130412911039477)
                  ·
                    refine ⟨10054635855976210409951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107249449130412911039477 10054635855976210409951)
                    ·
                      rfl

theorem cell22_29372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_29372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29372 prefixEnd_29372 := by exact prefixLift 29372
  have htrace : WordTrace (prefixWord ++ tailWord_29372) baseStart_29372 baseEnd_29372 := by
    simpa [prefixWord, tailWord_29372, baseEnd_29372] using wordTrace_append hprefix tailTrace_29372
  have hstable : (prefixWord ++ tailWord_29372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29372).length < 2 ^ (prefixWord ++ tailWord_29372).sum := by decide
  have hdescent : baseEnd_29372 < baseStart_29372 := by decide
  rcases family_descends (prefixWord ++ tailWord_29372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29374 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_29374 : Nat := 118140960795 + 29374 * 2 ^ 59
def prefixEnd_29374 : Nat := 4983230072969 + 3 ^ 40 * 29374 * 2
def baseEnd_29374 : Nat := 3351773498949623953315

theorem tailTrace_29374 : CollatzResearch.WordTrace tailWord_29374 prefixEnd_29374 3351773498949623953315 := by
  unfold tailWord_29374
  simp only [CollatzResearch.WordTrace]
  refine ⟨133919724448811190613897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 714238530393659683274117 133919724448811190613897)
  ·
    refine ⟨100439793336608392960423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133919724448811190613897 100439793336608392960423)
    ·
      refine ⟨150659690004912589440635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100439793336608392960423 150659690004912589440635)
      ·
        refine ⟨225989535007368884160953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150659690004912589440635 225989535007368884160953)
        ·
          refine ⟨169492151255526663120715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225989535007368884160953 169492151255526663120715)
          ·
            refine ⟨254238226883289994681073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169492151255526663120715 254238226883289994681073)
            ·
              refine ⟨190678670162467496010805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254238226883289994681073 190678670162467496010805)
              ·
                refine ⟨17876125327731327751013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190678670162467496010805 17876125327731327751013)
                ·
                  refine ⟨3351773498949623953315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17876125327731327751013 3351773498949623953315)
                  ·
                    rfl

theorem cell22_29374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_29374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29374 prefixEnd_29374 := by exact prefixLift 29374
  have htrace : WordTrace (prefixWord ++ tailWord_29374) baseStart_29374 baseEnd_29374 := by
    simpa [prefixWord, tailWord_29374, baseEnd_29374] using wordTrace_append hprefix tailTrace_29374
  have hstable : (prefixWord ++ tailWord_29374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29374).length < 2 ^ (prefixWord ++ tailWord_29374).sum := by decide
  have hdescent : baseEnd_29374 < baseStart_29374 := by decide
  rcases family_descends (prefixWord ++ tailWord_29374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29417 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_29417 : Nat := 118140960795 + 29417 * 2 ^ 59
def prefixEnd_29417 : Nat := 4983230072969 + 3 ^ 40 * 29417 * 2
def baseEnd_29417 : Nat := 10070040275611093034813

theorem tailTrace_29417 : CollatzResearch.WordTrace tailWord_29417 prefixEnd_29417 10070040275611093034813 := by
  unfold tailWord_29417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072926134434707868726505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 715284089623138579151003 1072926134434707868726505)
  ·
    refine ⟨804694600826030901544879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1072926134434707868726505 804694600826030901544879)
    ·
      refine ⟨1207041901239046352317319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804694600826030901544879 1207041901239046352317319)
      ·
        refine ⟨1810562851858569528475979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207041901239046352317319 1810562851858569528475979)
        ·
          refine ⟨2715844277787854292713969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810562851858569528475979 2715844277787854292713969)
          ·
            refine ⟨2036883208340890719535477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715844277787854292713969 2036883208340890719535477)
            ·
              refine ⟨190957800781958504956451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2036883208340890719535477 190957800781958504956451)
              ·
                refine ⟨286436701172937757434677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190957800781958504956451 286436701172937757434677)
                ·
                  refine ⟨26853440734962914759501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286436701172937757434677 26853440734962914759501)
                  ·
                    refine ⟨10070040275611093034813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26853440734962914759501 10070040275611093034813)
                    ·
                      rfl

theorem cell22_29417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_29417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29417 prefixEnd_29417 := by exact prefixLift 29417
  have htrace : WordTrace (prefixWord ++ tailWord_29417) baseStart_29417 baseEnd_29417 := by
    simpa [prefixWord, tailWord_29417, baseEnd_29417] using wordTrace_append hprefix tailTrace_29417
  have hstable : (prefixWord ++ tailWord_29417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29417).length < 2 ^ (prefixWord ++ tailWord_29417).sum := by decide
  have hdescent : baseEnd_29417 < baseStart_29417 := by decide
  rcases family_descends (prefixWord ++ tailWord_29417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29539 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 2, 4]
def baseStart_29539 : Nat := 118140960795 + 29539 * 2 ^ 59
def prefixEnd_29539 : Nat := 4983230072969 + 3 ^ 40 * 29539 * 2
def baseEnd_29539 : Nat := 10111803368843441484439

theorem tailTrace_29539 : CollatzResearch.WordTrace tailWord_29539 prefixEnd_29539 10111803368843441484439 := by
  unfold tailWord_29539
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077375839992722704667671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 718250559995148469778447 1077375839992722704667671)
  ·
    refine ⟨1616063759989084057001507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1077375839992722704667671 1616063759989084057001507)
    ·
      refine ⟨2424095639983626085502261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616063759989084057001507 2424095639983626085502261)
      ·
        refine ⟨227258966248464945515837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2424095639983626085502261 227258966248464945515837)
        ·
          refine ⟨85222112343174354568439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227258966248464945515837 85222112343174354568439)
          ·
            refine ⟨127833168514761531852659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85222112343174354568439 127833168514761531852659)
            ·
              refine ⟨191749752772142297778989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127833168514761531852659 191749752772142297778989)
              ·
                refine ⟨71906157289553361667121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191749752772142297778989 71906157289553361667121)
                ·
                  refine ⟨53929617967165021250341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71906157289553361667121 53929617967165021250341)
                  ·
                    refine ⟨10111803368843441484439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53929617967165021250341 10111803368843441484439)
                    ·
                      rfl

theorem cell22_29539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_29539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29539 prefixEnd_29539 := by exact prefixLift 29539
  have htrace : WordTrace (prefixWord ++ tailWord_29539) baseStart_29539 baseEnd_29539 := by
    simpa [prefixWord, tailWord_29539, baseEnd_29539] using wordTrace_append hprefix tailTrace_29539
  have hstable : (prefixWord ++ tailWord_29539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29539).length < 2 ^ (prefixWord ++ tailWord_29539).sum := by decide
  have hdescent : baseEnd_29539 < baseStart_29539 := by decide
  rcases family_descends (prefixWord ++ tailWord_29539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29558 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_29558 : Nat := 118140960795 + 29558 * 2 ^ 59
def prefixEnd_29558 : Nat := 4983230072969 + 3 ^ 40 * 29558 * 2
def baseEnd_29558 : Nat := 10118307457133725259381

theorem tailTrace_29558 : CollatzResearch.WordTrace tailWord_29558 prefixEnd_29558 10118307457133725259381 := by
  unfold tailWord_29558
  simp only [CollatzResearch.WordTrace]
  refine ⟨67379301682743059350583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 718712551282592633072885 67379301682743059350583)
  ·
    refine ⟨101068952524114589025875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67379301682743059350583 101068952524114589025875)
    ·
      refine ⟨151603428786171883538813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101068952524114589025875 151603428786171883538813)
      ·
        refine ⟨56851285794814456327055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151603428786171883538813 56851285794814456327055)
        ·
          refine ⟨85276928692221684490583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56851285794814456327055 85276928692221684490583)
          ·
            refine ⟨127915393038332526735875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85276928692221684490583 127915393038332526735875)
            ·
              refine ⟨191873089557498790103813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127915393038332526735875 191873089557498790103813)
              ·
                refine ⟨35976204292031023144465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191873089557498790103813 35976204292031023144465)
                ·
                  refine ⟨26982153219023267358349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35976204292031023144465 26982153219023267358349)
                  ·
                    refine ⟨10118307457133725259381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26982153219023267358349 10118307457133725259381)
                    ·
                      rfl

theorem cell22_29558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_29558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29558 prefixEnd_29558 := by exact prefixLift 29558
  have htrace : WordTrace (prefixWord ++ tailWord_29558) baseStart_29558 baseEnd_29558 := by
    simpa [prefixWord, tailWord_29558, baseEnd_29558] using wordTrace_append hprefix tailTrace_29558
  have hstable : (prefixWord ++ tailWord_29558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29558).length < 2 ^ (prefixWord ++ tailWord_29558).sum := by decide
  have hdescent : baseEnd_29558 < baseStart_29558 := by decide
  rcases family_descends (prefixWord ++ tailWord_29558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29567 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_29567 : Nat := 118140960795 + 29567 * 2 ^ 59
def prefixEnd_29567 : Nat := 4983230072969 + 3 ^ 40 * 29567 * 2
def baseEnd_29567 : Nat := 10121388341060701784353

theorem tailTrace_29567 : CollatzResearch.WordTrace tailWord_29567 prefixEnd_29567 10121388341060701784353 := by
  unfold tailWord_29567
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078397083891283486686955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 718931389260855657791303 1078397083891283486686955)
  ·
    refine ⟨1617595625836925230030433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1078397083891283486686955 1617595625836925230030433)
    ·
      refine ⟨1213196719377693922522825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1617595625836925230030433 1213196719377693922522825)
      ·
        refine ⟨909897539533270441892119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1213196719377693922522825 909897539533270441892119)
        ·
          refine ⟨1364846309299905662838179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909897539533270441892119 1364846309299905662838179)
          ·
            refine ⟨2047269463949858494257269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364846309299905662838179 2047269463949858494257269)
            ·
              refine ⟨191931512245299233836619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2047269463949858494257269 191931512245299233836619)
              ·
                refine ⟨287897268367948850754929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191931512245299233836619 287897268367948850754929)
                ·
                  refine ⟨215922951275961638066197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287897268367948850754929 215922951275961638066197)
                  ·
                    refine ⟨10121388341060701784353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215922951275961638066197 10121388341060701784353)
                    ·
                      rfl

theorem cell22_29567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_29567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29567 prefixEnd_29567 := by exact prefixLift 29567
  have htrace : WordTrace (prefixWord ++ tailWord_29567) baseStart_29567 baseEnd_29567 := by
    simpa [prefixWord, tailWord_29567, baseEnd_29567] using wordTrace_append hprefix tailTrace_29567
  have hstable : (prefixWord ++ tailWord_29567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29567).length < 2 ^ (prefixWord ++ tailWord_29567).sum := by decide
  have hdescent : baseEnd_29567 < baseStart_29567 := by decide
  rcases family_descends (prefixWord ++ tailWord_29567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29590 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_29590 : Nat := 118140960795 + 29590 * 2 ^ 59
def prefixEnd_29590 : Nat := 4983230072969 + 3 ^ 40 * 29590 * 2
def baseEnd_29590 : Nat := 10129261711096308459283

theorem tailTrace_29590 : CollatzResearch.WordTrace tailWord_29590 prefixEnd_29590 10129261711096308459283 := by
  unfold tailWord_29590
  simp only [CollatzResearch.WordTrace]
  refine ⟨67452247675497400923389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 719490641871972276516149 67452247675497400923389)
  ·
    refine ⟨25294592878311525346271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67452247675497400923389 25294592878311525346271)
    ·
      refine ⟨37941889317467288019407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25294592878311525346271 37941889317467288019407)
      ·
        refine ⟨56912833976200932029111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37941889317467288019407 56912833976200932029111)
        ·
          refine ⟨85369250964301398043667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56912833976200932029111 85369250964301398043667)
          ·
            refine ⟨128053876446452097065501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85369250964301398043667 128053876446452097065501)
            ·
              refine ⟨48020203667419536399563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128053876446452097065501 48020203667419536399563)
              ·
                refine ⟨72030305501129304599345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48020203667419536399563 72030305501129304599345)
                ·
                  refine ⟨54022729125846978449509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72030305501129304599345 54022729125846978449509)
                  ·
                    refine ⟨10129261711096308459283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54022729125846978449509 10129261711096308459283)
                    ·
                      rfl

theorem cell22_29590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_29590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29590 prefixEnd_29590 := by exact prefixLift 29590
  have htrace : WordTrace (prefixWord ++ tailWord_29590) baseStart_29590 baseEnd_29590 := by
    simpa [prefixWord, tailWord_29590, baseEnd_29590] using wordTrace_append hprefix tailTrace_29590
  have hstable : (prefixWord ++ tailWord_29590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29590).length < 2 ^ (prefixWord ++ tailWord_29590).sum := by decide
  have hdescent : baseEnd_29590 < baseStart_29590 := by decide
  rcases family_descends (prefixWord ++ tailWord_29590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29620 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_29620 : Nat := 118140960795 + 29620 * 2 ^ 59
def prefixEnd_29620 : Nat := 4983230072969 + 3 ^ 40 * 29620 * 2
def baseEnd_29620 : Nat := 10139531324186230209191

theorem tailTrace_29620 : CollatzResearch.WordTrace tailWord_29620 prefixEnd_29620 10139531324186230209191 := by
  unfold tailWord_29620
  simp only [CollatzResearch.WordTrace]
  refine ⟨540165076349636769183157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 720220101799515692244209 540165076349636769183157)
  ·
    refine ⟨50640475907778447110921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 540165076349636769183157 50640475907778447110921)
    ·
      refine ⟨37980356930833835333191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50640475907778447110921 37980356930833835333191)
      ·
        refine ⟨56970535396250752999787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37980356930833835333191 56970535396250752999787)
        ·
          refine ⟨85455803094376129499681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56970535396250752999787 85455803094376129499681)
          ·
            refine ⟨64091852320782097124761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85455803094376129499681 64091852320782097124761)
            ·
              refine ⟨48068889240586572843571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64091852320782097124761 48068889240586572843571)
              ·
                refine ⟨72103333860879859265357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48068889240586572843571 72103333860879859265357)
                ·
                  refine ⟨27038750197829947224509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72103333860879859265357 27038750197829947224509)
                  ·
                    refine ⟨10139531324186230209191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27038750197829947224509 10139531324186230209191)
                    ·
                      rfl

theorem cell22_29620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_29620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29620 prefixEnd_29620 := by exact prefixLift 29620
  have htrace : WordTrace (prefixWord ++ tailWord_29620) baseStart_29620 baseEnd_29620 := by
    simpa [prefixWord, tailWord_29620, baseEnd_29620] using wordTrace_append hprefix tailTrace_29620
  have hstable : (prefixWord ++ tailWord_29620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29620).length < 2 ^ (prefixWord ++ tailWord_29620).sum := by decide
  have hdescent : baseEnd_29620 < baseStart_29620 := by decide
  rcases family_descends (prefixWord ++ tailWord_29620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29644 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_29644 : Nat := 118140960795 + 29644 * 2 ^ 59
def prefixEnd_29644 : Nat := 4983230072969 + 3 ^ 40 * 29644 * 2
def baseEnd_29644 : Nat := 3382582338219389203039

theorem tailTrace_29644 : CollatzResearch.WordTrace tailWord_29644 prefixEnd_29644 3382582338219389203039 := by
  unfold tailWord_29644
  simp only [CollatzResearch.WordTrace]
  refine ⟨540602752306162818619993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 720803669741550424826657 540602752306162818619993)
  ·
    refine ⟨405452064229622113964995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 540602752306162818619993 405452064229622113964995)
    ·
      refine ⟨608178096344433170947493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405452064229622113964995 608178096344433170947493)
      ·
        refine ⟨114033393064581219552655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 608178096344433170947493 114033393064581219552655)
        ·
          refine ⟨171050089596871829328983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114033393064581219552655 171050089596871829328983)
          ·
            refine ⟨256575134395307743993475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171050089596871829328983 256575134395307743993475)
            ·
              refine ⟨384862701592961615990213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256575134395307743993475 384862701592961615990213)
              ·
                refine ⟨72161756548680302998165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384862701592961615990213 72161756548680302998165)
                ·
                  refine ⟨3382582338219389203039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72161756548680302998165 3382582338219389203039)
                  ·
                    rfl

theorem cell22_29644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_29644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29644 prefixEnd_29644 := by exact prefixLift 29644
  have htrace : WordTrace (prefixWord ++ tailWord_29644) baseStart_29644 baseEnd_29644 := by
    simpa [prefixWord, tailWord_29644, baseEnd_29644] using wordTrace_append hprefix tailTrace_29644
  have hstable : (prefixWord ++ tailWord_29644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29644).length < 2 ^ (prefixWord ++ tailWord_29644).sum := by decide
  have hdescent : baseEnd_29644 < baseStart_29644 := by decide
  rcases family_descends (prefixWord ++ tailWord_29644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29646 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_29646 : Nat := 118140960795 + 29646 * 2 ^ 59
def prefixEnd_29646 : Nat := 4983230072969 + 3 ^ 40 * 29646 * 2
def baseEnd_29646 : Nat := 10148431655530829059111

theorem tailTrace_29646 : CollatzResearch.WordTrace tailWord_29646 prefixEnd_29646 10148431655530829059111 := by
  unfold tailWord_29646
  simp only [CollatzResearch.WordTrace]
  refine ⟨135159806325634997351599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 720852300403386652541861 135159806325634997351599)
  ·
    refine ⟨202739709488452496027399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135159806325634997351599 202739709488452496027399)
    ·
      refine ⟨304109564232678744041099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202739709488452496027399 304109564232678744041099)
      ·
        refine ⟨456164346349018116061649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304109564232678744041099 456164346349018116061649)
        ·
          refine ⟨342123259761763587046237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456164346349018116061649 342123259761763587046237)
          ·
            refine ⟨128296222410661345142339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342123259761763587046237 128296222410661345142339)
            ·
              refine ⟨192444333615992017713509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128296222410661345142339 192444333615992017713509)
              ·
                refine ⟨36083312552998503321283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192444333615992017713509 36083312552998503321283)
                ·
                  refine ⟨54124968829497754981925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36083312552998503321283 54124968829497754981925)
                  ·
                    refine ⟨10148431655530829059111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54124968829497754981925 10148431655530829059111)
                    ·
                      rfl

theorem cell22_29646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_29646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29646 prefixEnd_29646 := by exact prefixLift 29646
  have htrace : WordTrace (prefixWord ++ tailWord_29646) baseStart_29646 baseEnd_29646 := by
    simpa [prefixWord, tailWord_29646, baseEnd_29646] using wordTrace_append hprefix tailTrace_29646
  have hstable : (prefixWord ++ tailWord_29646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29646).length < 2 ^ (prefixWord ++ tailWord_29646).sum := by decide
  have hdescent : baseEnd_29646 < baseStart_29646 := by decide
  rcases family_descends (prefixWord ++ tailWord_29646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29678 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_29678 : Nat := 118140960795 + 29678 * 2 ^ 59
def prefixEnd_29678 : Nat := 4983230072969 + 3 ^ 40 * 29678 * 2
def baseEnd_29678 : Nat := 3386461969831137419671

theorem tailTrace_29678 : CollatzResearch.WordTrace tailWord_29678 prefixEnd_29678 3386461969831137419671 := by
  unfold tailWord_29678
  simp only [CollatzResearch.WordTrace]
  refine ⟨135305698311143680497211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 721630390992766295985125 135305698311143680497211)
  ·
    refine ⟨202958547466715520745817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135305698311143680497211 202958547466715520745817)
    ·
      refine ⟨152218910600036640559363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202958547466715520745817 152218910600036640559363)
      ·
        refine ⟨228328365900054960839045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152218910600036640559363 228328365900054960839045)
        ·
          refine ⟨42811568606260305157321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228328365900054960839045 42811568606260305157321)
          ·
            refine ⟨32108676454695228867991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42811568606260305157321 32108676454695228867991)
            ·
              refine ⟨48163014682042843301987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32108676454695228867991 48163014682042843301987)
              ·
                refine ⟨72244522023064264952981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48163014682042843301987 72244522023064264952981)
                ·
                  refine ⟨3386461969831137419671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72244522023064264952981 3386461969831137419671)
                  ·
                    rfl

theorem cell22_29678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_29678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29678 prefixEnd_29678 := by exact prefixLift 29678
  have htrace : WordTrace (prefixWord ++ tailWord_29678) baseStart_29678 baseEnd_29678 := by
    simpa [prefixWord, tailWord_29678, baseEnd_29678] using wordTrace_append hprefix tailTrace_29678
  have hstable : (prefixWord ++ tailWord_29678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29678).length < 2 ^ (prefixWord ++ tailWord_29678).sum := by decide
  have hdescent : baseEnd_29678 < baseStart_29678 := by decide
  rcases family_descends (prefixWord ++ tailWord_29678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29689 : List Nat := [1, 2, 1, 3, 1, 3, 4, 7]
def baseStart_29689 : Nat := 118140960795 + 29689 * 2 ^ 59
def prefixEnd_29689 : Nat := 4983230072969 + 3 ^ 40 * 29689 * 2
def baseEnd_29689 : Nat := 1129239048254783359331

theorem tailTrace_29689 : CollatzResearch.WordTrace tailWord_29689 prefixEnd_29689 1129239048254783359331 := by
  unfold tailWord_29689
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082846789449298322628121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 721897859632865548418747 1082846789449298322628121)
  ·
    refine ⟨812135092086973741971091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1082846789449298322628121 812135092086973741971091)
    ·
      refine ⟨1218202638130460612956637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812135092086973741971091 1218202638130460612956637)
      ·
        refine ⟨456825989298922729858739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1218202638130460612956637 456825989298922729858739)
        ·
          refine ⟨685238983948384094788109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456825989298922729858739 685238983948384094788109)
          ·
            refine ⟨256964618980644035545541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 685238983948384094788109 256964618980644035545541)
            ·
              refine ⟨48180866058870756664789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256964618980644035545541 48180866058870756664789)
              ·
                refine ⟨1129239048254783359331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48180866058870756664789 1129239048254783359331)
                ·
                  rfl

theorem cell22_29689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 7].length) (baseStart_29689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29689 prefixEnd_29689 := by exact prefixLift 29689
  have htrace : WordTrace (prefixWord ++ tailWord_29689) baseStart_29689 baseEnd_29689 := by
    simpa [prefixWord, tailWord_29689, baseEnd_29689] using wordTrace_append hprefix tailTrace_29689
  have hstable : (prefixWord ++ tailWord_29689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29689).length < 2 ^ (prefixWord ++ tailWord_29689).sum := by decide
  have hdescent : baseEnd_29689 < baseStart_29689 := by decide
  rcases family_descends (prefixWord ++ tailWord_29689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29714 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_29714 : Nat := 118140960795 + 29714 * 2 ^ 59
def prefixEnd_29714 : Nat := 4983230072969 + 3 ^ 40 * 29714 * 2
def baseEnd_29714 : Nat := 10171709445201318358903

theorem tailTrace_29714 : CollatzResearch.WordTrace tailWord_29714 prefixEnd_29714 10171709445201318358903 := by
  unfold tailWord_29714
  simp only [CollatzResearch.WordTrace]
  refine ⟨270939653589681898072049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 722505742905818394858797 270939653589681898072049)
  ·
    refine ⟨203204740192261423554037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270939653589681898072049 203204740192261423554037)
    ·
      refine ⟨19050444393024508458191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203204740192261423554037 19050444393024508458191)
      ·
        refine ⟨28575666589536762687287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19050444393024508458191 28575666589536762687287)
        ·
          refine ⟨42863499884305144030931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28575666589536762687287 42863499884305144030931)
          ·
            refine ⟨64295249826457716046397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42863499884305144030931 64295249826457716046397)
            ·
              refine ⟨24110718684921643517399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64295249826457716046397 24110718684921643517399)
              ·
                refine ⟨36166078027382465276099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24110718684921643517399 36166078027382465276099)
                ·
                  refine ⟨54249117041073697914149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36166078027382465276099 54249117041073697914149)
                  ·
                    refine ⟨10171709445201318358903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54249117041073697914149 10171709445201318358903)
                    ·
                      rfl

theorem cell22_29714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_29714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29714 prefixEnd_29714 := by exact prefixLift 29714
  have htrace : WordTrace (prefixWord ++ tailWord_29714) baseStart_29714 baseEnd_29714 := by
    simpa [prefixWord, tailWord_29714, baseEnd_29714] using wordTrace_append hprefix tailTrace_29714
  have hstable : (prefixWord ++ tailWord_29714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29714).length < 2 ^ (prefixWord ++ tailWord_29714).sum := by decide
  have hdescent : baseEnd_29714 < baseStart_29714 := by decide
  rcases family_descends (prefixWord ++ tailWord_29714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29828 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_29828 : Nat := 118140960795 + 29828 * 2 ^ 59
def prefixEnd_29828 : Nat := 4983230072969 + 3 ^ 40 * 29828 * 2
def baseEnd_29828 : Nat := 10210733974943021008553

theorem tailTrace_29828 : CollatzResearch.WordTrace tailWord_29828 prefixEnd_29828 10210733974943021008553 := by
  unfold tailWord_29828
  simp only [CollatzResearch.WordTrace]
  refine ⟨543958267972862530969069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 725277690630483374625425 543958267972862530969069)
  ·
    refine ⟨203984350489823449113401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 543958267972862530969069 203984350489823449113401)
    ·
      refine ⟨152988262867367586835051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203984350489823449113401 152988262867367586835051)
      ·
        refine ⟨229482394301051380252577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152988262867367586835051 229482394301051380252577)
        ·
          refine ⟨172111795725788535189433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229482394301051380252577 172111795725788535189433)
          ·
            refine ⟨129083846794341401392075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172111795725788535189433 129083846794341401392075)
            ·
              refine ⟨193625770191512102088113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129083846794341401392075 193625770191512102088113)
              ·
                refine ⟨145219327643634076566085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193625770191512102088113 145219327643634076566085)
                ·
                  refine ⟨27228623933181389356141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145219327643634076566085 27228623933181389356141)
                  ·
                    refine ⟨10210733974943021008553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27228623933181389356141 10210733974943021008553)
                    ·
                      rfl

theorem cell22_29828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_29828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29828 prefixEnd_29828 := by exact prefixLift 29828
  have htrace : WordTrace (prefixWord ++ tailWord_29828) baseStart_29828 baseEnd_29828 := by
    simpa [prefixWord, tailWord_29828, baseEnd_29828] using wordTrace_append hprefix tailTrace_29828
  have hstable : (prefixWord ++ tailWord_29828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29828).length < 2 ^ (prefixWord ++ tailWord_29828).sum := by decide
  have hdescent : baseEnd_29828 < baseStart_29828 := by decide
  rcases family_descends (prefixWord ++ tailWord_29828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29931 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 8]
def baseStart_29931 : Nat := 118140960795 + 29931 * 2 ^ 59
def prefixEnd_29931 : Nat := 4983230072969 + 3 ^ 40 * 29931 * 2
def baseEnd_29931 : Nat := 3415330993295028561079

theorem tailTrace_29931 : CollatzResearch.WordTrace tailWord_29931 prefixEnd_29931 3415330993295028561079 := by
  unfold tailWord_29931
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091673254572573652937647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 727782169715049101958431 1091673254572573652937647)
  ·
    refine ⟨1637509881858860479406471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1091673254572573652937647 1637509881858860479406471)
    ·
      refine ⟨2456264822788290719109707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637509881858860479406471 2456264822788290719109707)
      ·
        refine ⟨3684397234182436078664561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456264822788290719109707 3684397234182436078664561)
        ·
          refine ⟨2763297925636827058998421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3684397234182436078664561 2763297925636827058998421)
          ·
            refine ⟨129529590264226268390551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2763297925636827058998421 129529590264226268390551)
            ·
              refine ⟨194294385396339402585827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129529590264226268390551 194294385396339402585827)
              ·
                refine ⟨291441578094509103878741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194294385396339402585827 291441578094509103878741)
                ·
                  refine ⟨3415330993295028561079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 291441578094509103878741 3415330993295028561079)
                  ·
                    rfl

theorem cell22_29931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_29931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29931 prefixEnd_29931 := by exact prefixLift 29931
  have htrace : WordTrace (prefixWord ++ tailWord_29931) baseStart_29931 baseEnd_29931 := by
    simpa [prefixWord, tailWord_29931, baseEnd_29931] using wordTrace_append hprefix tailTrace_29931
  have hstable : (prefixWord ++ tailWord_29931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29931).length < 2 ^ (prefixWord ++ tailWord_29931).sum := by decide
  have hdescent : baseEnd_29931 < baseStart_29931 := by decide
  rcases family_descends (prefixWord ++ tailWord_29931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29954 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_29954 : Nat := 118140960795 + 29954 * 2 ^ 59
def prefixEnd_29954 : Nat := 4983230072969 + 3 ^ 40 * 29954 * 2
def baseEnd_29954 : Nat := 3417955449973564119389

theorem tailTrace_29954 : CollatzResearch.WordTrace tailWord_29954 prefixEnd_29954 3417955449973564119389 := by
  unfold tailWord_29954
  simp only [CollatzResearch.WordTrace]
  refine ⟨273128033372312145256229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 728341422326165720683277 273128033372312145256229)
  ·
    refine ⟨51211506257308527235543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273128033372312145256229 51211506257308527235543)
    ·
      refine ⟨76817259385962790853315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51211506257308527235543 76817259385962790853315)
      ·
        refine ⟨115225889078944186279973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76817259385962790853315 115225889078944186279973)
        ·
          refine ⟨21604854202302034927495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115225889078944186279973 21604854202302034927495)
          ·
            refine ⟨32407281303453052391243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604854202302034927495 32407281303453052391243)
            ·
              refine ⟨48610921955179578586865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32407281303453052391243 48610921955179578586865)
              ·
                refine ⟨36458191466384683940149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48610921955179578586865 36458191466384683940149)
                ·
                  refine ⟨3417955449973564119389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36458191466384683940149 3417955449973564119389)
                  ·
                    rfl

theorem cell22_29954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_29954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29954 prefixEnd_29954 := by exact prefixLift 29954
  have htrace : WordTrace (prefixWord ++ tailWord_29954) baseStart_29954 baseEnd_29954 := by
    simpa [prefixWord, tailWord_29954, baseEnd_29954] using wordTrace_append hprefix tailTrace_29954
  have hstable : (prefixWord ++ tailWord_29954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29954).length < 2 ^ (prefixWord ++ tailWord_29954).sum := by decide
  have hdescent : baseEnd_29954 < baseStart_29954 := by decide
  rcases family_descends (prefixWord ++ tailWord_29954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29978 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_29978 : Nat := 118140960795 + 29978 * 2 ^ 59
def prefixEnd_29978 : Nat := 4983230072969 + 3 ^ 40 * 29978 * 2
def baseEnd_29978 : Nat := 10262082040392629758093

theorem tailTrace_29978 : CollatzResearch.WordTrace tailWord_29978 prefixEnd_29978 10262082040392629758093 := by
  unfold tailWord_29978
  simp only [CollatzResearch.WordTrace]
  refine ⟨273346871350575169974647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 728924990268200453265725 273346871350575169974647)
  ·
    refine ⟨410020307025862754961971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273346871350575169974647 410020307025862754961971)
    ·
      refine ⟨615030460538794132442957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410020307025862754961971 615030460538794132442957)
      ·
        refine ⟨230636422702047799666109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615030460538794132442957 230636422702047799666109)
        ·
          refine ⟨86488658513267924874791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230636422702047799666109 86488658513267924874791)
          ·
            refine ⟨129732987769901887312187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86488658513267924874791 129732987769901887312187)
            ·
              refine ⟨194599481654852830968281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129732987769901887312187 194599481654852830968281)
              ·
                refine ⟨145949611241139623226211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194599481654852830968281 145949611241139623226211)
                ·
                  refine ⟨218924416861709434839317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145949611241139623226211 218924416861709434839317)
                  ·
                    refine ⟨10262082040392629758093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218924416861709434839317 10262082040392629758093)
                    ·
                      rfl

theorem cell22_29978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_29978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29978 prefixEnd_29978 := by exact prefixLift 29978
  have htrace : WordTrace (prefixWord ++ tailWord_29978) baseStart_29978 baseEnd_29978 := by
    simpa [prefixWord, tailWord_29978, baseEnd_29978] using wordTrace_append hprefix tailTrace_29978
  have hstable : (prefixWord ++ tailWord_29978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29978).length < 2 ^ (prefixWord ++ tailWord_29978).sum := by decide
  have hdescent : baseEnd_29978 < baseStart_29978 := by decide
  rcases family_descends (prefixWord ++ tailWord_29978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29980 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_29980 : Nat := 118140960795 + 29980 * 2 ^ 59
def prefixEnd_29980 : Nat := 4983230072969 + 3 ^ 40 * 29980 * 2
def baseEnd_29980 : Nat := 10262766681265291208087

theorem tailTrace_29980 : CollatzResearch.WordTrace tailWord_29980 prefixEnd_29980 10262766681265291208087 := by
  unfold tailWord_29980
  simp only [CollatzResearch.WordTrace]
  refine ⟨546730215697527510735697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 728973620930036680980929 546730215697527510735697)
  ·
    refine ⟨410047661773145633051773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 546730215697527510735697 410047661773145633051773)
    ·
      refine ⟨153767873164929612394415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410047661773145633051773 153767873164929612394415)
      ·
        refine ⟨230651809747394418591623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153767873164929612394415 230651809747394418591623)
        ·
          refine ⟨345977714621091627887435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230651809747394418591623 345977714621091627887435)
          ·
            refine ⟨518966571931637441831153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345977714621091627887435 518966571931637441831153)
            ·
              refine ⟨389224928948728081373365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518966571931637441831153 389224928948728081373365)
              ·
                refine ⟨36489837088943257628753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389224928948728081373365 36489837088943257628753)
                ·
                  refine ⟨27367377816707443221565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36489837088943257628753 27367377816707443221565)
                  ·
                    refine ⟨10262766681265291208087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27367377816707443221565 10262766681265291208087)
                    ·
                      rfl

theorem cell22_29980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_29980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29980 prefixEnd_29980 := by exact prefixLift 29980
  have htrace : WordTrace (prefixWord ++ tailWord_29980) baseStart_29980 baseEnd_29980 := by
    simpa [prefixWord, tailWord_29980, baseEnd_29980] using wordTrace_append hprefix tailTrace_29980
  have hstable : (prefixWord ++ tailWord_29980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29980).length < 2 ^ (prefixWord ++ tailWord_29980).sum := by decide
  have hdescent : baseEnd_29980 < baseStart_29980 := by decide
  rcases family_descends (prefixWord ++ tailWord_29980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29997 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_29997 : Nat := 118140960795 + 29997 * 2 ^ 59
def prefixEnd_29997 : Nat := 4983230072969 + 3 ^ 40 * 29997 * 2
def baseEnd_29997 : Nat := 10268586128682913533035

theorem tailTrace_29997 : CollatzResearch.WordTrace tailWord_29997 prefixEnd_29997 10268586128682913533035 := by
  unfold tailWord_29997
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094080472333466924840245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 729386981555644616560163 1094080472333466924840245)
  ·
    refine ⟨102570044281262524203773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1094080472333466924840245 102570044281262524203773)
    ·
      refine ⟨38463766605473446576415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102570044281262524203773 38463766605473446576415)
      ·
        refine ⟨57695649908210169864623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38463766605473446576415 57695649908210169864623)
        ·
          refine ⟨86543474862315254796935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57695649908210169864623 86543474862315254796935)
          ·
            refine ⟨129815212293472882195403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86543474862315254796935 129815212293472882195403)
            ·
              refine ⟨194722818440209323293105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129815212293472882195403 194722818440209323293105)
              ·
                refine ⟨146042113830156992469829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194722818440209323293105 146042113830156992469829)
                ·
                  refine ⟨27382896343154436088093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146042113830156992469829 27382896343154436088093)
                  ·
                    refine ⟨10268586128682913533035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27382896343154436088093 10268586128682913533035)
                    ·
                      rfl

theorem cell22_29997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_29997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_29997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_29997 prefixEnd_29997 := by exact prefixLift 29997
  have htrace : WordTrace (prefixWord ++ tailWord_29997) baseStart_29997 baseEnd_29997 := by
    simpa [prefixWord, tailWord_29997, baseEnd_29997] using wordTrace_append hprefix tailTrace_29997
  have hstable : (prefixWord ++ tailWord_29997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29997).length < 2 ^ (prefixWord ++ tailWord_29997).sum := by decide
  have hdescent : baseEnd_29997 < baseStart_29997 := by decide
  rcases family_descends (prefixWord ++ tailWord_29997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30025 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_30025 : Nat := 118140960795 + 30025 * 2 ^ 59
def prefixEnd_30025 : Nat := 4983230072969 + 3 ^ 40 * 30025 * 2
def baseEnd_30025 : Nat := 10278171100900173832949

theorem tailTrace_30025 : CollatzResearch.WordTrace tailWord_30025 prefixEnd_30025 10278171100900173832949 := by
  unfold tailWord_30025
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095101716232027706859529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 730067810821351804573019 1095101716232027706859529)
  ·
    refine ⟨821326287174020780144647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1095101716232027706859529 821326287174020780144647)
    ·
      refine ⟨1231989430761031170216971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821326287174020780144647 1231989430761031170216971)
      ·
        refine ⟨1847984146141546755325457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231989430761031170216971 1847984146141546755325457)
        ·
          refine ⟨1385988109606160066494093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847984146141546755325457 1385988109606160066494093)
          ·
            refine ⟨519745541102310024935285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1385988109606160066494093 519745541102310024935285)
            ·
              refine ⟨48726144478341564837683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 519745541102310024935285 48726144478341564837683)
              ·
                refine ⟨73089216717512347256525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48726144478341564837683 73089216717512347256525)
                ·
                  refine ⟨27408456269067130221197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73089216717512347256525 27408456269067130221197)
                  ·
                    refine ⟨10278171100900173832949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27408456269067130221197 10278171100900173832949)
                    ·
                      rfl

theorem cell22_30025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_30025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30025 prefixEnd_30025 := by exact prefixLift 30025
  have htrace : WordTrace (prefixWord ++ tailWord_30025) baseStart_30025 baseEnd_30025 := by
    simpa [prefixWord, tailWord_30025, baseEnd_30025] using wordTrace_append hprefix tailTrace_30025
  have hstable : (prefixWord ++ tailWord_30025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30025).length < 2 ^ (prefixWord ++ tailWord_30025).sum := by decide
  have hdescent : baseEnd_30025 < baseStart_30025 := by decide
  rcases family_descends (prefixWord ++ tailWord_30025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30100 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_30100 : Nat := 118140960795 + 30100 * 2 ^ 59
def prefixEnd_30100 : Nat := 4983230072969 + 3 ^ 40 * 30100 * 2
def baseEnd_30100 : Nat := 3434615044541659402573

theorem tailTrace_30100 : CollatzResearch.WordTrace tailWord_30100 prefixEnd_30100 3434615044541659402573 := by
  unfold tailWord_30100
  simp only [CollatzResearch.WordTrace]
  refine ⟨548918595480157757919877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 731891460640210343893169 548918595480157757919877)
  ·
    refine ⟨102922236652529579609977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 548918595480157757919877 102922236652529579609977)
    ·
      refine ⟨77191677489397184707483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102922236652529579609977 77191677489397184707483)
      ·
        refine ⟨115787516234095777061225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77191677489397184707483 115787516234095777061225)
        ·
          refine ⟨86840637175571832795919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115787516234095777061225 86840637175571832795919)
          ·
            refine ⟨130260955763357749193879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86840637175571832795919 130260955763357749193879)
            ·
              refine ⟨195391433645036623790819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130260955763357749193879 195391433645036623790819)
              ·
                refine ⟨293087150467554935686229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195391433645036623790819 293087150467554935686229)
                ·
                  refine ⟨3434615044541659402573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 293087150467554935686229 3434615044541659402573)
                  ·
                    rfl

theorem cell22_30100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_30100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30100 prefixEnd_30100 := by exact prefixLift 30100
  have htrace : WordTrace (prefixWord ++ tailWord_30100) baseStart_30100 baseEnd_30100 := by
    simpa [prefixWord, tailWord_30100, baseEnd_30100] using wordTrace_append hprefix tailTrace_30100
  have hstable : (prefixWord ++ tailWord_30100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30100).length < 2 ^ (prefixWord ++ tailWord_30100).sum := by decide
  have hdescent : baseEnd_30100 < baseStart_30100 := by decide
  rcases family_descends (prefixWord ++ tailWord_30100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30115 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 4, 3]
def baseStart_30115 : Nat := 118140960795 + 30115 * 2 ^ 59
def prefixEnd_30115 : Nat := 4983230072969 + 3 ^ 40 * 30115 * 2
def baseEnd_30115 : Nat := 10308979940169939082673

theorem tailTrace_30115 : CollatzResearch.WordTrace tailWord_30115 prefixEnd_30115 10308979940169939082673 := by
  unfold tailWord_30115
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098384285905973077635799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 732256190603982051757199 1098384285905973077635799)
  ·
    refine ⟨1647576428858959616453699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098384285905973077635799 1647576428858959616453699)
    ·
      refine ⟨2471364643288439424680549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647576428858959616453699 2471364643288439424680549)
      ·
        refine ⟨463380870616582392127603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2471364643288439424680549 463380870616582392127603)
        ·
          refine ⟨695071305924873588191405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463380870616582392127603 695071305924873588191405)
          ·
            refine ⟨260651739721827595571777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695071305924873588191405 260651739721827595571777)
            ·
              refine ⟨195488804791370696678833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260651739721827595571777 195488804791370696678833)
              ·
                refine ⟨146616603593528022509125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195488804791370696678833 146616603593528022509125)
                ·
                  refine ⟨27490613173786504220461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146616603593528022509125 27490613173786504220461)
                  ·
                    refine ⟨10308979940169939082673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27490613173786504220461 10308979940169939082673)
                    ·
                      rfl

theorem cell22_30115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 3].length) (baseStart_30115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30115 prefixEnd_30115 := by exact prefixLift 30115
  have htrace : WordTrace (prefixWord ++ tailWord_30115) baseStart_30115 baseEnd_30115 := by
    simpa [prefixWord, tailWord_30115, baseEnd_30115] using wordTrace_append hprefix tailTrace_30115
  have hstable : (prefixWord ++ tailWord_30115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30115).length < 2 ^ (prefixWord ++ tailWord_30115).sum := by decide
  have hdescent : baseEnd_30115 < baseStart_30115 := by decide
  rcases family_descends (prefixWord ++ tailWord_30115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30190 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_30190 : Nat := 118140960795 + 30190 * 2 ^ 59
def prefixEnd_30190 : Nat := 4983230072969 + 3 ^ 40 * 30190 * 2
def baseEnd_30190 : Nat := 3444884657631581152481

theorem tailTrace_30190 : CollatzResearch.WordTrace tailWord_30190 prefixEnd_30190 3444884657631581152481 := by
  unfold tailWord_30190
  simp only [CollatzResearch.WordTrace]
  refine ⟨137639970079282610827003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 734079840422840591077349 137639970079282610827003)
  ·
    refine ⟨206459955118923916240505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137639970079282610827003 206459955118923916240505)
    ·
      refine ⟨154844966339192937180379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206459955118923916240505 154844966339192937180379)
      ·
        refine ⟨232267449508789405770569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154844966339192937180379 232267449508789405770569)
        ·
          refine ⟨174200587131592054327927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232267449508789405770569 174200587131592054327927)
          ·
            refine ⟨261300880697388081491891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174200587131592054327927 261300880697388081491891)
            ·
              refine ⟨391951321046082122237837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261300880697388081491891 391951321046082122237837)
              ·
                refine ⟨146981745392280795839189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391951321046082122237837 146981745392280795839189)
                ·
                  refine ⟨3444884657631581152481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 146981745392280795839189 3444884657631581152481)
                  ·
                    rfl

theorem cell22_30190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_30190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30190 prefixEnd_30190 := by exact prefixLift 30190
  have htrace : WordTrace (prefixWord ++ tailWord_30190) baseStart_30190 baseEnd_30190 := by
    simpa [prefixWord, tailWord_30190, baseEnd_30190] using wordTrace_append hprefix tailTrace_30190
  have hstable : (prefixWord ++ tailWord_30190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30190).length < 2 ^ (prefixWord ++ tailWord_30190).sum := by decide
  have hdescent : baseEnd_30190 < baseStart_30190 := by decide
  rcases family_descends (prefixWord ++ tailWord_30190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30194 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_30194 : Nat := 118140960795 + 30194 * 2 ^ 59
def prefixEnd_30194 : Nat := 4983230072969 + 3 ^ 40 * 30194 * 2
def baseEnd_30194 : Nat := 10336023254640066357431

theorem tailTrace_30194 : CollatzResearch.WordTrace tailWord_30194 prefixEnd_30194 10336023254640066357431 := by
  unfold tailWord_30194
  simp only [CollatzResearch.WordTrace]
  refine ⟨275316413154942392440409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 734177101746513046507757 275316413154942392440409)
  ·
    refine ⟨206487309866206794330307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275316413154942392440409 206487309866206794330307)
    ·
      refine ⟨309730964799310191495461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206487309866206794330307 309730964799310191495461)
      ·
        refine ⟨58074555899870660905399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309730964799310191495461 58074555899870660905399)
        ·
          refine ⟨87111833849805991358099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58074555899870660905399 87111833849805991358099)
          ·
            refine ⟨130667750774708987037149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87111833849805991358099 130667750774708987037149)
            ·
              refine ⟨49000406540515870138931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130667750774708987037149 49000406540515870138931)
              ·
                refine ⟨73500609810773805208397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49000406540515870138931 73500609810773805208397)
                ·
                  refine ⟨27562728679040176953149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73500609810773805208397 27562728679040176953149)
                  ·
                    refine ⟨10336023254640066357431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27562728679040176953149 10336023254640066357431)
                    ·
                      rfl

theorem cell22_30194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_30194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30194 prefixEnd_30194 := by exact prefixLift 30194
  have htrace : WordTrace (prefixWord ++ tailWord_30194) baseStart_30194 baseEnd_30194 := by
    simpa [prefixWord, tailWord_30194, baseEnd_30194] using wordTrace_append hprefix tailTrace_30194
  have hstable : (prefixWord ++ tailWord_30194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30194).length < 2 ^ (prefixWord ++ tailWord_30194).sum := by decide
  have hdescent : baseEnd_30194 < baseStart_30194 := by decide
  rcases family_descends (prefixWord ++ tailWord_30194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30318 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_30318 : Nat := 118140960795 + 30318 * 2 ^ 59
def prefixEnd_30318 : Nat := 4983230072969 + 3 ^ 40 * 30318 * 2
def baseEnd_30318 : Nat := 10378470988745076257051

theorem tailTrace_30318 : CollatzResearch.WordTrace tailWord_30318 prefixEnd_30318 10378470988745076257051 := by
  unfold tailWord_30318
  simp only [CollatzResearch.WordTrace]
  refine ⟨138223538021317343409451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 737192202780359164850405 138223538021317343409451)
  ·
    refine ⟨207335307031976015114177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138223538021317343409451 207335307031976015114177)
    ·
      refine ⟨155501480273982011335633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207335307031976015114177 155501480273982011335633)
      ·
        refine ⟨116626110205486508501725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155501480273982011335633 116626110205486508501725)
        ·
          refine ⟨43734791327057440688147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116626110205486508501725 43734791327057440688147)
          ·
            refine ⟨65602186990586161032221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43734791327057440688147 65602186990586161032221)
            ·
              refine ⟨24600820121469810387083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65602186990586161032221 24600820121469810387083)
              ·
                refine ⟨36901230182204715580625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24600820121469810387083 36901230182204715580625)
                ·
                  refine ⟨27675922636653536685469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36901230182204715580625 27675922636653536685469)
                  ·
                    refine ⟨10378470988745076257051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27675922636653536685469 10378470988745076257051)
                    ·
                      rfl

theorem cell22_30318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_30318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30318 prefixEnd_30318 := by exact prefixLift 30318
  have htrace : WordTrace (prefixWord ++ tailWord_30318) baseStart_30318 baseEnd_30318 := by
    simpa [prefixWord, tailWord_30318, baseEnd_30318] using wordTrace_append hprefix tailTrace_30318
  have hstable : (prefixWord ++ tailWord_30318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30318).length < 2 ^ (prefixWord ++ tailWord_30318).sum := by decide
  have hdescent : baseEnd_30318 < baseStart_30318 := by decide
  rcases family_descends (prefixWord ++ tailWord_30318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30432 : List Nat := [2, 1, 1, 3, 1, 2, 5, 7]
def baseStart_30432 : Nat := 118140960795 + 30432 * 2 ^ 59
def prefixEnd_30432 : Nat := 4983230072969 + 3 ^ 40 * 30432 * 2
def baseEnd_30432 : Nat := 1157499502054086545189

theorem tailTrace_30432 : CollatzResearch.WordTrace tailWord_30432 prefixEnd_30432 1157499502054086545189 := by
  unfold tailWord_30432
  simp only [CollatzResearch.WordTrace]
  refine ⟨554973112878768108462775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 739964150505024144617033 554973112878768108462775)
  ·
    refine ⟨832459669318152162694163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554973112878768108462775 832459669318152162694163)
    ·
      refine ⟨1248689503977228244041245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832459669318152162694163 1248689503977228244041245)
      ·
        refine ⟨468258563991460591515467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1248689503977228244041245 468258563991460591515467)
        ·
          refine ⟨702387845987190887273201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468258563991460591515467 702387845987190887273201)
          ·
            refine ⟨526790884490393165454901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702387845987190887273201 526790884490393165454901)
            ·
              refine ⟨49386645420974359261397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 526790884490393165454901 49386645420974359261397)
              ·
                refine ⟨1157499502054086545189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49386645420974359261397 1157499502054086545189)
                ·
                  rfl

theorem cell22_30432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_30432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30432 prefixEnd_30432 := by exact prefixLift 30432
  have htrace : WordTrace (prefixWord ++ tailWord_30432) baseStart_30432 baseEnd_30432 := by
    simpa [prefixWord, tailWord_30432, baseEnd_30432] using wordTrace_append hprefix tailTrace_30432
  have hstable : (prefixWord ++ tailWord_30432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30432).length < 2 ^ (prefixWord ++ tailWord_30432).sum := by decide
  have hdescent : baseEnd_30432 < baseStart_30432 := by decide
  rcases family_descends (prefixWord ++ tailWord_30432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30449 : List Nat := [1, 2, 2, 2, 2, 4, 3, 6]
def baseStart_30449 : Nat := 118140960795 + 30449 * 2 ^ 59
def prefixEnd_30449 : Nat := 4983230072969 + 3 ^ 40 * 30449 * 2
def baseEnd_30449 : Nat := 1158146107322711247961

theorem tailTrace_30449 : CollatzResearch.WordTrace tailWord_30449 prefixEnd_30449 1158146107322711247961 := by
  unfold tailWord_30449
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110566266695948120294401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 740377511130632080196267 1110566266695948120294401)
  ·
    refine ⟨832924700021961090220801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1110566266695948120294401 832924700021961090220801)
    ·
      refine ⟨624693525016470817665601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 832924700021961090220801 624693525016470817665601)
      ·
        refine ⟨468520143762353113249201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624693525016470817665601 468520143762353113249201)
        ·
          refine ⟨351390107821764834936901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468520143762353113249201 351390107821764834936901)
          ·
            refine ⟨65885645216580906550669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351390107821764834936901 65885645216580906550669)
            ·
              refine ⟨24707116956217839956501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65885645216580906550669 24707116956217839956501)
              ·
                refine ⟨1158146107322711247961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24707116956217839956501 1158146107322711247961)
                ·
                  rfl

theorem cell22_30449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 6].length) (baseStart_30449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30449 prefixEnd_30449 := by exact prefixLift 30449
  have htrace : WordTrace (prefixWord ++ tailWord_30449) baseStart_30449 baseEnd_30449 := by
    simpa [prefixWord, tailWord_30449, baseEnd_30449] using wordTrace_append hprefix tailTrace_30449
  have hstable : (prefixWord ++ tailWord_30449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30449).length < 2 ^ (prefixWord ++ tailWord_30449).sum := by decide
  have hdescent : baseEnd_30449 < baseStart_30449 := by decide
  rcases family_descends (prefixWord ++ tailWord_30449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30515 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 1, 3]
def baseStart_30515 : Nat := 118140960795 + 30515 * 2 ^ 59
def prefixEnd_30515 : Nat := 4983230072969 + 3 ^ 40 * 30515 * 2
def baseEnd_30515 : Nat := 10445908114702229081447

theorem tailTrace_30515 : CollatzResearch.WordTrace tailWord_30515 prefixEnd_30515 10445908114702229081447 := by
  unfold tailWord_30515
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112973484456841392196999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 741982322971227594797999 1112973484456841392196999)
  ·
    refine ⟨1669460226685262088295499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112973484456841392196999 1669460226685262088295499)
    ·
      refine ⟨2504190340027893132443249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669460226685262088295499 2504190340027893132443249)
      ·
        refine ⟨1878142755020919849332437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2504190340027893132443249 1878142755020919849332437)
        ·
          refine ⟨44018970820802808968729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1878142755020919849332437 44018970820802808968729)
          ·
            refine ⟨33014228115602106726547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44018970820802808968729 33014228115602106726547)
            ·
              refine ⟨49521342173403160089821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33014228115602106726547 49521342173403160089821)
              ·
                refine ⟨18570503315026185033683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49521342173403160089821 18570503315026185033683)
                ·
                  refine ⟨27855754972539277550525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18570503315026185033683 27855754972539277550525)
                  ·
                    refine ⟨10445908114702229081447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27855754972539277550525 10445908114702229081447)
                    ·
                      rfl

theorem cell22_30515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 3].length) (baseStart_30515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30515 prefixEnd_30515 := by exact prefixLift 30515
  have htrace : WordTrace (prefixWord ++ tailWord_30515) baseStart_30515 baseEnd_30515 := by
    simpa [prefixWord, tailWord_30515, baseEnd_30515] using wordTrace_append hprefix tailTrace_30515
  have hstable : (prefixWord ++ tailWord_30515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30515).length < 2 ^ (prefixWord ++ tailWord_30515).sum := by decide
  have hdescent : baseEnd_30515 < baseStart_30515 := by decide
  rcases family_descends (prefixWord ++ tailWord_30515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30554 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_30554 : Nat := 118140960795 + 30554 * 2 ^ 59
def prefixEnd_30554 : Nat := 4983230072969 + 3 ^ 40 * 30554 * 2
def baseEnd_30554 : Nat := 10459258611719127356327

theorem tailTrace_30554 : CollatzResearch.WordTrace tailWord_30554 prefixEnd_30554 10459258611719127356327 := by
  unfold tailWord_30554
  simp only [CollatzResearch.WordTrace]
  refine ⟨278598982828887763216679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 742930620877034035244477 278598982828887763216679)
  ·
    refine ⟨417898474243331644825019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278598982828887763216679 417898474243331644825019)
    ·
      refine ⟨626847711364997467237529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417898474243331644825019 626847711364997467237529)
      ·
        refine ⟨470135783523748100428147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626847711364997467237529 470135783523748100428147)
        ·
          refine ⟨705203675285622150642221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470135783523748100428147 705203675285622150642221)
          ·
            refine ⟨264451378232108306490833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705203675285622150642221 264451378232108306490833)
            ·
              refine ⟨198338533674081229868125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264451378232108306490833 198338533674081229868125)
              ·
                refine ⟨74376950127780461200547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198338533674081229868125 74376950127780461200547)
                ·
                  refine ⟨111565425191670691800821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74376950127780461200547 111565425191670691800821)
                  ·
                    refine ⟨10459258611719127356327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111565425191670691800821 10459258611719127356327)
                    ·
                      rfl

theorem cell22_30554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_30554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30554 prefixEnd_30554 := by exact prefixLift 30554
  have htrace : WordTrace (prefixWord ++ tailWord_30554) baseStart_30554 baseEnd_30554 := by
    simpa [prefixWord, tailWord_30554, baseEnd_30554] using wordTrace_append hprefix tailTrace_30554
  have hstable : (prefixWord ++ tailWord_30554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30554).length < 2 ^ (prefixWord ++ tailWord_30554).sum := by decide
  have hdescent : baseEnd_30554 < baseStart_30554 := by decide
  rcases family_descends (prefixWord ++ tailWord_30554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30590 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_30590 : Nat := 118140960795 + 30590 * 2 ^ 59
def prefixEnd_30590 : Nat := 4983230072969 + 3 ^ 40 * 30590 * 2
def baseEnd_30590 : Nat := 3490527382475677818739

theorem tailTrace_30590 : CollatzResearch.WordTrace tailWord_30590 prefixEnd_30590 3490527382475677818739 := by
  unfold tailWord_30590
  simp only [CollatzResearch.WordTrace]
  refine ⟨139463619898141150147153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 743805972790086134118149 139463619898141150147153)
  ·
    refine ⟨104597714923605862610365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139463619898141150147153 104597714923605862610365)
    ·
      refine ⟨39224143096352198478887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104597714923605862610365 39224143096352198478887)
      ·
        refine ⟨58836214644528297718331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39224143096352198478887 58836214644528297718331)
        ·
          refine ⟨88254321966792446577497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58836214644528297718331 88254321966792446577497)
          ·
            refine ⟨66190741475094334933123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88254321966792446577497 66190741475094334933123)
            ·
              refine ⟨99286112212641502399685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66190741475094334933123 99286112212641502399685)
              ·
                refine ⟨18616146039870281699941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99286112212641502399685 18616146039870281699941)
                ·
                  refine ⟨3490527382475677818739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18616146039870281699941 3490527382475677818739)
                  ·
                    rfl

theorem cell22_30590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_30590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30590 prefixEnd_30590 := by exact prefixLift 30590
  have htrace : WordTrace (prefixWord ++ tailWord_30590) baseStart_30590 baseEnd_30590 := by
    simpa [prefixWord, tailWord_30590, baseEnd_30590] using wordTrace_append hprefix tailTrace_30590
  have hstable : (prefixWord ++ tailWord_30590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30590).length < 2 ^ (prefixWord ++ tailWord_30590).sum := by decide
  have hdescent : baseEnd_30590 < baseStart_30590 := by decide
  rcases family_descends (prefixWord ++ tailWord_30590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30721 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_30721 : Nat := 118140960795 + 30721 * 2 ^ 59
def prefixEnd_30721 : Nat := 4983230072969 + 3 ^ 40 * 30721 * 2
def baseEnd_30721 : Nat := 10516426124586358430815

theorem tailTrace_30721 : CollatzResearch.WordTrace tailWord_30721 prefixEnd_30721 10516426124586358430815 := by
  unfold tailWord_30721
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120486921710538574196017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 746991281140359049464011 1120486921710538574196017)
  ·
    refine ⟨840365191282903930647013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1120486921710538574196017 840365191282903930647013)
    ·
      refine ⟨157568473365544486996315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 840365191282903930647013 157568473365544486996315)
      ·
        refine ⟨236352710048316730494473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157568473365544486996315 236352710048316730494473)
        ·
          refine ⟨177264532536237547870855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236352710048316730494473 177264532536237547870855)
          ·
            refine ⟨265896798804356321806283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177264532536237547870855 265896798804356321806283)
            ·
              refine ⟨398845198206534482709425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265896798804356321806283 398845198206534482709425)
              ·
                refine ⟨299133898654900862032069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398845198206534482709425 299133898654900862032069)
                ·
                  refine ⟨56087605997793911631013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299133898654900862032069 56087605997793911631013)
                  ·
                    refine ⟨10516426124586358430815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56087605997793911631013 10516426124586358430815)
                    ·
                      rfl

theorem cell22_30721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_30721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30721 prefixEnd_30721 := by exact prefixLift 30721
  have htrace : WordTrace (prefixWord ++ tailWord_30721) baseStart_30721 baseEnd_30721 := by
    simpa [prefixWord, tailWord_30721, baseEnd_30721] using wordTrace_append hprefix tailTrace_30721
  have hstable : (prefixWord ++ tailWord_30721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30721).length < 2 ^ (prefixWord ++ tailWord_30721).sum := by decide
  have hdescent : baseEnd_30721 < baseStart_30721 := by decide
  rcases family_descends (prefixWord ++ tailWord_30721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30759 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 4]
def baseStart_30759 : Nat := 118140960795 + 30759 * 2 ^ 59
def prefixEnd_30759 : Nat := 4983230072969 + 3 ^ 40 * 30759 * 2
def baseEnd_30759 : Nat := 3509811433722308660233

theorem tailTrace_30759 : CollatzResearch.WordTrace tailWord_30759 prefixEnd_30759 3509811433722308660233 := by
  unfold tailWord_30759
  simp only [CollatzResearch.WordTrace]
  refine ⟨1121872895572871064079331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 747915263715247376052887 1121872895572871064079331)
  ·
    refine ⟨1682809343359306596118997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1121872895572871064079331 1682809343359306596118997)
    ·
      refine ⟨39440843984983748346539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1682809343359306596118997 39440843984983748346539)
      ·
        refine ⟨59161265977475622519809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39440843984983748346539 59161265977475622519809)
        ·
          refine ⟨44370949483106716889857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59161265977475622519809 44370949483106716889857)
          ·
            refine ⟨33278212112330037667393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44370949483106716889857 33278212112330037667393)
            ·
              refine ⟨24958659084247528250545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33278212112330037667393 24958659084247528250545)
              ·
                refine ⟨18718994313185646187909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24958659084247528250545 18718994313185646187909)
                ·
                  refine ⟨3509811433722308660233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18718994313185646187909 3509811433722308660233)
                  ·
                    rfl

theorem cell22_30759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 4].length) (baseStart_30759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30759 prefixEnd_30759 := by exact prefixLift 30759
  have htrace : WordTrace (prefixWord ++ tailWord_30759) baseStart_30759 baseEnd_30759 := by
    simpa [prefixWord, tailWord_30759, baseEnd_30759] using wordTrace_append hprefix tailTrace_30759
  have hstable : (prefixWord ++ tailWord_30759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30759).length < 2 ^ (prefixWord ++ tailWord_30759).sum := by decide
  have hdescent : baseEnd_30759 < baseStart_30759 := by decide
  rcases family_descends (prefixWord ++ tailWord_30759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30785 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_30785 : Nat := 118140960795 + 30785 * 2 ^ 59
def prefixEnd_30785 : Nat := 4983230072969 + 3 ^ 40 * 30785 * 2
def baseEnd_30785 : Nat := 10538334632511524830619

theorem tailTrace_30785 : CollatzResearch.WordTrace tailWord_30785 prefixEnd_30785 10538334632511524830619 := by
  unfold tailWord_30785
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122821193478677504525809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 748547462319118336350539 1122821193478677504525809)
  ·
    refine ⟨842115895109008128394357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1122821193478677504525809 842115895109008128394357)
    ·
      refine ⟨78948365166469512036971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 842115895109008128394357 78948365166469512036971)
      ·
        refine ⟨118422547749704268055457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78948365166469512036971 118422547749704268055457)
        ·
          refine ⟨88816910812278201041593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118422547749704268055457 88816910812278201041593)
          ·
            refine ⟨66612683109208650781195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88816910812278201041593 66612683109208650781195)
            ·
              refine ⟨99919024663812976171793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66612683109208650781195 99919024663812976171793)
              ·
                refine ⟨74939268497859732128845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99919024663812976171793 74939268497859732128845)
                ·
                  refine ⟨28102225686697399548317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74939268497859732128845 28102225686697399548317)
                  ·
                    refine ⟨10538334632511524830619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28102225686697399548317 10538334632511524830619)
                    ·
                      rfl

theorem cell22_30785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_30785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30785 prefixEnd_30785 := by exact prefixLift 30785
  have htrace : WordTrace (prefixWord ++ tailWord_30785) baseStart_30785 baseEnd_30785 := by
    simpa [prefixWord, tailWord_30785, baseEnd_30785] using wordTrace_append hprefix tailTrace_30785
  have hstable : (prefixWord ++ tailWord_30785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30785).length < 2 ^ (prefixWord ++ tailWord_30785).sum := by decide
  have hdescent : baseEnd_30785 < baseStart_30785 := by decide
  rcases family_descends (prefixWord ++ tailWord_30785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30845 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_30845 : Nat := 118140960795 + 30845 * 2 ^ 59
def prefixEnd_30845 : Nat := 4983230072969 + 3 ^ 40 * 30845 * 2
def baseEnd_30845 : Nat := 10558873858691368330435

theorem tailTrace_30845 : CollatzResearch.WordTrace tailWord_30845 prefixEnd_30845 10558873858691368330435 := by
  unfold tailWord_30845
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125009573261307751709989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 750006382174205167806659 1125009573261307751709989)
  ·
    refine ⟨210939294986495203445623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1125009573261307751709989 210939294986495203445623)
    ·
      refine ⟨316408942479742805168435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210939294986495203445623 316408942479742805168435)
      ·
        refine ⟨474613413719614207752653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316408942479742805168435 474613413719614207752653)
        ·
          refine ⟨177980030144855327907245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474613413719614207752653 177980030144855327907245)
          ·
            refine ⟨66742511304320747965217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177980030144855327907245 66742511304320747965217)
            ·
              refine ⟨50056883478240560973913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66742511304320747965217 50056883478240560973913)
              ·
                refine ⟨37542662608680420730435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50056883478240560973913 37542662608680420730435)
                ·
                  refine ⟨56313993913020631095653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37542662608680420730435 56313993913020631095653)
                  ·
                    refine ⟨10558873858691368330435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56313993913020631095653 10558873858691368330435)
                    ·
                      rfl

theorem cell22_30845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_30845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30845 prefixEnd_30845 := by exact prefixLift 30845
  have htrace : WordTrace (prefixWord ++ tailWord_30845) baseStart_30845 baseEnd_30845 := by
    simpa [prefixWord, tailWord_30845, baseEnd_30845] using wordTrace_append hprefix tailTrace_30845
  have hstable : (prefixWord ++ tailWord_30845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30845).length < 2 ^ (prefixWord ++ tailWord_30845).sum := by decide
  have hdescent : baseEnd_30845 < baseStart_30845 := by decide
  rcases family_descends (prefixWord ++ tailWord_30845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30870 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_30870 : Nat := 118140960795 + 30870 * 2 ^ 59
def prefixEnd_30870 : Nat := 4983230072969 + 3 ^ 40 * 30870 * 2
def baseEnd_30870 : Nat := 10567431869599636455359

theorem tailTrace_30870 : CollatzResearch.WordTrace tailWord_30870 prefixEnd_30870 10567431869599636455359 := by
  unfold tailWord_30870
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370087385671063835629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 750614265447158014246709 70370087385671063835629)
  ·
    refine ⟨26388782769626648938361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70370087385671063835629 26388782769626648938361)
    ·
      refine ⟨19791587077219986703771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26388782769626648938361 19791587077219986703771)
      ·
        refine ⟨29687380615829980055657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19791587077219986703771 29687380615829980055657)
        ·
          refine ⟨22265535461872485041743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29687380615829980055657 22265535461872485041743)
          ·
            refine ⟨33398303192808727562615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22265535461872485041743 33398303192808727562615)
            ·
              refine ⟨50097454789213091343923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33398303192808727562615 50097454789213091343923)
              ·
                refine ⟨75146182183819637015885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50097454789213091343923 75146182183819637015885)
                ·
                  refine ⟨28179818318932363880957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75146182183819637015885 28179818318932363880957)
                  ·
                    refine ⟨10567431869599636455359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28179818318932363880957 10567431869599636455359)
                    ·
                      rfl

theorem cell22_30870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_30870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30870 prefixEnd_30870 := by exact prefixLift 30870
  have htrace : WordTrace (prefixWord ++ tailWord_30870) baseStart_30870 baseEnd_30870 := by
    simpa [prefixWord, tailWord_30870, baseEnd_30870] using wordTrace_append hprefix tailTrace_30870
  have hstable : (prefixWord ++ tailWord_30870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30870).length < 2 ^ (prefixWord ++ tailWord_30870).sum := by decide
  have hdescent : baseEnd_30870 < baseStart_30870 := by decide
  rcases family_descends (prefixWord ++ tailWord_30870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30877 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 4]
def baseStart_30877 : Nat := 118140960795 + 30877 * 2 ^ 59
def prefixEnd_30877 : Nat := 4983230072969 + 3 ^ 40 * 30877 * 2
def baseEnd_30877 : Nat := 3523276037551317176779

theorem tailTrace_30877 : CollatzResearch.WordTrace tailWord_30877 prefixEnd_30877 3523276037551317176779 := by
  unfold tailWord_30877
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126176709145377216874885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 750784472763584811249923 1126176709145377216874885)
  ·
    refine ⟨211158132964758228164041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1126176709145377216874885 211158132964758228164041)
    ·
      refine ⟨158368599723568671123031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211158132964758228164041 158368599723568671123031)
      ·
        refine ⟨237552899585353006684547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158368599723568671123031 237552899585353006684547)
        ·
          refine ⟨356329349378029510026821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237552899585353006684547 356329349378029510026821)
          ·
            refine ⟨66811753008380533130029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356329349378029510026821 66811753008380533130029)
            ·
              refine ⟨25054407378142699923761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66811753008380533130029 25054407378142699923761)
              ·
                refine ⟨18790805533607024942821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25054407378142699923761 18790805533607024942821)
                ·
                  refine ⟨3523276037551317176779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18790805533607024942821 3523276037551317176779)
                  ·
                    rfl

theorem cell22_30877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_30877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30877 prefixEnd_30877 := by exact prefixLift 30877
  have htrace : WordTrace (prefixWord ++ tailWord_30877) baseStart_30877 baseEnd_30877 := by
    simpa [prefixWord, tailWord_30877, baseEnd_30877] using wordTrace_append hprefix tailTrace_30877
  have hstable : (prefixWord ++ tailWord_30877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30877).length < 2 ^ (prefixWord ++ tailWord_30877).sum := by decide
  have hdescent : baseEnd_30877 < baseStart_30877 := by decide
  rcases family_descends (prefixWord ++ tailWord_30877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30963 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 3, 4]
def baseStart_30963 : Nat := 118140960795 + 30963 * 2 ^ 59
def prefixEnd_30963 : Nat := 4983230072969 + 3 ^ 40 * 30963 * 2
def baseEnd_30963 : Nat := 10599267670178393880073

theorem tailTrace_30963 : CollatzResearch.WordTrace tailWord_30963 prefixEnd_30963 10599267670178393880073 := by
  unfold tailWord_30963
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129313386833813904505543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 752875591222542603003695 1129313386833813904505543)
  ·
    refine ⟨1693970080250720856758315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129313386833813904505543 1693970080250720856758315)
    ·
      refine ⟨2540955120376081285137473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693970080250720856758315 2540955120376081285137473)
      ·
        refine ⟨1905716340282060963853105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540955120376081285137473 1905716340282060963853105)
        ·
          refine ⟨1429287255211545722889829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905716340282060963853105 1429287255211545722889829)
          ·
            refine ⟨267991360352164823041843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1429287255211545722889829 267991360352164823041843)
            ·
              refine ⟨401987040528247234562765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267991360352164823041843 401987040528247234562765)
              ·
                refine ⟨150745140198092712961037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401987040528247234562765 150745140198092712961037)
                ·
                  refine ⟨56529427574284767360389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150745140198092712961037 56529427574284767360389)
                  ·
                    refine ⟨10599267670178393880073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56529427574284767360389 10599267670178393880073)
                    ·
                      rfl

theorem cell22_30963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_30963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_30963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_30963 prefixEnd_30963 := by exact prefixLift 30963
  have htrace : WordTrace (prefixWord ++ tailWord_30963) baseStart_30963 baseEnd_30963 := by
    simpa [prefixWord, tailWord_30963, baseEnd_30963] using wordTrace_append hprefix tailTrace_30963
  have hstable : (prefixWord ++ tailWord_30963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30963).length < 2 ^ (prefixWord ++ tailWord_30963).sum := by decide
  have hdescent : baseEnd_30963 < baseStart_30963 := by decide
  rcases family_descends (prefixWord ++ tailWord_30963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31055 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 3, 3]
def baseStart_31055 : Nat := 118140960795 + 31055 * 2 ^ 59
def prefixEnd_31055 : Nat := 4983230072969 + 3 ^ 40 * 31055 * 2
def baseEnd_31055 : Nat := 10630761150320820579791

theorem tailTrace_31055 : CollatzResearch.WordTrace tailWord_31055 prefixEnd_31055 10630761150320820579791 := by
  unfold tailWord_31055
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132668902500513616854619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 755112601667009077903079 1132668902500513616854619)
  ·
    refine ⟨1699003353750770425281929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132668902500513616854619 1699003353750770425281929)
    ·
      refine ⟨1274252515313077818961447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1699003353750770425281929 1274252515313077818961447)
      ·
        refine ⟨1911378772969616728442171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274252515313077818961447 1911378772969616728442171)
        ·
          refine ⟨2867068159454425092663257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911378772969616728442171 2867068159454425092663257)
          ·
            refine ⟨2150301119590818819497443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867068159454425092663257 2150301119590818819497443)
            ·
              refine ⟨3225451679386228229246165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150301119590818819497443 3225451679386228229246165)
              ·
                refine ⟨75596523735614724122957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3225451679386228229246165 75596523735614724122957)
                ·
                  refine ⟨28348696400855521546109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75596523735614724122957 28348696400855521546109)
                  ·
                    refine ⟨10630761150320820579791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28348696400855521546109 10630761150320820579791)
                    ·
                      rfl

theorem cell22_31055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_31055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31055 prefixEnd_31055 := by exact prefixLift 31055
  have htrace : WordTrace (prefixWord ++ tailWord_31055) baseStart_31055 baseEnd_31055 := by
    simpa [prefixWord, tailWord_31055, baseEnd_31055] using wordTrace_append hprefix tailTrace_31055
  have hstable : (prefixWord ++ tailWord_31055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31055).length < 2 ^ (prefixWord ++ tailWord_31055).sum := by decide
  have hdescent : baseEnd_31055 < baseStart_31055 := by decide
  rcases family_descends (prefixWord ++ tailWord_31055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31061 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_31061 : Nat := 118140960795 + 31061 * 2 ^ 59
def prefixEnd_31061 : Nat := 4983230072969 + 3 ^ 40 * 31061 * 2
def baseEnd_31061 : Nat := 10632815072938804929773

theorem tailTrace_31061 : CollatzResearch.WordTrace tailWord_31061 prefixEnd_31061 10632815072938804929773 := by
  unfold tailWord_31061
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132887740478776641573037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 755258493652517761048691 1132887740478776641573037)
  ·
    refine ⟨424832902679541240589889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1132887740478776641573037 424832902679541240589889)
    ·
      refine ⟨318624677009655930442417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424832902679541240589889 318624677009655930442417)
      ·
        refine ⟨238968507757241947831813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318624677009655930442417 238968507757241947831813)
        ·
          refine ⟨44806595204482865218465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238968507757241947831813 44806595204482865218465)
          ·
            refine ⟨33604946403362148913849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44806595204482865218465 33604946403362148913849)
            ·
              refine ⟨25203709802521611685387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33604946403362148913849 25203709802521611685387)
              ·
                refine ⟨37805564703782417528081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25203709802521611685387 37805564703782417528081)
                ·
                  refine ⟨28354173527836813146061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37805564703782417528081 28354173527836813146061)
                  ·
                    refine ⟨10632815072938804929773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28354173527836813146061 10632815072938804929773)
                    ·
                      rfl

theorem cell22_31061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_31061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31061 prefixEnd_31061 := by exact prefixLift 31061
  have htrace : WordTrace (prefixWord ++ tailWord_31061) baseStart_31061 baseEnd_31061 := by
    simpa [prefixWord, tailWord_31061, baseEnd_31061] using wordTrace_append hprefix tailTrace_31061
  have hstable : (prefixWord ++ tailWord_31061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31061).length < 2 ^ (prefixWord ++ tailWord_31061).sum := by decide
  have hdescent : baseEnd_31061 < baseStart_31061 := by decide
  rcases family_descends (prefixWord ++ tailWord_31061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31083 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_31083 : Nat := 118140960795 + 31083 * 2 ^ 59
def prefixEnd_31083 : Nat := 4983230072969 + 3 ^ 40 * 31083 * 2
def baseEnd_31083 : Nat := 10640346122538080879705

theorem tailTrace_31083 : CollatzResearch.WordTrace tailWord_31083 prefixEnd_31083 10640346122538080879705 := by
  unfold tailWord_31083
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133690146399074398873903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 755793430932716265915935 1133690146399074398873903)
  ·
    refine ⟨1700535219598611598310855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133690146399074398873903 1700535219598611598310855)
    ·
      refine ⟨2550802829397917397466283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700535219598611598310855 2550802829397917397466283)
      ·
        refine ⟨3826204244096876096199425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550802829397917397466283 3826204244096876096199425)
        ·
          refine ⟨2869653183072657072149569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3826204244096876096199425 2869653183072657072149569)
          ·
            refine ⟨2152239887304492804112177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869653183072657072149569 2152239887304492804112177)
            ·
              refine ⟨1614179915478369603084133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152239887304492804112177 1614179915478369603084133)
              ·
                refine ⟨302658734152194300578275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1614179915478369603084133 302658734152194300578275)
                ·
                  refine ⟨453988101228291450867413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302658734152194300578275 453988101228291450867413)
                  ·
                    refine ⟨10640346122538080879705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 453988101228291450867413 10640346122538080879705)
                    ·
                      rfl

theorem cell22_31083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_31083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31083 prefixEnd_31083 := by exact prefixLift 31083
  have htrace : WordTrace (prefixWord ++ tailWord_31083) baseStart_31083 baseEnd_31083 := by
    simpa [prefixWord, tailWord_31083, baseEnd_31083] using wordTrace_append hprefix tailTrace_31083
  have hstable : (prefixWord ++ tailWord_31083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31083).length < 2 ^ (prefixWord ++ tailWord_31083).sum := by decide
  have hdescent : baseEnd_31083 < baseStart_31083 := by decide
  rcases family_descends (prefixWord ++ tailWord_31083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31115 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 3, 4]
def baseStart_31115 : Nat := 118140960795 + 31115 * 2 ^ 59
def prefixEnd_31115 : Nat := 4983230072969 + 3 ^ 40 * 31115 * 2
def baseEnd_31115 : Nat := 10651300376500664079607

theorem tailTrace_31115 : CollatzResearch.WordTrace tailWord_31115 prefixEnd_31115 10651300376500664079607 := by
  unfold tailWord_31115
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134857282283143864038799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 756571521522095909359199 1134857282283143864038799)
  ·
    refine ⟨1702285923424715796058199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134857282283143864038799 1702285923424715796058199)
    ·
      refine ⟨2553428885137073694087299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702285923424715796058199 2553428885137073694087299)
      ·
        refine ⟨3830143327705610541130949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553428885137073694087299 3830143327705610541130949)
        ·
          refine ⟨718151873944801976462053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3830143327705610541130949 718151873944801976462053)
          ·
            refine ⟨134653476364650370586635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 718151873944801976462053 134653476364650370586635)
            ·
              refine ⟨201980214546975555879953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134653476364650370586635 201980214546975555879953)
              ·
                refine ⟨151485160910231666909965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201980214546975555879953 151485160910231666909965)
                ·
                  refine ⟨56806935341336875091237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151485160910231666909965 56806935341336875091237)
                  ·
                    refine ⟨10651300376500664079607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56806935341336875091237 10651300376500664079607)
                    ·
                      rfl

theorem cell22_31115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_31115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31115 prefixEnd_31115 := by exact prefixLift 31115
  have htrace : WordTrace (prefixWord ++ tailWord_31115) baseStart_31115 baseEnd_31115 := by
    simpa [prefixWord, tailWord_31115, baseEnd_31115] using wordTrace_append hprefix tailTrace_31115
  have hstable : (prefixWord ++ tailWord_31115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31115).length < 2 ^ (prefixWord ++ tailWord_31115).sum := by decide
  have hdescent : baseEnd_31115 < baseStart_31115 := by decide
  rcases family_descends (prefixWord ++ tailWord_31115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31130 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_31130 : Nat := 118140960795 + 31130 * 2 ^ 59
def prefixEnd_31130 : Nat := 4983230072969 + 3 ^ 40 * 31130 * 2
def baseEnd_31130 : Nat := 3552145061015208318187

theorem tailTrace_31130 : CollatzResearch.WordTrace tailWord_31130 prefixEnd_31130 3552145061015208318187 := by
  unfold tailWord_31130
  simp only [CollatzResearch.WordTrace]
  refine ⟨283851094307200356458711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 756936251485867617223229 283851094307200356458711)
  ·
    refine ⟨425776641460800534688067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283851094307200356458711 425776641460800534688067)
    ·
      refine ⟨638664962191200802032101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425776641460800534688067 638664962191200802032101)
      ·
        refine ⟨119749680410850150381019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 638664962191200802032101 119749680410850150381019)
        ·
          refine ⟨179624520616275225571529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119749680410850150381019 179624520616275225571529)
          ·
            refine ⟨134718390462206419178647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179624520616275225571529 134718390462206419178647)
            ·
              refine ⟨202077585693309628767971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134718390462206419178647 202077585693309628767971)
              ·
                refine ⟨303116378539964443151957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202077585693309628767971 303116378539964443151957)
                ·
                  refine ⟨3552145061015208318187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 303116378539964443151957 3552145061015208318187)
                  ·
                    rfl

theorem cell22_31130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_31130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31130 prefixEnd_31130 := by exact prefixLift 31130
  have htrace : WordTrace (prefixWord ++ tailWord_31130) baseStart_31130 baseEnd_31130 := by
    simpa [prefixWord, tailWord_31130, baseEnd_31130] using wordTrace_append hprefix tailTrace_31130
  have hstable : (prefixWord ++ tailWord_31130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31130).length < 2 ^ (prefixWord ++ tailWord_31130).sum := by decide
  have hdescent : baseEnd_31130 < baseStart_31130 := by decide
  rcases family_descends (prefixWord ++ tailWord_31130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31160 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_31160 : Nat := 118140960795 + 31160 * 2 ^ 59
def prefixEnd_31160 : Nat := 4983230072969 + 3 ^ 40 * 31160 * 2
def baseEnd_31160 : Nat := 10666704796135546704469

theorem tailTrace_31160 : CollatzResearch.WordTrace tailWord_31160 prefixEnd_31160 10666704796135546704469 := by
  unfold tailWord_31160
  simp only [CollatzResearch.WordTrace]
  refine ⟨568249283560058274713467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 757665711413411032951289 568249283560058274713467)
  ·
    refine ⟨852373925340087412070201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 568249283560058274713467 852373925340087412070201)
    ·
      refine ⟨639280444005065559052651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 852373925340087412070201 639280444005065559052651)
      ·
        refine ⟨958920666007598338578977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639280444005065559052651 958920666007598338578977)
        ·
          refine ⟨719190499505698753934233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958920666007598338578977 719190499505698753934233)
          ·
            refine ⟨539392874629274065450675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719190499505698753934233 539392874629274065450675)
            ·
              refine ⟨809089311943911098176013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539392874629274065450675 809089311943911098176013)
              ·
                refine ⟨303408491978966661816005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809089311943911098176013 303408491978966661816005)
                ·
                  refine ⟨56889092246056249090501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303408491978966661816005 56889092246056249090501)
                  ·
                    refine ⟨10666704796135546704469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56889092246056249090501 10666704796135546704469)
                    ·
                      rfl

theorem cell22_31160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_31160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31160 prefixEnd_31160 := by exact prefixLift 31160
  have htrace : WordTrace (prefixWord ++ tailWord_31160) baseStart_31160 baseEnd_31160 := by
    simpa [prefixWord, tailWord_31160, baseEnd_31160] using wordTrace_append hprefix tailTrace_31160
  have hstable : (prefixWord ++ tailWord_31160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31160).length < 2 ^ (prefixWord ++ tailWord_31160).sum := by decide
  have hdescent : baseEnd_31160 < baseStart_31160 := by decide
  rcases family_descends (prefixWord ++ tailWord_31160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31164 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 4]
def baseStart_31164 : Nat := 118140960795 + 31164 * 2 ^ 59
def prefixEnd_31164 : Nat := 4983230072969 + 3 ^ 40 * 31164 * 2
def baseEnd_31164 : Nat := 3556024692626956534819

theorem tailTrace_31164 : CollatzResearch.WordTrace tailWord_31164 prefixEnd_31164 3556024692626956534819 := by
  unfold tailWord_31164
  simp only [CollatzResearch.WordTrace]
  refine ⟨568322229552812616286273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 757762972737083488381697 568322229552812616286273)
  ·
    refine ⟨426241672164609462214705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 568322229552812616286273 426241672164609462214705)
    ·
      refine ⟨319681254123457096661029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426241672164609462214705 319681254123457096661029)
      ·
        refine ⟨59940235148148205623943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319681254123457096661029 59940235148148205623943)
        ·
          refine ⟨89910352722222308435915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59940235148148205623943 89910352722222308435915)
          ·
            refine ⟨134865529083333462653873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89910352722222308435915 134865529083333462653873)
            ·
              refine ⟨101149146812500096990405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134865529083333462653873 101149146812500096990405)
              ·
                refine ⟨18965465027343768185701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101149146812500096990405 18965465027343768185701)
                ·
                  refine ⟨3556024692626956534819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18965465027343768185701 3556024692626956534819)
                  ·
                    rfl

theorem cell22_31164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_31164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31164 prefixEnd_31164 := by exact prefixLift 31164
  have htrace : WordTrace (prefixWord ++ tailWord_31164) baseStart_31164 baseEnd_31164 := by
    simpa [prefixWord, tailWord_31164, baseEnd_31164] using wordTrace_append hprefix tailTrace_31164
  have hstable : (prefixWord ++ tailWord_31164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31164).length < 2 ^ (prefixWord ++ tailWord_31164).sum := by decide
  have hdescent : baseEnd_31164 < baseStart_31164 := by decide
  rcases family_descends (prefixWord ++ tailWord_31164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31222 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_31222 : Nat := 118140960795 + 31222 * 2 ^ 59
def prefixEnd_31222 : Nat := 4983230072969 + 3 ^ 40 * 31222 * 2
def baseEnd_31222 : Nat := 10687928663188051654279

theorem tailTrace_31222 : CollatzResearch.WordTrace tailWord_31222 prefixEnd_31222 10687928663188051654279 := by
  unfold tailWord_31222
  simp only [CollatzResearch.WordTrace]
  refine ⟨71172493305968821136495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 759173261930334092122613 71172493305968821136495)
  ·
    refine ⟨106758739958953231704743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71172493305968821136495 106758739958953231704743)
    ·
      refine ⟨160138109938429847557115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106758739958953231704743 160138109938429847557115)
      ·
        refine ⟨240207164907644771335673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160138109938429847557115 240207164907644771335673)
        ·
          refine ⟨180155373680733578501755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240207164907644771335673 180155373680733578501755)
          ·
            refine ⟨270233060521100367752633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180155373680733578501755 270233060521100367752633)
            ·
              refine ⟨202674795390825275814475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270233060521100367752633 202674795390825275814475)
              ·
                refine ⟨304012193086237913721713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202674795390825275814475 304012193086237913721713)
                ·
                  refine ⟨228009144814678435291285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304012193086237913721713 228009144814678435291285)
                  ·
                    refine ⟨10687928663188051654279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228009144814678435291285 10687928663188051654279)
                    ·
                      rfl

theorem cell22_31222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_31222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31222 prefixEnd_31222 := by exact prefixLift 31222
  have htrace : WordTrace (prefixWord ++ tailWord_31222) baseStart_31222 baseEnd_31222 := by
    simpa [prefixWord, tailWord_31222, baseEnd_31222] using wordTrace_append hprefix tailTrace_31222
  have hstable : (prefixWord ++ tailWord_31222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31222).length < 2 ^ (prefixWord ++ tailWord_31222).sum := by decide
  have hdescent : baseEnd_31222 < baseStart_31222 := by decide
  rcases family_descends (prefixWord ++ tailWord_31222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31235 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_31235 : Nat := 118140960795 + 31235 * 2 ^ 59
def prefixEnd_31235 : Nat := 4983230072969 + 3 ^ 40 * 31235 * 2
def baseEnd_31235 : Nat := 10692378828860351079239

theorem tailTrace_31235 : CollatzResearch.WordTrace tailWord_31235 prefixEnd_31235 10692378828860351079239 := by
  unfold tailWord_31235
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139234041848404358407159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 759489361232269572271439 1139234041848404358407159)
  ·
    refine ⟨1708851062772606537610739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139234041848404358407159 1708851062772606537610739)
    ·
      refine ⟨2563276594158909806416109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708851062772606537610739 2563276594158909806416109)
      ·
        refine ⟨961228722809591177406041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2563276594158909806416109 961228722809591177406041)
        ·
          refine ⟨720921542107193383054531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 961228722809591177406041 720921542107193383054531)
          ·
            refine ⟨1081382313160790074581797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720921542107193383054531 1081382313160790074581797)
            ·
              refine ⟨202759183717648138984087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1081382313160790074581797 202759183717648138984087)
              ·
                refine ⟨304138775576472208476131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202759183717648138984087 304138775576472208476131)
                ·
                  refine ⟨456208163364708312714197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304138775576472208476131 456208163364708312714197)
                  ·
                    refine ⟨10692378828860351079239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 456208163364708312714197 10692378828860351079239)
                    ·
                      rfl

theorem cell22_31235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_31235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31235 prefixEnd_31235 := by exact prefixLift 31235
  have htrace : WordTrace (prefixWord ++ tailWord_31235) baseStart_31235 baseEnd_31235 := by
    simpa [prefixWord, tailWord_31235, baseEnd_31235] using wordTrace_append hprefix tailTrace_31235
  have hstable : (prefixWord ++ tailWord_31235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31235).length < 2 ^ (prefixWord ++ tailWord_31235).sum := by decide
  have hdescent : baseEnd_31235 < baseStart_31235 := by decide
  rcases family_descends (prefixWord ++ tailWord_31235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31312 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_31312 : Nat := 118140960795 + 31312 * 2 ^ 59
def prefixEnd_31312 : Nat := 4983230072969 + 3 ^ 40 * 31312 * 2
def baseEnd_31312 : Nat := 10718737502457816904003

theorem tailTrace_31312 : CollatzResearch.WordTrace tailWord_31312 prefixEnd_31312 10718737502457816904003 := by
  unfold tailWord_31312
  simp only [CollatzResearch.WordTrace]
  refine ⟨571021231284723254480095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 761361641712964339306793 571021231284723254480095)
  ·
    refine ⟨856531846927084881720143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 571021231284723254480095 856531846927084881720143)
    ·
      refine ⟨1284797770390627322580215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856531846927084881720143 1284797770390627322580215)
      ·
        refine ⟨1927196655585940983870323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284797770390627322580215 1927196655585940983870323)
        ·
          refine ⟨2890794983378911475805485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927196655585940983870323 2890794983378911475805485)
          ·
            refine ⟨1084048118767091803427057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2890794983378911475805485 1084048118767091803427057)
            ·
              refine ⟨813036089075318852570293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084048118767091803427057 813036089075318852570293)
              ·
                refine ⟨76222133350811142428465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 813036089075318852570293 76222133350811142428465)
                ·
                  refine ⟨57166600013108356821349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76222133350811142428465 57166600013108356821349)
                  ·
                    refine ⟨10718737502457816904003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57166600013108356821349 10718737502457816904003)
                    ·
                      rfl

theorem cell22_31312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_31312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31312 prefixEnd_31312 := by exact prefixLift 31312
  have htrace : WordTrace (prefixWord ++ tailWord_31312) baseStart_31312 baseEnd_31312 := by
    simpa [prefixWord, tailWord_31312, baseEnd_31312] using wordTrace_append hprefix tailTrace_31312
  have hstable : (prefixWord ++ tailWord_31312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31312).length < 2 ^ (prefixWord ++ tailWord_31312).sum := by decide
  have hdescent : baseEnd_31312 < baseStart_31312 := by decide
  rcases family_descends (prefixWord ++ tailWord_31312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31314 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_31314 : Nat := 118140960795 + 31314 * 2 ^ 59
def prefixEnd_31314 : Nat := 4983230072969 + 3 ^ 40 * 31314 * 2
def baseEnd_31314 : Nat := 10719422143330478353997

theorem tailTrace_31314 : CollatzResearch.WordTrace tailWord_31314 prefixEnd_31314 10719422143330478353997 := by
  unfold tailWord_31314
  simp only [CollatzResearch.WordTrace]
  refine ⟨285528852140550212633249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 761410272374800567021997 285528852140550212633249)
  ·
    refine ⟨214146639105412659474937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285528852140550212633249 214146639105412659474937)
    ·
      refine ⟨160609979329059494606203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214146639105412659474937 160609979329059494606203)
      ·
        refine ⟨240914968993589241909305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160609979329059494606203 240914968993589241909305)
        ·
          refine ⟨180686226745191931431979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240914968993589241909305 180686226745191931431979)
          ·
            refine ⟨271029340117787897147969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180686226745191931431979 271029340117787897147969)
            ·
              refine ⟨203272005088340922860977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271029340117787897147969 203272005088340922860977)
              ·
                refine ⟨152454003816255692145733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203272005088340922860977 152454003816255692145733)
                ·
                  refine ⟨28585125715547942277325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152454003816255692145733 28585125715547942277325)
                  ·
                    refine ⟨10719422143330478353997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28585125715547942277325 10719422143330478353997)
                    ·
                      rfl

theorem cell22_31314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_31314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31314 prefixEnd_31314 := by exact prefixLift 31314
  have htrace : WordTrace (prefixWord ++ tailWord_31314) baseStart_31314 baseEnd_31314 := by
    simpa [prefixWord, tailWord_31314, baseEnd_31314] using wordTrace_append hprefix tailTrace_31314
  have hstable : (prefixWord ++ tailWord_31314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31314).length < 2 ^ (prefixWord ++ tailWord_31314).sum := by decide
  have hdescent : baseEnd_31314 < baseStart_31314 := by decide
  rcases family_descends (prefixWord ++ tailWord_31314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31316 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 4]
def baseStart_31316 : Nat := 118140960795 + 31316 * 2 ^ 59
def prefixEnd_31316 : Nat := 4983230072969 + 3 ^ 40 * 31316 * 2
def baseEnd_31316 : Nat := 3573368928067713267997

theorem tailTrace_31316 : CollatzResearch.WordTrace tailWord_31316 prefixEnd_31316 3573368928067713267997 := by
  unfold tailWord_31316
  simp only [CollatzResearch.WordTrace]
  refine ⟨571094177277477596052901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 761458903036636794737201 571094177277477596052901)
  ·
    refine ⟨107080158239527049259919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 571094177277477596052901 107080158239527049259919)
    ·
      refine ⟨160620237359290573889879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107080158239527049259919 160620237359290573889879)
      ·
        refine ⟨240930356038935860834819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160620237359290573889879 240930356038935860834819)
        ·
          refine ⟨361395534058403791252229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240930356038935860834819 361395534058403791252229)
          ·
            refine ⟨67761662635950710859793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361395534058403791252229 67761662635950710859793)
            ·
              refine ⟨50821246976963033144845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67761662635950710859793 50821246976963033144845)
              ·
                refine ⟨19057967616361137429317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50821246976963033144845 19057967616361137429317)
                ·
                  refine ⟨3573368928067713267997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19057967616361137429317 3573368928067713267997)
                  ·
                    rfl

theorem cell22_31316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_31316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31316 prefixEnd_31316 := by exact prefixLift 31316
  have htrace : WordTrace (prefixWord ++ tailWord_31316) baseStart_31316 baseEnd_31316 := by
    simpa [prefixWord, tailWord_31316, baseEnd_31316] using wordTrace_append hprefix tailTrace_31316
  have hstable : (prefixWord ++ tailWord_31316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31316).length < 2 ^ (prefixWord ++ tailWord_31316).sum := by decide
  have hdescent : baseEnd_31316 < baseStart_31316 := by decide
  rcases family_descends (prefixWord ++ tailWord_31316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31393 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_31393 : Nat := 118140960795 + 31393 * 2 ^ 59
def prefixEnd_31393 : Nat := 4983230072969 + 3 ^ 40 * 31393 * 2
def baseEnd_31393 : Nat := 10746465457800605628755

theorem tailTrace_31393 : CollatzResearch.WordTrace tailWord_31393 prefixEnd_31393 10746465457800605628755 := by
  unfold tailWord_31393
  simp only [CollatzResearch.WordTrace]
  refine ⟨1144996775275997342658833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 763331183517331561772555 1144996775275997342658833)
  ·
    refine ⟨858747581456998006994125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1144996775275997342658833 858747581456998006994125)
    ·
      refine ⟨322030343046374252622797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 858747581456998006994125 322030343046374252622797)
      ·
        refine ⟨120761378642390344733549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322030343046374252622797 120761378642390344733549)
        ·
          refine ⟨45285516990896379275081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120761378642390344733549 45285516990896379275081)
          ·
            refine ⟨33964137743172284456311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45285516990896379275081 33964137743172284456311)
            ·
              refine ⟨50946206614758426684467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33964137743172284456311 50946206614758426684467)
              ·
                refine ⟨76419309922137640026701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50946206614758426684467 76419309922137640026701)
                ·
                  refine ⟨28657241220801615010013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76419309922137640026701 28657241220801615010013)
                  ·
                    refine ⟨10746465457800605628755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28657241220801615010013 10746465457800605628755)
                    ·
                      rfl

theorem cell22_31393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_31393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31393 prefixEnd_31393 := by exact prefixLift 31393
  have htrace : WordTrace (prefixWord ++ tailWord_31393) baseStart_31393 baseEnd_31393 := by
    simpa [prefixWord, tailWord_31393, baseEnd_31393] using wordTrace_append hprefix tailTrace_31393
  have hstable : (prefixWord ++ tailWord_31393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31393).length < 2 ^ (prefixWord ++ tailWord_31393).sum := by decide
  have hdescent : baseEnd_31393 < baseStart_31393 := by decide
  rcases family_descends (prefixWord ++ tailWord_31393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31417 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 8]
def baseStart_31417 : Nat := 118140960795 + 31417 * 2 ^ 59
def prefixEnd_31417 : Nat := 4983230072969 + 3 ^ 40 * 31417 * 2
def baseEnd_31417 : Nat := 3584893716090847676227

theorem tailTrace_31417 : CollatzResearch.WordTrace tailWord_31417 prefixEnd_31417 3584893716090847676227 := by
  unfold tailWord_31417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145872127189049441532505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 763914751459366294355003 1145872127189049441532505)
  ·
    refine ⟨859404095391787081149379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1145872127189049441532505 859404095391787081149379)
    ·
      refine ⟨1289106143087680621724069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859404095391787081149379 1289106143087680621724069)
      ·
        refine ⟨241707401828940116573263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1289106143087680621724069 241707401828940116573263)
        ·
          refine ⟨362561102743410174859895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241707401828940116573263 362561102743410174859895)
          ·
            refine ⟨543841654115115262289843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362561102743410174859895 543841654115115262289843)
            ·
              refine ⟨815762481172672893434765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543841654115115262289843 815762481172672893434765)
              ·
                refine ⟨305910930439752335038037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815762481172672893434765 305910930439752335038037)
                ·
                  refine ⟨3584893716090847676227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 305910930439752335038037 3584893716090847676227)
                  ·
                    rfl

theorem cell22_31417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_31417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31417 prefixEnd_31417 := by exact prefixLift 31417
  have htrace : WordTrace (prefixWord ++ tailWord_31417) baseStart_31417 baseEnd_31417 := by
    simpa [prefixWord, tailWord_31417, baseEnd_31417] using wordTrace_append hprefix tailTrace_31417
  have hstable : (prefixWord ++ tailWord_31417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31417).length < 2 ^ (prefixWord ++ tailWord_31417).sum := by decide
  have hdescent : baseEnd_31417 < baseStart_31417 := by decide
  rcases family_descends (prefixWord ++ tailWord_31417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31444 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_31444 : Nat := 118140960795 + 31444 * 2 ^ 59
def prefixEnd_31444 : Nat := 4983230072969 + 3 ^ 40 * 31444 * 2
def baseEnd_31444 : Nat := 10763923800053472603599

theorem tailTrace_31444 : CollatzResearch.WordTrace tailWord_31444 prefixEnd_31444 10763923800053472603599 := by
  unfold tailWord_31444
  simp only [CollatzResearch.WordTrace]
  refine ⟨573428449045616526382693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 764571265394155368510257 573428449045616526382693)
  ·
    refine ⟨107517834196053098696755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 573428449045616526382693 107517834196053098696755)
    ·
      refine ⟨161276751294079648045133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107517834196053098696755 161276751294079648045133)
      ·
        refine ⟨60478781735279868016925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161276751294079648045133 60478781735279868016925)
        ·
          refine ⟨22679543150729950506347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60478781735279868016925 22679543150729950506347)
          ·
            refine ⟨34019314726094925759521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22679543150729950506347 34019314726094925759521)
            ·
              refine ⟨25514486044571194319641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34019314726094925759521 25514486044571194319641)
              ·
                refine ⟨19135864533428395739731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25514486044571194319641 19135864533428395739731)
                ·
                  refine ⟨28703796800142593609597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19135864533428395739731 28703796800142593609597)
                  ·
                    refine ⟨10763923800053472603599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28703796800142593609597 10763923800053472603599)
                    ·
                      rfl

theorem cell22_31444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_31444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31444 prefixEnd_31444 := by exact prefixLift 31444
  have htrace : WordTrace (prefixWord ++ tailWord_31444) baseStart_31444 baseEnd_31444 := by
    simpa [prefixWord, tailWord_31444, baseEnd_31444] using wordTrace_append hprefix tailTrace_31444
  have hstable : (prefixWord ++ tailWord_31444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31444).length < 2 ^ (prefixWord ++ tailWord_31444).sum := by decide
  have hdescent : baseEnd_31444 < baseStart_31444 := by decide
  rcases family_descends (prefixWord ++ tailWord_31444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31517 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_31517 : Nat := 118140960795 + 31517 * 2 ^ 59
def prefixEnd_31517 : Nat := 4983230072969 + 3 ^ 40 * 31517 * 2
def baseEnd_31517 : Nat := 10788913191905615528375

theorem tailTrace_31517 : CollatzResearch.WordTrace tailWord_31517 prefixEnd_31517 10788913191905615528375 := by
  unfold tailWord_31517
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149519426826766520172805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 766346284551177680115203 1149519426826766520172805)
  ·
    refine ⟨215534892530018722532401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1149519426826766520172805 215534892530018722532401)
    ·
      refine ⟨161651169397514041899301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215534892530018722532401 161651169397514041899301)
      ·
        refine ⟨30309594262033882856119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161651169397514041899301 30309594262033882856119)
        ·
          refine ⟨45464391393050824284179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30309594262033882856119 45464391393050824284179)
          ·
            refine ⟨68196587089576236426269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45464391393050824284179 68196587089576236426269)
            ·
              refine ⟨25573720158591088659851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68196587089576236426269 25573720158591088659851)
              ·
                refine ⟨38360580237886632989777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25573720158591088659851 38360580237886632989777)
                ·
                  refine ⟨28770435178414974742333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38360580237886632989777 28770435178414974742333)
                  ·
                    refine ⟨10788913191905615528375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28770435178414974742333 10788913191905615528375)
                    ·
                      rfl

theorem cell22_31517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_31517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31517 prefixEnd_31517 := by exact prefixLift 31517
  have htrace : WordTrace (prefixWord ++ tailWord_31517) baseStart_31517 baseEnd_31517 := by
    simpa [prefixWord, tailWord_31517, baseEnd_31517] using wordTrace_append hprefix tailTrace_31517
  have hstable : (prefixWord ++ tailWord_31517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31517).length < 2 ^ (prefixWord ++ tailWord_31517).sum := by decide
  have hdescent : baseEnd_31517 < baseStart_31517 := by decide
  rcases family_descends (prefixWord ++ tailWord_31517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31530 : List Nat := [3, 1, 4, 3, 1, 2, 2, 6]
def baseStart_31530 : Nat := 118140960795 + 31530 * 2 ^ 59
def prefixEnd_31530 : Nat := 4983230072969 + 3 ^ 40 * 31530 * 2
def baseEnd_31530 : Nat := 1199262595286434994815

theorem tailTrace_31530 : CollatzResearch.WordTrace tailWord_31530 prefixEnd_31530 1199262595286434994815 := by
  unfold tailWord_31530
  simp only [CollatzResearch.WordTrace]
  refine ⟨287498393944917435099011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 766662383853113160264029 287498393944917435099011)
  ·
    refine ⟨431247590917376152648517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287498393944917435099011 431247590917376152648517)
    ·
      refine ⟨80858923297008028621597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431247590917376152648517 80858923297008028621597)
      ·
        refine ⟨30322096236378010733099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80858923297008028621597 30322096236378010733099)
        ·
          refine ⟨45483144354567016099649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30322096236378010733099 45483144354567016099649)
          ·
            refine ⟨34112358265925262074737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45483144354567016099649 34112358265925262074737)
            ·
              refine ⟨25584268699443946556053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34112358265925262074737 25584268699443946556053)
              ·
                refine ⟨1199262595286434994815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25584268699443946556053 1199262595286434994815)
                ·
                  rfl

theorem cell22_31530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_31530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31530 prefixEnd_31530 := by exact prefixLift 31530
  have htrace : WordTrace (prefixWord ++ tailWord_31530) baseStart_31530 baseEnd_31530 := by
    simpa [prefixWord, tailWord_31530, baseEnd_31530] using wordTrace_append hprefix tailTrace_31530
  have hstable : (prefixWord ++ tailWord_31530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31530).length < 2 ^ (prefixWord ++ tailWord_31530).sum := by decide
  have hdescent : baseEnd_31530 < baseStart_31530 := by decide
  rcases family_descends (prefixWord ++ tailWord_31530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31588 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_31588 : Nat := 118140960795 + 31588 * 2 ^ 59
def prefixEnd_31588 : Nat := 4983230072969 + 3 ^ 40 * 31588 * 2
def baseEnd_31588 : Nat := 10813217942885097003157

theorem tailTrace_31588 : CollatzResearch.WordTrace tailWord_31588 prefixEnd_31588 10813217942885097003157 := by
  unfold tailWord_31588
  simp only [CollatzResearch.WordTrace]
  refine ⟨576054504784772823003709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 768072673046363764004945 576054504784772823003709)
  ·
    refine ⟨216020439294289808626391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 576054504784772823003709 216020439294289808626391)
    ·
      refine ⟨324030658941434712939587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216020439294289808626391 324030658941434712939587)
      ·
        refine ⟨486045988412152069409381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324030658941434712939587 486045988412152069409381)
        ·
          refine ⟨91133622827278513014259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486045988412152069409381 91133622827278513014259)
          ·
            refine ⟨136700434240917769521389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91133622827278513014259 136700434240917769521389)
            ·
              refine ⟨51262662840344163570521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136700434240917769521389 51262662840344163570521)
              ·
                refine ⟨38446997130258122677891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51262662840344163570521 38446997130258122677891)
                ·
                  refine ⟨57670495695387184016837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38446997130258122677891 57670495695387184016837)
                  ·
                    refine ⟨10813217942885097003157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57670495695387184016837 10813217942885097003157)
                    ·
                      rfl

theorem cell22_31588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_31588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31588 prefixEnd_31588 := by exact prefixLift 31588
  have htrace : WordTrace (prefixWord ++ tailWord_31588) baseStart_31588 baseEnd_31588 := by
    simpa [prefixWord, tailWord_31588, baseEnd_31588] using wordTrace_append hprefix tailTrace_31588
  have hstable : (prefixWord ++ tailWord_31588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31588).length < 2 ^ (prefixWord ++ tailWord_31588).sum := by decide
  have hdescent : baseEnd_31588 < baseStart_31588 := by decide
  rcases family_descends (prefixWord ++ tailWord_31588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31599 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_31599 : Nat := 118140960795 + 31599 * 2 ^ 59
def prefixEnd_31599 : Nat := 4983230072969 + 3 ^ 40 * 31599 * 2
def baseEnd_31599 : Nat := 10816983467684734978123

theorem tailTrace_31599 : CollatzResearch.WordTrace tailWord_31599 prefixEnd_31599 10816983467684734978123 := by
  unfold tailWord_31599
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152510212529694524657851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 768340141686463016438567 1152510212529694524657851)
  ·
    refine ⟨1728765318794541786986777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1152510212529694524657851 1728765318794541786986777)
    ·
      refine ⟨1296573989095906340240083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1728765318794541786986777 1296573989095906340240083)
      ·
        refine ⟨1944860983643859510360125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296573989095906340240083 1944860983643859510360125)
        ·
          refine ⟨729322868866447316385047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1944860983643859510360125 729322868866447316385047)
          ·
            refine ⟨1093984303299670974577571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729322868866447316385047 1093984303299670974577571)
            ·
              refine ⟨1640976454949506461866357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093984303299670974577571 1640976454949506461866357)
              ·
                refine ⟨153841542651516230799971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1640976454949506461866357 153841542651516230799971)
                ·
                  refine ⟨230762313977274346199957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153841542651516230799971 230762313977274346199957)
                  ·
                    refine ⟨10816983467684734978123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230762313977274346199957 10816983467684734978123)
                    ·
                      rfl

theorem cell22_31599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_31599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31599 prefixEnd_31599 := by exact prefixLift 31599
  have htrace : WordTrace (prefixWord ++ tailWord_31599) baseStart_31599 baseEnd_31599 := by
    simpa [prefixWord, tailWord_31599, baseEnd_31599] using wordTrace_append hprefix tailTrace_31599
  have hstable : (prefixWord ++ tailWord_31599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31599).length < 2 ^ (prefixWord ++ tailWord_31599).sum := by decide
  have hdescent : baseEnd_31599 < baseStart_31599 := by decide
  rcases family_descends (prefixWord ++ tailWord_31599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31601 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_31601 : Nat := 118140960795 + 31601 * 2 ^ 59
def prefixEnd_31601 : Nat := 4983230072969 + 3 ^ 40 * 31601 * 2
def baseEnd_31601 : Nat := 10817668108557396428117

theorem tailTrace_31601 : CollatzResearch.WordTrace tailWord_31601 prefixEnd_31601 10817668108557396428117 := by
  unfold tailWord_31601
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152583158522448866230657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 768388772348299244153771 1152583158522448866230657)
  ·
    refine ⟨864437368891836649672993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1152583158522448866230657 864437368891836649672993)
    ·
      refine ⟨648328026668877487254745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 864437368891836649672993 648328026668877487254745)
      ·
        refine ⟨486246020001658115441059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648328026668877487254745 486246020001658115441059)
        ·
          refine ⟨729369030002487173161589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486246020001658115441059 729369030002487173161589)
          ·
            refine ⟨68378346562733172483899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 729369030002487173161589 68378346562733172483899)
            ·
              refine ⟨102567519844099758725849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68378346562733172483899 102567519844099758725849)
              ·
                refine ⟨76925639883074819044387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102567519844099758725849 76925639883074819044387)
                ·
                  refine ⟨115388459824612228566581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76925639883074819044387 115388459824612228566581)
                  ·
                    refine ⟨10817668108557396428117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115388459824612228566581 10817668108557396428117)
                    ·
                      rfl

theorem cell22_31601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_31601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31601 prefixEnd_31601 := by exact prefixLift 31601
  have htrace : WordTrace (prefixWord ++ tailWord_31601) baseStart_31601 baseEnd_31601 := by
    simpa [prefixWord, tailWord_31601, baseEnd_31601] using wordTrace_append hprefix tailTrace_31601
  have hstable : (prefixWord ++ tailWord_31601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31601).length < 2 ^ (prefixWord ++ tailWord_31601).sum := by decide
  have hdescent : baseEnd_31601 < baseStart_31601 := by decide
  rcases family_descends (prefixWord ++ tailWord_31601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31605 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_31605 : Nat := 118140960795 + 31605 * 2 ^ 59
def prefixEnd_31605 : Nat := 4983230072969 + 3 ^ 40 * 31605 * 2
def baseEnd_31605 : Nat := 10819037390302719328105

theorem tailTrace_31605 : CollatzResearch.WordTrace tailWord_31605 prefixEnd_31605 10819037390302719328105 := by
  unfold tailWord_31605
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152729050507957549376269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 768486033671971699584179 1152729050507957549376269)
  ·
    refine ⟨432273393940484081016101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1152729050507957549376269 432273393940484081016101)
    ·
      refine ⟨81051261363840765190519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432273393940484081016101 81051261363840765190519)
      ·
        refine ⟨121576892045761147785779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81051261363840765190519 121576892045761147785779)
        ·
          refine ⟨182365338068641721678669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121576892045761147785779 182365338068641721678669)
          ·
            refine ⟨68387001775740645629501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182365338068641721678669 68387001775740645629501)
            ·
              refine ⟨25645125665902742111063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68387001775740645629501 25645125665902742111063)
              ·
                refine ⟨38467688498854113166595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25645125665902742111063 38467688498854113166595)
                ·
                  refine ⟨57701532748281169749893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38467688498854113166595 57701532748281169749893)
                  ·
                    refine ⟨10819037390302719328105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57701532748281169749893 10819037390302719328105)
                    ·
                      rfl

theorem cell22_31605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_31605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31605 prefixEnd_31605 := by exact prefixLift 31605
  have htrace : WordTrace (prefixWord ++ tailWord_31605) baseStart_31605 baseEnd_31605 := by
    simpa [prefixWord, tailWord_31605, baseEnd_31605] using wordTrace_append hprefix tailTrace_31605
  have hstable : (prefixWord ++ tailWord_31605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31605).length < 2 ^ (prefixWord ++ tailWord_31605).sum := by decide
  have hdescent : baseEnd_31605 < baseStart_31605 := by decide
  rcases family_descends (prefixWord ++ tailWord_31605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31650 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_31650 : Nat := 118140960795 + 31650 * 2 ^ 59
def prefixEnd_31650 : Nat := 4983230072969 + 3 ^ 40 * 31650 * 2
def baseEnd_31650 : Nat := 10834441809937601952967

theorem tailTrace_31650 : CollatzResearch.WordTrace tailWord_31650 prefixEnd_31650 10834441809937601952967 := by
  unfold tailWord_31650
  simp only [CollatzResearch.WordTrace]
  refine ⟨288592583836232558691101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 769580223563286823176269 288592583836232558691101)
  ·
    refine ⟨108222218938587209509163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288592583836232558691101 108222218938587209509163)
    ·
      refine ⟨162333328407880814263745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108222218938587209509163 162333328407880814263745)
      ·
        refine ⟨121749996305910610697809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162333328407880814263745 121749996305910610697809)
        ·
          refine ⟨91312497229432958023357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121749996305910610697809 91312497229432958023357)
          ·
            refine ⟨34242186461037359258759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91312497229432958023357 34242186461037359258759)
            ·
              refine ⟨51363279691556038888139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34242186461037359258759 51363279691556038888139)
              ·
                refine ⟨77044919537334058332209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51363279691556038888139 77044919537334058332209)
                ·
                  refine ⟨57783689653000543749157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77044919537334058332209 57783689653000543749157)
                  ·
                    refine ⟨10834441809937601952967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57783689653000543749157 10834441809937601952967)
                    ·
                      rfl

theorem cell22_31650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_31650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31650 prefixEnd_31650 := by exact prefixLift 31650
  have htrace : WordTrace (prefixWord ++ tailWord_31650) baseStart_31650 baseEnd_31650 := by
    simpa [prefixWord, tailWord_31650, baseEnd_31650] using wordTrace_append hprefix tailTrace_31650
  have hstable : (prefixWord ++ tailWord_31650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31650).length < 2 ^ (prefixWord ++ tailWord_31650).sum := by decide
  have hdescent : baseEnd_31650 < baseStart_31650 := by decide
  rcases family_descends (prefixWord ++ tailWord_31650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31659 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 9]
def baseStart_31659 : Nat := 118140960795 + 31659 * 2 ^ 59
def prefixEnd_31659 : Nat := 4983230072969 + 3 ^ 40 * 31659 * 2
def baseEnd_31659 : Nat := 3612507564621526159313

theorem tailTrace_31659 : CollatzResearch.WordTrace tailWord_31659 prefixEnd_31659 3612507564621526159313 := by
  unfold tailWord_31659
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154698592312324771842031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 769799061541549847894687 1154698592312324771842031)
  ·
    refine ⟨1732047888468487157763047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1154698592312324771842031 1732047888468487157763047)
    ·
      refine ⟨2598071832702730736644571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732047888468487157763047 2598071832702730736644571)
      ·
        refine ⟨3897107749054096104966857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598071832702730736644571 3897107749054096104966857)
        ·
          refine ⟨2922830811790572078725143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3897107749054096104966857 2922830811790572078725143)
          ·
            refine ⟨4384246217685858118087715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922830811790572078725143 4384246217685858118087715)
            ·
              refine ⟨6576369326528787177131573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384246217685858118087715 6576369326528787177131573)
              ·
                refine ⟨616534624362073797856085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6576369326528787177131573 616534624362073797856085)
                ·
                  refine ⟨3612507564621526159313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 616534624362073797856085 3612507564621526159313)
                  ·
                    rfl

theorem cell22_31659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_31659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31659 prefixEnd_31659 := by exact prefixLift 31659
  have htrace : WordTrace (prefixWord ++ tailWord_31659) baseStart_31659 baseEnd_31659 := by
    simpa [prefixWord, tailWord_31659, baseEnd_31659] using wordTrace_append hprefix tailTrace_31659
  have hstable : (prefixWord ++ tailWord_31659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31659).length < 2 ^ (prefixWord ++ tailWord_31659).sum := by decide
  have hdescent : baseEnd_31659 < baseStart_31659 := by decide
  rcases family_descends (prefixWord ++ tailWord_31659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31680 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 1, 3]
def baseStart_31680 : Nat := 118140960795 + 31680 * 2 ^ 59
def prefixEnd_31680 : Nat := 4983230072969 + 3 ^ 40 * 31680 * 2
def baseEnd_31680 : Nat := 10844711423027523702875

theorem tailTrace_31680 : CollatzResearch.WordTrace tailWord_31680 prefixEnd_31680 10844711423027523702875 := by
  unfold tailWord_31680
  simp only [CollatzResearch.WordTrace]
  refine ⟨577732262618122679178247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 770309683490830238904329 577732262618122679178247)
  ·
    refine ⟨866598393927184018767371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577732262618122679178247 866598393927184018767371)
    ·
      refine ⟨1299897590890776028151057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866598393927184018767371 1299897590890776028151057)
      ·
        refine ⟨974923193168082021113293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299897590890776028151057 974923193168082021113293)
        ·
          refine ⟨365596197438030757917485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 974923193168082021113293 365596197438030757917485)
          ·
            refine ⟨137098574039261534219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365596197438030757917485 137098574039261534219057)
            ·
              refine ⟨102823930529446150664293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137098574039261534219057 102823930529446150664293)
              ·
                refine ⟨19279486974271153249555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102823930529446150664293 19279486974271153249555)
                ·
                  refine ⟨28919230461406729874333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19279486974271153249555 28919230461406729874333)
                  ·
                    refine ⟨10844711423027523702875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28919230461406729874333 10844711423027523702875)
                    ·
                      rfl

theorem cell22_31680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_31680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31680 prefixEnd_31680 := by exact prefixLift 31680
  have htrace : WordTrace (prefixWord ++ tailWord_31680) baseStart_31680 baseEnd_31680 := by
    simpa [prefixWord, tailWord_31680, baseEnd_31680] using wordTrace_append hprefix tailTrace_31680
  have hstable : (prefixWord ++ tailWord_31680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31680).length < 2 ^ (prefixWord ++ tailWord_31680).sum := by decide
  have hdescent : baseEnd_31680 < baseStart_31680 := by decide
  rcases family_descends (prefixWord ++ tailWord_31680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31686 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_31686 : Nat := 118140960795 + 31686 * 2 ^ 59
def prefixEnd_31686 : Nat := 4983230072969 + 3 ^ 40 * 31686 * 2
def baseEnd_31686 : Nat := 10846765345645508052857

theorem tailTrace_31686 : CollatzResearch.WordTrace tailWord_31686 prefixEnd_31686 10846765345645508052857 := by
  unfold tailWord_31686
  simp only [CollatzResearch.WordTrace]
  refine ⟨36115105100453386971091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 770455575476338922049941 36115105100453386971091)
  ·
    refine ⟨54172657650680080456637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36115105100453386971091 54172657650680080456637)
    ·
      refine ⟨20314746619005030171239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54172657650680080456637 20314746619005030171239)
      ·
        refine ⟨30472119928507545256859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20314746619005030171239 30472119928507545256859)
        ·
          refine ⟨45708179892761317885289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30472119928507545256859 45708179892761317885289)
          ·
            refine ⟨34281134919570988413967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45708179892761317885289 34281134919570988413967)
            ·
              refine ⟨51421702379356482620951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34281134919570988413967 51421702379356482620951)
              ·
                refine ⟨77132553569034723931427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51421702379356482620951 77132553569034723931427)
                ·
                  refine ⟨115698830353552085897141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77132553569034723931427 115698830353552085897141)
                  ·
                    refine ⟨10846765345645508052857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115698830353552085897141 10846765345645508052857)
                    ·
                      rfl

theorem cell22_31686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_31686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31686 prefixEnd_31686 := by exact prefixLift 31686
  have htrace : WordTrace (prefixWord ++ tailWord_31686) baseStart_31686 baseEnd_31686 := by
    simpa [prefixWord, tailWord_31686, baseEnd_31686] using wordTrace_append hprefix tailTrace_31686
  have hstable : (prefixWord ++ tailWord_31686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31686).length < 2 ^ (prefixWord ++ tailWord_31686).sum := by decide
  have hdescent : baseEnd_31686 < baseStart_31686 := by decide
  rcases family_descends (prefixWord ++ tailWord_31686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31691 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 2, 5]
def baseStart_31691 : Nat := 118140960795 + 31691 * 2 ^ 59
def prefixEnd_31691 : Nat := 4983230072969 + 3 ^ 40 * 31691 * 2
def baseEnd_31691 : Nat := 10848476947827161677841

theorem tailTrace_31691 : CollatzResearch.WordTrace tailWord_31691 prefixEnd_31691 10848476947827161677841 := by
  unfold tailWord_31691
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155865728196394237006927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 770577152130929491337951 1155865728196394237006927)
  ·
    refine ⟨1733798592294591355510391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1155865728196394237006927 1733798592294591355510391)
    ·
      refine ⟨2600697888441887033265587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733798592294591355510391 2600697888441887033265587)
      ·
        refine ⟨3901046832662830549898381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600697888441887033265587 3901046832662830549898381)
        ·
          refine ⟨1462892562248561456211893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3901046832662830549898381 1462892562248561456211893)
          ·
            refine ⟨137146177710802636519865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1462892562248561456211893 137146177710802636519865)
            ·
              refine ⟨102859633283101977389899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137146177710802636519865 102859633283101977389899)
              ·
                refine ⟨154289449924652966084849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102859633283101977389899 154289449924652966084849)
                ·
                  refine ⟨115717087443489724563637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154289449924652966084849 115717087443489724563637)
                  ·
                    refine ⟨10848476947827161677841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115717087443489724563637 10848476947827161677841)
                    ·
                      rfl

theorem cell22_31691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_31691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31691 prefixEnd_31691 := by exact prefixLift 31691
  have htrace : WordTrace (prefixWord ++ tailWord_31691) baseStart_31691 baseEnd_31691 := by
    simpa [prefixWord, tailWord_31691, baseEnd_31691] using wordTrace_append hprefix tailTrace_31691
  have hstable : (prefixWord ++ tailWord_31691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31691).length < 2 ^ (prefixWord ++ tailWord_31691).sum := by decide
  have hdescent : baseEnd_31691 < baseStart_31691 := by decide
  rcases family_descends (prefixWord ++ tailWord_31691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31714 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_31714 : Nat := 118140960795 + 31714 * 2 ^ 59
def prefixEnd_31714 : Nat := 4983230072969 + 3 ^ 40 * 31714 * 2
def baseEnd_31714 : Nat := 10856350317862768352771

theorem tailTrace_31714 : CollatzResearch.WordTrace tailWord_31714 prefixEnd_31714 10856350317862768352771 := by
  unfold tailWord_31714
  simp only [CollatzResearch.WordTrace]
  refine ⟨289176151778267291273549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 771136404742046110062797 289176151778267291273549)
  ·
    refine ⟨108441056916850234227581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289176151778267291273549 108441056916850234227581)
    ·
      refine ⟨40665396343818837835343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108441056916850234227581 40665396343818837835343)
      ·
        refine ⟨60998094515728256753015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40665396343818837835343 60998094515728256753015)
        ·
          refine ⟨91497141773592385129523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60998094515728256753015 91497141773592385129523)
          ·
            refine ⟨137245712660388577694285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91497141773592385129523 137245712660388577694285)
            ·
              refine ⟨51467142247645716635357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137245712660388577694285 51467142247645716635357)
              ·
                refine ⟨19300178342867143738259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51467142247645716635357 19300178342867143738259)
                ·
                  refine ⟨28950267514300715607389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19300178342867143738259 28950267514300715607389)
                  ·
                    refine ⟨10856350317862768352771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28950267514300715607389 10856350317862768352771)
                    ·
                      rfl

theorem cell22_31714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_31714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31714 prefixEnd_31714 := by exact prefixLift 31714
  have htrace : WordTrace (prefixWord ++ tailWord_31714) baseStart_31714 baseEnd_31714 := by
    simpa [prefixWord, tailWord_31714, baseEnd_31714] using wordTrace_append hprefix tailTrace_31714
  have hstable : (prefixWord ++ tailWord_31714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31714).length < 2 ^ (prefixWord ++ tailWord_31714).sum := by decide
  have hdescent : baseEnd_31714 < baseStart_31714 := by decide
  rcases family_descends (prefixWord ++ tailWord_31714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31738 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_31738 : Nat := 118140960795 + 31738 * 2 ^ 59
def prefixEnd_31738 : Nat := 4983230072969 + 3 ^ 40 * 31738 * 2
def baseEnd_31738 : Nat := 3621522002778235250899

theorem tailTrace_31738 : CollatzResearch.WordTrace tailWord_31738 prefixEnd_31738 3621522002778235250899 := by
  unfold tailWord_31738
  simp only [CollatzResearch.WordTrace]
  refine ⟨289394989756530315991967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 771719972684080842645245 289394989756530315991967)
  ·
    refine ⟨434092484634795473987951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289394989756530315991967 434092484634795473987951)
    ·
      refine ⟨651138726952193210981927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434092484634795473987951 651138726952193210981927)
      ·
        refine ⟨976708090428289816472891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651138726952193210981927 976708090428289816472891)
        ·
          refine ⟨1465062135642434724709337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976708090428289816472891 1465062135642434724709337)
          ·
            refine ⟨1098796601731826043532003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465062135642434724709337 1098796601731826043532003)
            ·
              refine ⟨1648194902597739065298005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098796601731826043532003 1648194902597739065298005)
              ·
                refine ⟨19314784014817254671461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1648194902597739065298005 19314784014817254671461)
                ·
                  refine ⟨3621522002778235250899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19314784014817254671461 3621522002778235250899)
                  ·
                    rfl

theorem cell22_31738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_31738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31738 prefixEnd_31738 := by exact prefixLift 31738
  have htrace : WordTrace (prefixWord ++ tailWord_31738) baseStart_31738 baseEnd_31738 := by
    simpa [prefixWord, tailWord_31738, baseEnd_31738] using wordTrace_append hprefix tailTrace_31738
  have hstable : (prefixWord ++ tailWord_31738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31738).length < 2 ^ (prefixWord ++ tailWord_31738).sum := by decide
  have hdescent : baseEnd_31738 < baseStart_31738 := by decide
  rcases family_descends (prefixWord ++ tailWord_31738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31768 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_31768 : Nat := 118140960795 + 31768 * 2 ^ 59
def prefixEnd_31768 : Nat := 4983230072969 + 3 ^ 40 * 31768 * 2
def baseEnd_31768 : Nat := 10874835621424627502605

theorem tailTrace_31768 : CollatzResearch.WordTrace tailWord_31768 prefixEnd_31768 10874835621424627502605 := by
  unfold tailWord_31768
  simp only [CollatzResearch.WordTrace]
  refine ⟨579337074458718193779979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 772449432611624258373305 579337074458718193779979)
  ·
    refine ⟨869005611688077290669969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 579337074458718193779979 869005611688077290669969)
    ·
      refine ⟨651754208766057968002477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 869005611688077290669969 651754208766057968002477)
      ·
        refine ⟨244407828287271738000929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651754208766057968002477 244407828287271738000929)
        ·
          refine ⟨183305871215453803500697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244407828287271738000929 183305871215453803500697)
          ·
            refine ⟨137479403411590352625523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183305871215453803500697 137479403411590352625523)
            ·
              refine ⟨206219105117385528938285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137479403411590352625523 206219105117385528938285)
              ·
                refine ⟨77332164419019573351857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206219105117385528938285 77332164419019573351857)
                ·
                  refine ⟨57999123314264680013893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77332164419019573351857 57999123314264680013893)
                  ·
                    refine ⟨10874835621424627502605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57999123314264680013893 10874835621424627502605)
                    ·
                      rfl

theorem cell22_31768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_31768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31768 prefixEnd_31768 := by exact prefixLift 31768
  have htrace : WordTrace (prefixWord ++ tailWord_31768) baseStart_31768 baseEnd_31768 := by
    simpa [prefixWord, tailWord_31768, baseEnd_31768] using wordTrace_append hprefix tailTrace_31768
  have hstable : (prefixWord ++ tailWord_31768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31768).length < 2 ^ (prefixWord ++ tailWord_31768).sum := by decide
  have hdescent : baseEnd_31768 < baseStart_31768 := by decide
  rcases family_descends (prefixWord ++ tailWord_31768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31783 : List Nat := [1, 1, 7, 1, 1, 11]
def baseStart_31783 : Nat := 118140960795 + 31783 * 2 ^ 59
def prefixEnd_31783 : Nat := 4983230072969 + 3 ^ 40 * 31783 * 2
def baseEnd_31783 : Nat := 134320622567525782439

theorem tailTrace_31783 : CollatzResearch.WordTrace tailWord_31783 prefixEnd_31783 134320622567525782439 := by
  unfold tailWord_31783
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159221243863093949356003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 772814162575395966237335 1159221243863093949356003)
  ·
    refine ⟨1738831865794640924034005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1159221243863093949356003 1738831865794640924034005)
    ·
      refine ⟨40753871854561896657047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1738831865794640924034005 40753871854561896657047)
      ·
        refine ⟨61130807781842844985571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40753871854561896657047 61130807781842844985571)
        ·
          refine ⟨91696211672764267478357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61130807781842844985571 91696211672764267478357)
          ·
            refine ⟨134320622567525782439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 91696211672764267478357 134320622567525782439)
            ·
              rfl

theorem cell22_31783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 11].length) (baseStart_31783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31783 prefixEnd_31783 := by exact prefixLift 31783
  have htrace : WordTrace (prefixWord ++ tailWord_31783) baseStart_31783 baseEnd_31783 := by
    simpa [prefixWord, tailWord_31783, baseEnd_31783] using wordTrace_append hprefix tailTrace_31783
  have hstable : (prefixWord ++ tailWord_31783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31783).length < 2 ^ (prefixWord ++ tailWord_31783).sum := by decide
  have hdescent : baseEnd_31783 < baseStart_31783 := by decide
  rcases family_descends (prefixWord ++ tailWord_31783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31815 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 3, 3]
def baseStart_31815 : Nat := 118140960795 + 31815 * 2 ^ 59
def prefixEnd_31815 : Nat := 4983230072969 + 3 ^ 40 * 31815 * 2
def baseEnd_31815 : Nat := 10890924681932171577461

theorem tailTrace_31815 : CollatzResearch.WordTrace tailWord_31815 prefixEnd_31815 10890924681932171577461 := by
  unfold tailWord_31815
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160388379747163414520899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 773592253164775609680599 1160388379747163414520899)
  ·
    refine ⟨1740582569620745121781349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1160388379747163414520899 1740582569620745121781349)
    ·
      refine ⟨326359231803889710334003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1740582569620745121781349 326359231803889710334003)
      ·
        refine ⟨489538847705834565501005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326359231803889710334003 489538847705834565501005)
        ·
          refine ⟨183577067889687962062877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489538847705834565501005 183577067889687962062877)
          ·
            refine ⟨68841400458632985773579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183577067889687962062877 68841400458632985773579)
            ·
              refine ⟨103262100687949478660369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68841400458632985773579 103262100687949478660369)
              ·
                refine ⟨77446575515962108995277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103262100687949478660369 77446575515962108995277)
                ·
                  refine ⟨29042465818485790873229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77446575515962108995277 29042465818485790873229)
                  ·
                    refine ⟨10890924681932171577461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29042465818485790873229 10890924681932171577461)
                    ·
                      rfl

theorem cell22_31815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_31815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31815 prefixEnd_31815 := by exact prefixLift 31815
  have htrace : WordTrace (prefixWord ++ tailWord_31815) baseStart_31815 baseEnd_31815 := by
    simpa [prefixWord, tailWord_31815, baseEnd_31815] using wordTrace_append hprefix tailTrace_31815
  have hstable : (prefixWord ++ tailWord_31815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31815).length < 2 ^ (prefixWord ++ tailWord_31815).sum := by decide
  have hdescent : baseEnd_31815 < baseStart_31815 := by decide
  rcases family_descends (prefixWord ++ tailWord_31815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31832 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 1, 3]
def baseStart_31832 : Nat := 118140960795 + 31832 * 2 ^ 59
def prefixEnd_31832 : Nat := 4983230072969 + 3 ^ 40 * 31832 * 2
def baseEnd_31832 : Nat := 10896744129349793902409

theorem tailTrace_31832 : CollatzResearch.WordTrace tailWord_31832 prefixEnd_31832 10896744129349793902409 := by
  unfold tailWord_31832
  simp only [CollatzResearch.WordTrace]
  refine ⟨580504210342787658944875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 774005613790383545259833 580504210342787658944875)
  ·
    refine ⟨870756315514181488417313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580504210342787658944875 870756315514181488417313)
    ·
      refine ⟨653067236635636116312985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 870756315514181488417313 653067236635636116312985)
      ·
        refine ⟨489800427476727087234739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653067236635636116312985 489800427476727087234739)
        ·
          refine ⟨734700641215090630852109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489800427476727087234739 734700641215090630852109)
          ·
            refine ⟨275512740455658986569541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 734700641215090630852109 275512740455658986569541)
            ·
              refine ⟨51658638835436059981789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275512740455658986569541 51658638835436059981789)
              ·
                refine ⟨19371989563288522493171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51658638835436059981789 19371989563288522493171)
                ·
                  refine ⟨29057984344932783739757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19371989563288522493171 29057984344932783739757)
                  ·
                    refine ⟨10896744129349793902409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29057984344932783739757 10896744129349793902409)
                    ·
                      rfl

theorem cell22_31832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_31832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31832 prefixEnd_31832 := by exact prefixLift 31832
  have htrace : WordTrace (prefixWord ++ tailWord_31832) baseStart_31832 baseEnd_31832 := by
    simpa [prefixWord, tailWord_31832, baseEnd_31832] using wordTrace_append hprefix tailTrace_31832
  have hstable : (prefixWord ++ tailWord_31832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31832).length < 2 ^ (prefixWord ++ tailWord_31832).sum := by decide
  have hdescent : baseEnd_31832 < baseStart_31832 := by decide
  rcases family_descends (prefixWord ++ tailWord_31832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31862 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_31862 : Nat := 118140960795 + 31862 * 2 ^ 59
def prefixEnd_31862 : Nat := 4983230072969 + 3 ^ 40 * 31862 * 2
def baseEnd_31862 : Nat := 3635671247479905217439

theorem tailTrace_31862 : CollatzResearch.WordTrace tailWord_31862 prefixEnd_31862 3635671247479905217439 := by
  unfold tailWord_31862
  simp only [CollatzResearch.WordTrace]
  refine ⟨72631413161055652592615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 774735073717926960987893 72631413161055652592615)
  ·
    refine ⟨108947119741583478888923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72631413161055652592615 108947119741583478888923)
    ·
      refine ⟨163420679612375218333385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108947119741583478888923 163420679612375218333385)
      ·
        refine ⟨122565509709281413750039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163420679612375218333385 122565509709281413750039)
        ·
          refine ⟨183848264563922120625059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122565509709281413750039 183848264563922120625059)
          ·
            refine ⟨275772396845883180937589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183848264563922120625059 275772396845883180937589)
            ·
              refine ⟨25853662204301548212899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275772396845883180937589 25853662204301548212899)
              ·
                refine ⟨38780493306452322319349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25853662204301548212899 38780493306452322319349)
                ·
                  refine ⟨3635671247479905217439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38780493306452322319349 3635671247479905217439)
                  ·
                    rfl

theorem cell22_31862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_31862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31862 prefixEnd_31862 := by exact prefixLift 31862
  have htrace : WordTrace (prefixWord ++ tailWord_31862) baseStart_31862 baseEnd_31862 := by
    simpa [prefixWord, tailWord_31862, baseEnd_31862] using wordTrace_append hprefix tailTrace_31862
  have hstable : (prefixWord ++ tailWord_31862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31862).length < 2 ^ (prefixWord ++ tailWord_31862).sum := by decide
  have hdescent : baseEnd_31862 < baseStart_31862 := by decide
  rcases family_descends (prefixWord ++ tailWord_31862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31875 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 1, 4]
def baseStart_31875 : Nat := 118140960795 + 31875 * 2 ^ 59
def prefixEnd_31875 : Nat := 4983230072969 + 3 ^ 40 * 31875 * 2
def baseEnd_31875 : Nat := 10911463908112015077277

theorem tailTrace_31875 : CollatzResearch.WordTrace tailWord_31875 prefixEnd_31875 10911463908112015077277 := by
  unfold tailWord_31875
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162576759529793661705079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 775051173019862441136719 1162576759529793661705079)
  ·
    refine ⟨1743865139294690492557619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162576759529793661705079 1743865139294690492557619)
    ·
      refine ⟨2615797708942035738836429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743865139294690492557619 2615797708942035738836429)
      ·
        refine ⟨980924140853263402063661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2615797708942035738836429 980924140853263402063661)
        ·
          refine ⟨367846552819973775773873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 980924140853263402063661 367846552819973775773873)
          ·
            refine ⟨275884914614980331830405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367846552819973775773873 275884914614980331830405)
            ·
              refine ⟨51728421490308812218201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275884914614980331830405 51728421490308812218201)
              ·
                refine ⟨38796316117731609163651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51728421490308812218201 38796316117731609163651)
                ·
                  refine ⟨58194474176597413745477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38796316117731609163651 58194474176597413745477)
                  ·
                    refine ⟨10911463908112015077277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58194474176597413745477 10911463908112015077277)
                    ·
                      rfl

theorem cell22_31875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 4].length) (baseStart_31875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31875 prefixEnd_31875 := by exact prefixLift 31875
  have htrace : WordTrace (prefixWord ++ tailWord_31875) baseStart_31875 baseEnd_31875 := by
    simpa [prefixWord, tailWord_31875, baseEnd_31875] using wordTrace_append hprefix tailTrace_31875
  have hstable : (prefixWord ++ tailWord_31875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31875).length < 2 ^ (prefixWord ++ tailWord_31875).sum := by decide
  have hdescent : baseEnd_31875 < baseStart_31875 := by decide
  rcases family_descends (prefixWord ++ tailWord_31875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31905 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_31905 : Nat := 118140960795 + 31905 * 2 ^ 59
def prefixEnd_31905 : Nat := 4983230072969 + 3 ^ 40 * 31905 * 2
def baseEnd_31905 : Nat := 10921733521201936827185

theorem tailTrace_31905 : CollatzResearch.WordTrace tailWord_31905 prefixEnd_31905 10921733521201936827185 := by
  unfold tailWord_31905
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163670949421108785297169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 775780632947405856864779 1163670949421108785297169)
  ·
    refine ⟨872753212065831588972877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1163670949421108785297169 872753212065831588972877)
    ·
      refine ⟨327282454524686845864829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 872753212065831588972877 327282454524686845864829)
      ·
        refine ⟨122730920446757567199311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327282454524686845864829 122730920446757567199311)
        ·
          refine ⟨184096380670136350798967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122730920446757567199311 184096380670136350798967)
          ·
            refine ⟨276144571005204526198451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184096380670136350798967 276144571005204526198451)
            ·
              refine ⟨414216856507806789297677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276144571005204526198451 414216856507806789297677)
              ·
                refine ⟨155331321190427545986629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414216856507806789297677 155331321190427545986629)
                ·
                  refine ⟨29124622723205164872493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155331321190427545986629 29124622723205164872493)
                  ·
                    refine ⟨10921733521201936827185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29124622723205164872493 10921733521201936827185)
                    ·
                      rfl

theorem cell22_31905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_31905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31905 prefixEnd_31905 := by exact prefixLift 31905
  have htrace : WordTrace (prefixWord ++ tailWord_31905) baseStart_31905 baseEnd_31905 := by
    simpa [prefixWord, tailWord_31905, baseEnd_31905] using wordTrace_append hprefix tailTrace_31905
  have hstable : (prefixWord ++ tailWord_31905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31905).length < 2 ^ (prefixWord ++ tailWord_31905).sum := by decide
  have hdescent : baseEnd_31905 < baseStart_31905 := by decide
  rcases family_descends (prefixWord ++ tailWord_31905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31922 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_31922 : Nat := 118140960795 + 31922 * 2 ^ 59
def prefixEnd_31922 : Nat := 4983230072969 + 3 ^ 40 * 31922 * 2
def baseEnd_31922 : Nat := 10927552968619559152133

theorem tailTrace_31922 : CollatzResearch.WordTrace tailWord_31922 prefixEnd_31922 10927552968619559152133 := by
  unfold tailWord_31922
  simp only [CollatzResearch.WordTrace]
  refine ⟨291072747589880172166505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 776193993573013792444013 291072747589880172166505)
  ·
    refine ⟨218304560692410129124879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291072747589880172166505 218304560692410129124879)
    ·
      refine ⟨327456841038615193687319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218304560692410129124879 327456841038615193687319)
      ·
        refine ⟨491185261557922790530979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327456841038615193687319 491185261557922790530979)
        ·
          refine ⟨736777892336884185796469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491185261557922790530979 736777892336884185796469)
          ·
            refine ⟨69072927406582892418419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 736777892336884185796469 69072927406582892418419)
            ·
              refine ⟨103609391109874338627629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69072927406582892418419 103609391109874338627629)
              ·
                refine ⟨38853521666202876985361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103609391109874338627629 38853521666202876985361)
                ·
                  refine ⟨29140141249652157739021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38853521666202876985361 29140141249652157739021)
                  ·
                    refine ⟨10927552968619559152133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29140141249652157739021 10927552968619559152133)
                    ·
                      rfl

theorem cell22_31922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_31922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31922 prefixEnd_31922 := by exact prefixLift 31922
  have htrace : WordTrace (prefixWord ++ tailWord_31922) baseStart_31922 baseEnd_31922 := by
    simpa [prefixWord, tailWord_31922, baseEnd_31922] using wordTrace_append hprefix tailTrace_31922
  have hstable : (prefixWord ++ tailWord_31922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31922).length < 2 ^ (prefixWord ++ tailWord_31922).sum := by decide
  have hdescent : baseEnd_31922 < baseStart_31922 := by decide
  rcases family_descends (prefixWord ++ tailWord_31922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31933 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_31933 : Nat := 118140960795 + 31933 * 2 ^ 59
def prefixEnd_31933 : Nat := 4983230072969 + 3 ^ 40 * 31933 * 2
def baseEnd_31933 : Nat := 10931318493419197127099

theorem tailTrace_31933 : CollatzResearch.WordTrace tailWord_31933 prefixEnd_31933 10931318493419197127099 := by
  unfold tailWord_31933
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164692193319669567316453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 776461462213113044877635 1164692193319669567316453)
  ·
    refine ⟨218379786247438043871835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1164692193319669567316453 218379786247438043871835)
    ·
      refine ⟨327569679371157065807753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218379786247438043871835 327569679371157065807753)
      ·
        refine ⟨245677259528367799355815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327569679371157065807753 245677259528367799355815)
        ·
          refine ⟨368515889292551699033723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245677259528367799355815 368515889292551699033723)
          ·
            refine ⟨552773833938827548550585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368515889292551699033723 552773833938827548550585)
            ·
              refine ⟨414580375454120661412939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552773833938827548550585 414580375454120661412939)
              ·
                refine ⟨621870563181180992119409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414580375454120661412939 621870563181180992119409)
                ·
                  refine ⟨466402922385885744089557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621870563181180992119409 466402922385885744089557)
                  ·
                    refine ⟨10931318493419197127099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 466402922385885744089557 10931318493419197127099)
                    ·
                      rfl

theorem cell22_31933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_31933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31933 prefixEnd_31933 := by exact prefixLift 31933
  have htrace : WordTrace (prefixWord ++ tailWord_31933) baseStart_31933 baseEnd_31933 := by
    simpa [prefixWord, tailWord_31933, baseEnd_31933] using wordTrace_append hprefix tailTrace_31933
  have hstable : (prefixWord ++ tailWord_31933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31933).length < 2 ^ (prefixWord ++ tailWord_31933).sum := by decide
  have hdescent : baseEnd_31933 < baseStart_31933 := by decide
  rcases family_descends (prefixWord ++ tailWord_31933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31937 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_31937 : Nat := 118140960795 + 31937 * 2 ^ 59
def prefixEnd_31937 : Nat := 4983230072969 + 3 ^ 40 * 31937 * 2
def baseEnd_31937 : Nat := 10932687775164520027087

theorem tailTrace_31937 : CollatzResearch.WordTrace tailWord_31937 prefixEnd_31937 10932687775164520027087 := by
  unfold tailWord_31937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164838085305178250462065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 776558723536785500308043 1164838085305178250462065)
  ·
    refine ⟨873628563978883687846549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1164838085305178250462065 873628563978883687846549)
    ·
      refine ⟨40951338936510172867807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 873628563978883687846549 40951338936510172867807)
      ·
        refine ⟨61427008404765259301711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40951338936510172867807 61427008404765259301711)
        ·
          refine ⟨92140512607147888952567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61427008404765259301711 92140512607147888952567)
          ·
            refine ⟨138210768910721833428851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92140512607147888952567 138210768910721833428851)
            ·
              refine ⟨207316153366082750143277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138210768910721833428851 207316153366082750143277)
              ·
                refine ⟨77743557512281031303729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207316153366082750143277 77743557512281031303729)
                ·
                  refine ⟨58307668134210773477797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77743557512281031303729 58307668134210773477797)
                  ·
                    refine ⟨10932687775164520027087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58307668134210773477797 10932687775164520027087)
                    ·
                      rfl

theorem cell22_31937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_31937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31937 prefixEnd_31937 := by exact prefixLift 31937
  have htrace : WordTrace (prefixWord ++ tailWord_31937) baseStart_31937 baseEnd_31937 := by
    simpa [prefixWord, tailWord_31937, baseEnd_31937] using wordTrace_append hprefix tailTrace_31937
  have hstable : (prefixWord ++ tailWord_31937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31937).length < 2 ^ (prefixWord ++ tailWord_31937).sum := by decide
  have hdescent : baseEnd_31937 < baseStart_31937 := by decide
  rcases family_descends (prefixWord ++ tailWord_31937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31956 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_31956 : Nat := 118140960795 + 31956 * 2 ^ 59
def prefixEnd_31956 : Nat := 4983230072969 + 3 ^ 40 * 31956 * 2
def baseEnd_31956 : Nat := 10939191863454803802029

theorem tailTrace_31956 : CollatzResearch.WordTrace tailWord_31956 prefixEnd_31956 10939191863454803802029 := by
  unfold tailWord_31956
  simp only [CollatzResearch.WordTrace]
  refine ⟨582765536118172247701861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 777020714824229663602481 582765536118172247701861)
  ·
    refine ⟨109268538022157296444099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 582765536118172247701861 109268538022157296444099)
    ·
      refine ⟨163902807033235944666149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109268538022157296444099 163902807033235944666149)
      ·
        refine ⟨30731776318731739624903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163902807033235944666149 30731776318731739624903)
        ·
          refine ⟨46097664478097609437355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30731776318731739624903 46097664478097609437355)
          ·
            refine ⟨69146496717146414156033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46097664478097609437355 69146496717146414156033)
            ·
              refine ⟨51859872537859810617025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69146496717146414156033 51859872537859810617025)
              ·
                refine ⟨38894904403394857962769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51859872537859810617025 38894904403394857962769)
                ·
                  refine ⟨29171178302546143472077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38894904403394857962769 29171178302546143472077)
                  ·
                    refine ⟨10939191863454803802029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29171178302546143472077 10939191863454803802029)
                    ·
                      rfl

theorem cell22_31956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_31956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31956 prefixEnd_31956 := by exact prefixLift 31956
  have htrace : WordTrace (prefixWord ++ tailWord_31956) baseStart_31956 baseEnd_31956 := by
    simpa [prefixWord, tailWord_31956, baseEnd_31956] using wordTrace_append hprefix tailTrace_31956
  have hstable : (prefixWord ++ tailWord_31956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31956).length < 2 ^ (prefixWord ++ tailWord_31956).sum := by decide
  have hdescent : baseEnd_31956 < baseStart_31956 := by decide
  rcases family_descends (prefixWord ++ tailWord_31956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31958 : List Nat := [5, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_31958 : Nat := 118140960795 + 31958 * 2 ^ 59
def prefixEnd_31958 : Nat := 4983230072969 + 3 ^ 40 * 31958 * 2
def baseEnd_31958 : Nat := 3646625501442488417341

theorem tailTrace_31958 : CollatzResearch.WordTrace tailWord_31958 prefixEnd_31958 3646625501442488417341 := by
  unfold tailWord_31958
  simp only [CollatzResearch.WordTrace]
  refine ⟨72850251139318677311033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 777069345486065891317685 72850251139318677311033)
  ·
    refine ⟨54637688354489007983275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72850251139318677311033 54637688354489007983275)
    ·
      refine ⟨81956532531733511974913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54637688354489007983275 81956532531733511974913)
      ·
        refine ⟨61467399398800133981185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81956532531733511974913 61467399398800133981185)
        ·
          refine ⟨46100549549100100485889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61467399398800133981185 46100549549100100485889)
          ·
            refine ⟨34575412161825075364417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46100549549100100485889 34575412161825075364417)
            ·
              refine ⟨25931559121368806523313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34575412161825075364417 25931559121368806523313)
              ·
                refine ⟨19448669341026604892485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25931559121368806523313 19448669341026604892485)
                ·
                  refine ⟨3646625501442488417341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19448669341026604892485 3646625501442488417341)
                  ·
                    rfl

theorem cell22_31958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_31958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31958 prefixEnd_31958 := by exact prefixLift 31958
  have htrace : WordTrace (prefixWord ++ tailWord_31958) baseStart_31958 baseEnd_31958 := by
    simpa [prefixWord, tailWord_31958, baseEnd_31958] using wordTrace_append hprefix tailTrace_31958
  have hstable : (prefixWord ++ tailWord_31958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31958).length < 2 ^ (prefixWord ++ tailWord_31958).sum := by decide
  have hdescent : baseEnd_31958 < baseStart_31958 := by decide
  rcases family_descends (prefixWord ++ tailWord_31958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31980 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_31980 : Nat := 118140960795 + 31980 * 2 ^ 59
def prefixEnd_31980 : Nat := 4983230072969 + 3 ^ 40 * 31980 * 2
def baseEnd_31980 : Nat := 3649135851308913733985

theorem tailTrace_31980 : CollatzResearch.WordTrace tailWord_31980 prefixEnd_31980 3649135851308913733985 := by
  unfold tailWord_31980
  simp only [CollatzResearch.WordTrace]
  refine ⟨583203212074698297138697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 777604282766264396184929 583203212074698297138697)
  ·
    refine ⟨437402409056023722854023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 583203212074698297138697 437402409056023722854023)
    ·
      refine ⟨656103613584035584281035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437402409056023722854023 656103613584035584281035)
      ·
        refine ⟨984155420376053376421553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656103613584035584281035 984155420376053376421553)
        ·
          refine ⟨738116565282040032316165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984155420376053376421553 738116565282040032316165)
          ·
            refine ⟨138396855990382506059281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 738116565282040032316165 138396855990382506059281)
            ·
              refine ⟨103797641992786879544461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138396855990382506059281 103797641992786879544461)
              ·
                refine ⟨38924115747295079829173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103797641992786879544461 38924115747295079829173)
                ·
                  refine ⟨3649135851308913733985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38924115747295079829173 3649135851308913733985)
                  ·
                    rfl

theorem cell22_31980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_31980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31980 prefixEnd_31980 := by exact prefixLift 31980
  have htrace : WordTrace (prefixWord ++ tailWord_31980) baseStart_31980 baseEnd_31980 := by
    simpa [prefixWord, tailWord_31980, baseEnd_31980] using wordTrace_append hprefix tailTrace_31980
  have hstable : (prefixWord ++ tailWord_31980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31980).length < 2 ^ (prefixWord ++ tailWord_31980).sum := by decide
  have hdescent : baseEnd_31980 < baseStart_31980 := by decide
  rcases family_descends (prefixWord ++ tailWord_31980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31988 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_31988 : Nat := 118140960795 + 31988 * 2 ^ 59
def prefixEnd_31988 : Nat := 4983230072969 + 3 ^ 40 * 31988 * 2
def baseEnd_31988 : Nat := 10950146117417387001931

theorem tailTrace_31988 : CollatzResearch.WordTrace tailWord_31988 prefixEnd_31988 10950146117417387001931 := by
  unfold tailWord_31988
  simp only [CollatzResearch.WordTrace]
  refine ⟨583349104060206980284309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 777798805413609307045745 583349104060206980284309)
  ·
    refine ⟨27344489252822202200827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 583349104060206980284309 27344489252822202200827)
    ·
      refine ⟨41016733879233303301241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27344489252822202200827 41016733879233303301241)
      ·
        refine ⟨30762550409424977475931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41016733879233303301241 30762550409424977475931)
        ·
          refine ⟨46143825614137466213897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30762550409424977475931 46143825614137466213897)
          ·
            refine ⟨34607869210603099660423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46143825614137466213897 34607869210603099660423)
            ·
              refine ⟨51911803815904649490635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34607869210603099660423 51911803815904649490635)
              ·
                refine ⟨77867705723856974235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51911803815904649490635 77867705723856974235953)
                ·
                  refine ⟨58400779292892730676965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77867705723856974235953 58400779292892730676965)
                  ·
                    refine ⟨10950146117417387001931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58400779292892730676965 10950146117417387001931)
                    ·
                      rfl

theorem cell22_31988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_31988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_31988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_31988 prefixEnd_31988 := by exact prefixLift 31988
  have htrace : WordTrace (prefixWord ++ tailWord_31988) baseStart_31988 baseEnd_31988 := by
    simpa [prefixWord, tailWord_31988, baseEnd_31988] using wordTrace_append hprefix tailTrace_31988
  have hstable : (prefixWord ++ tailWord_31988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31988).length < 2 ^ (prefixWord ++ tailWord_31988).sum := by decide
  have hdescent : baseEnd_31988 < baseStart_31988 := by decide
  rcases family_descends (prefixWord ++ tailWord_31988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32042 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_32042 : Nat := 118140960795 + 32042 * 2 ^ 59
def prefixEnd_32042 : Nat := 4983230072969 + 3 ^ 40 * 32042 * 2
def baseEnd_32042 : Nat := 3656210473659748717255

theorem tailTrace_32042 : CollatzResearch.WordTrace tailWord_32042 prefixEnd_32042 3656210473659748717255 := by
  unfold tailWord_32042
  simp only [CollatzResearch.WordTrace]
  refine ⟨292166937481195295758595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 779111833283187455356253 292166937481195295758595)
  ·
    refine ⟨438250406221792943637893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292166937481195295758595 438250406221792943637893)
    ·
      refine ⟨82171951166586176932105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438250406221792943637893 82171951166586176932105)
      ·
        refine ⟨61628963374939632699079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82171951166586176932105 61628963374939632699079)
        ·
          refine ⟨92443445062409449048619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61628963374939632699079 92443445062409449048619)
          ·
            refine ⟨138665167593614173572929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92443445062409449048619 138665167593614173572929)
            ·
              refine ⟨103998875695210630179697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138665167593614173572929 103998875695210630179697)
              ·
                refine ⟨77999156771407972634773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103998875695210630179697 77999156771407972634773)
                ·
                  refine ⟨3656210473659748717255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77999156771407972634773 3656210473659748717255)
                  ·
                    rfl

theorem cell22_32042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_32042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32042 prefixEnd_32042 := by exact prefixLift 32042
  have htrace : WordTrace (prefixWord ++ tailWord_32042) baseStart_32042 baseEnd_32042 := by
    simpa [prefixWord, tailWord_32042, baseEnd_32042] using wordTrace_append hprefix tailTrace_32042
  have hstable : (prefixWord ++ tailWord_32042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32042).length < 2 ^ (prefixWord ++ tailWord_32042).sum := by decide
  have hdescent : baseEnd_32042 < baseStart_32042 := by decide
  rcases family_descends (prefixWord ++ tailWord_32042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32119 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 1, 3]
def baseStart_32119 : Nat := 118140960795 + 32119 * 2 ^ 59
def prefixEnd_32119 : Nat := 4983230072969 + 3 ^ 40 * 32119 * 2
def baseEnd_32119 : Nat := 10994990094576711976529

theorem tailTrace_32119 : CollatzResearch.WordTrace tailWord_32119 prefixEnd_32119 10994990094576711976529 := by
  unfold tailWord_32119
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171476170645823333587411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 780984113763882222391607 1171476170645823333587411)
  ·
    refine ⟨1757214255968735000381117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171476170645823333587411 1757214255968735000381117)
    ·
      refine ⟨658955345988275625142919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1757214255968735000381117 658955345988275625142919)
      ·
        refine ⟨988433018982413437714379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658955345988275625142919 988433018982413437714379)
        ·
          refine ⟨1482649528473620156571569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988433018982413437714379 1482649528473620156571569)
          ·
            refine ⟨1111987146355215117428677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1482649528473620156571569 1111987146355215117428677)
            ·
              refine ⟨208497589941602834517877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1111987146355215117428677 208497589941602834517877)
              ·
                refine ⟨19546649057025265736051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208497589941602834517877 19546649057025265736051)
                ·
                  refine ⟨29319973585537898604077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19546649057025265736051 29319973585537898604077)
                  ·
                    refine ⟨10994990094576711976529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29319973585537898604077 10994990094576711976529)
                    ·
                      rfl

theorem cell22_32119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_32119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32119 prefixEnd_32119 := by exact prefixLift 32119
  have htrace : WordTrace (prefixWord ++ tailWord_32119) baseStart_32119 baseEnd_32119 := by
    simpa [prefixWord, tailWord_32119, baseEnd_32119] using wordTrace_append hprefix tailTrace_32119
  have hstable : (prefixWord ++ tailWord_32119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32119).length < 2 ^ (prefixWord ++ tailWord_32119).sum := by decide
  have hdescent : baseEnd_32119 < baseStart_32119 := by decide
  rcases family_descends (prefixWord ++ tailWord_32119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32132 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_32132 : Nat := 118140960795 + 32132 * 2 ^ 59
def prefixEnd_32132 : Nat := 4983230072969 + 3 ^ 40 * 32132 * 2
def baseEnd_32132 : Nat := 3666480086749670467163

theorem tailTrace_32132 : CollatzResearch.WordTrace tailWord_32132 prefixEnd_32132 3666480086749670467163 := by
  unfold tailWord_32132
  simp only [CollatzResearch.WordTrace]
  refine ⟨585975159799363276905325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 781300213065817702540433 585975159799363276905325)
  ·
    refine ⟨219740684924761228839497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 585975159799363276905325 219740684924761228839497)
    ·
      refine ⟨164805513693570921629623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219740684924761228839497 164805513693570921629623)
      ·
        refine ⟨247208270540356382444435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164805513693570921629623 247208270540356382444435)
        ·
          refine ⟨370812405810534573666653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247208270540356382444435 370812405810534573666653)
          ·
            refine ⟨139054652178950465124995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370812405810534573666653 139054652178950465124995)
            ·
              refine ⟨208581978268425697687493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139054652178950465124995 208581978268425697687493)
              ·
                refine ⟨39109120925329818316405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208581978268425697687493 39109120925329818316405)
                ·
                  refine ⟨3666480086749670467163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39109120925329818316405 3666480086749670467163)
                  ·
                    rfl

theorem cell22_32132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_32132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32132 prefixEnd_32132 := by exact prefixLift 32132
  have htrace : WordTrace (prefixWord ++ tailWord_32132) baseStart_32132 baseEnd_32132 := by
    simpa [prefixWord, tailWord_32132, baseEnd_32132] using wordTrace_append hprefix tailTrace_32132
  have hstable : (prefixWord ++ tailWord_32132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32132).length < 2 ^ (prefixWord ++ tailWord_32132).sum := by decide
  have hdescent : baseEnd_32132 < baseStart_32132 := by decide
  rcases family_descends (prefixWord ++ tailWord_32132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32136 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 1, 3]
def baseStart_32136 : Nat := 118140960795 + 32136 * 2 ^ 59
def prefixEnd_32136 : Nat := 4983230072969 + 3 ^ 40 * 32136 * 2
def baseEnd_32136 : Nat := 11000809541994334301477

theorem tailTrace_32136 : CollatzResearch.WordTrace tailWord_32136 prefixEnd_32136 11000809541994334301477 := by
  unfold tailWord_32136
  simp only [CollatzResearch.WordTrace]
  refine ⟨586048105792117618478131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 781397474389490157970841 586048105792117618478131)
  ·
    refine ⟨879072158688176427717197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 586048105792117618478131 879072158688176427717197)
    ·
      refine ⟨329652059508066160393949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 879072158688176427717197 329652059508066160393949)
      ·
        refine ⟨123619522315524810147731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329652059508066160393949 123619522315524810147731)
        ·
          refine ⟨185429283473287215221597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123619522315524810147731 185429283473287215221597)
          ·
            refine ⟨69535981302482705708099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185429283473287215221597 69535981302482705708099)
            ·
              refine ⟨104303971953724058562149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69535981302482705708099 104303971953724058562149)
              ·
                refine ⟨19556994741323260980403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104303971953724058562149 19556994741323260980403)
                ·
                  refine ⟨29335492111984891470605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19556994741323260980403 29335492111984891470605)
                  ·
                    refine ⟨11000809541994334301477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29335492111984891470605 11000809541994334301477)
                    ·
                      rfl

theorem cell22_32136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_32136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32136 prefixEnd_32136 := by exact prefixLift 32136
  have htrace : WordTrace (prefixWord ++ tailWord_32136) baseStart_32136 baseEnd_32136 := by
    simpa [prefixWord, tailWord_32136, baseEnd_32136] using wordTrace_append hprefix tailTrace_32136
  have hstable : (prefixWord ++ tailWord_32136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32136).length < 2 ^ (prefixWord ++ tailWord_32136).sum := by decide
  have hdescent : baseEnd_32136 < baseStart_32136 := by decide
  rcases family_descends (prefixWord ++ tailWord_32136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32260 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_32260 : Nat := 118140960795 + 32260 * 2 ^ 59
def prefixEnd_32260 : Nat := 4983230072969 + 3 ^ 40 * 32260 * 2
def baseEnd_32260 : Nat := 11043257276099344201097

theorem tailTrace_32260 : CollatzResearch.WordTrace tailWord_32260 prefixEnd_32260 11043257276099344201097 := by
  unfold tailWord_32260
  simp only [CollatzResearch.WordTrace]
  refine ⟨588309431567502207235117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 784412575423336276313489 588309431567502207235117)
  ·
    refine ⟨220616036837813327713169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 588309431567502207235117 220616036837813327713169)
    ·
      refine ⟨165462027628359995784877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220616036837813327713169 165462027628359995784877)
      ·
        refine ⟨62048260360634998419329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165462027628359995784877 62048260360634998419329)
        ·
          refine ⟨46536195270476248814497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62048260360634998419329 46536195270476248814497)
          ·
            refine ⟨34902146452857186610873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46536195270476248814497 34902146452857186610873)
            ·
              refine ⟨26176609839642889958155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34902146452857186610873 26176609839642889958155)
              ·
                refine ⟨39264914759464334937233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26176609839642889958155 39264914759464334937233)
                ·
                  refine ⟨29448686069598251202925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39264914759464334937233 29448686069598251202925)
                  ·
                    refine ⟨11043257276099344201097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29448686069598251202925 11043257276099344201097)
                    ·
                      rfl

theorem cell22_32260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_32260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32260 prefixEnd_32260 := by exact prefixLift 32260
  have htrace : WordTrace (prefixWord ++ tailWord_32260) baseStart_32260 baseEnd_32260 := by
    simpa [prefixWord, tailWord_32260, baseEnd_32260] using wordTrace_append hprefix tailTrace_32260
  have hstable : (prefixWord ++ tailWord_32260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32260).length < 2 ^ (prefixWord ++ tailWord_32260).sum := by decide
  have hdescent : baseEnd_32260 < baseStart_32260 := by decide
  rcases family_descends (prefixWord ++ tailWord_32260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32282 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_32282 : Nat := 118140960795 + 32282 * 2 ^ 59
def prefixEnd_32282 : Nat := 4983230072969 + 3 ^ 40 * 32282 * 2
def baseEnd_32282 : Nat := 11050788325698620151029

theorem tailTrace_32282 : CollatzResearch.WordTrace tailWord_32282 prefixEnd_32282 11050788325698620151029 := by
  unfold tailWord_32282
  simp only [CollatzResearch.WordTrace]
  refine ⟨294355317263825542942775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 784947512703534781180733 294355317263825542942775)
  ·
    refine ⟨441532975895738314414163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294355317263825542942775 441532975895738314414163)
    ·
      refine ⟨662299463843607471621245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441532975895738314414163 662299463843607471621245)
      ·
        refine ⟨248362298941352801857967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662299463843607471621245 248362298941352801857967)
        ·
          refine ⟨372543448412029202786951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248362298941352801857967 372543448412029202786951)
          ·
            refine ⟨558815172618043804180427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372543448412029202786951 558815172618043804180427)
            ·
              refine ⟨838222758927065706270641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558815172618043804180427 838222758927065706270641)
              ·
                refine ⟨628667069195299279702981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838222758927065706270641 628667069195299279702981)
                ·
                  refine ⟨117875075474118614944309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628667069195299279702981 117875075474118614944309)
                  ·
                    refine ⟨11050788325698620151029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117875075474118614944309 11050788325698620151029)
                    ·
                      rfl

theorem cell22_32282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_32282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32282 prefixEnd_32282 := by exact prefixLift 32282
  have htrace : WordTrace (prefixWord ++ tailWord_32282) baseStart_32282 baseEnd_32282 := by
    simpa [prefixWord, tailWord_32282, baseEnd_32282] using wordTrace_append hprefix tailTrace_32282
  have hstable : (prefixWord ++ tailWord_32282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32282).length < 2 ^ (prefixWord ++ tailWord_32282).sum := by decide
  have hdescent : baseEnd_32282 < baseStart_32282 := by decide
  rcases family_descends (prefixWord ++ tailWord_32282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32344 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_32344 : Nat := 118140960795 + 32344 * 2 ^ 59
def prefixEnd_32344 : Nat := 4983230072969 + 3 ^ 40 * 32344 * 2
def baseEnd_32344 : Nat := 11072012192751125100839

theorem tailTrace_32344 : CollatzResearch.WordTrace tailWord_32344 prefixEnd_32344 11072012192751125100839 := by
  unfold tailWord_32344
  simp only [CollatzResearch.WordTrace]
  refine ⟨589841297415343380264043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 786455063220457840352057 589841297415343380264043)
  ·
    refine ⟨884761946123015070396065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589841297415343380264043 884761946123015070396065)
    ·
      refine ⟨663571459592261302797049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 884761946123015070396065 663571459592261302797049)
      ·
        refine ⟨497678594694195977097787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663571459592261302797049 497678594694195977097787)
        ·
          refine ⟨746517892041293965646681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497678594694195977097787 746517892041293965646681)
          ·
            refine ⟨559888419030970474235011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746517892041293965646681 559888419030970474235011)
            ·
              refine ⟨839832628546455711352517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559888419030970474235011 839832628546455711352517)
              ·
                refine ⟨157468617852460445878597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839832628546455711352517 157468617852460445878597)
                ·
                  refine ⟨29525365847336333602237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157468617852460445878597 29525365847336333602237)
                  ·
                    refine ⟨11072012192751125100839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29525365847336333602237 11072012192751125100839)
                    ·
                      rfl

theorem cell22_32344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_32344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32344 prefixEnd_32344 := by exact prefixLift 32344
  have htrace : WordTrace (prefixWord ++ tailWord_32344) baseStart_32344 baseEnd_32344 := by
    simpa [prefixWord, tailWord_32344, baseEnd_32344] using wordTrace_append hprefix tailTrace_32344
  have hstable : (prefixWord ++ tailWord_32344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32344).length < 2 ^ (prefixWord ++ tailWord_32344).sum := by decide
  have hdescent : baseEnd_32344 < baseStart_32344 := by decide
  rcases family_descends (prefixWord ++ tailWord_32344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32348 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_32348 : Nat := 118140960795 + 32348 * 2 ^ 59
def prefixEnd_32348 : Nat := 4983230072969 + 3 ^ 40 * 32348 * 2
def baseEnd_32348 : Nat := 11073381474496448000827

theorem tailTrace_32348 : CollatzResearch.WordTrace tailWord_32348 prefixEnd_32348 11073381474496448000827 := by
  unfold tailWord_32348
  simp only [CollatzResearch.WordTrace]
  refine ⟨589914243408097721836849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 786552324544130295782465 589914243408097721836849)
  ·
    refine ⟨442435682556073291377637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 589914243408097721836849 442435682556073291377637)
    ·
      refine ⟨82956690479263742133307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442435682556073291377637 82956690479263742133307)
      ·
        refine ⟨124435035718895613199961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82956690479263742133307 124435035718895613199961)
        ·
          refine ⟨93326276789171709899971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124435035718895613199961 93326276789171709899971)
          ·
            refine ⟨139989415183757564849957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93326276789171709899971 139989415183757564849957)
            ·
              refine ⟨26248015346954543409367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139989415183757564849957 26248015346954543409367)
              ·
                refine ⟨39372023020431815114051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26248015346954543409367 39372023020431815114051)
                ·
                  refine ⟨59058034530647722671077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39372023020431815114051 59058034530647722671077)
                  ·
                    refine ⟨11073381474496448000827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59058034530647722671077 11073381474496448000827)
                    ·
                      rfl

theorem cell22_32348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_32348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32348 prefixEnd_32348 := by exact prefixLift 32348
  have htrace : WordTrace (prefixWord ++ tailWord_32348) baseStart_32348 baseEnd_32348 := by
    simpa [prefixWord, tailWord_32348, baseEnd_32348] using wordTrace_append hprefix tailTrace_32348
  have hstable : (prefixWord ++ tailWord_32348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32348).length < 2 ^ (prefixWord ++ tailWord_32348).sum := by decide
  have hdescent : baseEnd_32348 < baseStart_32348 := by decide
  rcases family_descends (prefixWord ++ tailWord_32348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32359 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 2, 4]
def baseStart_32359 : Nat := 118140960795 + 32359 * 2 ^ 59
def prefixEnd_32359 : Nat := 4983230072969 + 3 ^ 40 * 32359 * 2
def baseEnd_32359 : Nat := 11077146999296085975793

theorem tailTrace_32359 : CollatzResearch.WordTrace tailWord_32359 prefixEnd_32359 11077146999296085975793 := by
  unfold tailWord_32359
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180229689776344322324131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 786819793184229548216087 1180229689776344322324131)
  ·
    refine ⟨1770344534664516483486197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1180229689776344322324131 1770344534664516483486197)
    ·
      refine ⟨165969800124798420326831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1770344534664516483486197 165969800124798420326831)
      ·
        refine ⟨248954700187197630490247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165969800124798420326831 248954700187197630490247)
        ·
          refine ⟨373432050280796445735371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248954700187197630490247 373432050280796445735371)
          ·
            refine ⟨560148075421194668603057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373432050280796445735371 560148075421194668603057)
            ·
              refine ⟨420111056565896001452293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560148075421194668603057 420111056565896001452293)
              ·
                refine ⟨78770823106105500272305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420111056565896001452293 78770823106105500272305)
                ·
                  refine ⟨59078117329579125204229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78770823106105500272305 59078117329579125204229)
                  ·
                    refine ⟨11077146999296085975793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59078117329579125204229 11077146999296085975793)
                    ·
                      rfl

theorem cell22_32359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_32359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32359 prefixEnd_32359 := by exact prefixLift 32359
  have htrace : WordTrace (prefixWord ++ tailWord_32359) baseStart_32359 baseEnd_32359 := by
    simpa [prefixWord, tailWord_32359, baseEnd_32359] using wordTrace_append hprefix tailTrace_32359
  have hstable : (prefixWord ++ tailWord_32359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32359).length < 2 ^ (prefixWord ++ tailWord_32359).sum := by decide
  have hdescent : baseEnd_32359 < baseStart_32359 := by decide
  rcases family_descends (prefixWord ++ tailWord_32359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32361 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_32361 : Nat := 118140960795 + 32361 * 2 ^ 59
def prefixEnd_32361 : Nat := 4983230072969 + 3 ^ 40 * 32361 * 2
def baseEnd_32361 : Nat := 11077831640168747425787

theorem tailTrace_32361 : CollatzResearch.WordTrace tailWord_32361 prefixEnd_32361 11077831640168747425787 := by
  unfold tailWord_32361
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180302635769098663896937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 786868423846065775931291 1180302635769098663896937)
  ·
    refine ⟨885226976826823997922703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1180302635769098663896937 885226976826823997922703)
    ·
      refine ⟨1327840465240235996884055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885226976826823997922703 1327840465240235996884055)
      ·
        refine ⟨1991760697860353995326083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327840465240235996884055 1991760697860353995326083)
        ·
          refine ⟨2987641046790530992989125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991760697860353995326083 2987641046790530992989125)
          ·
            refine ⟨560182696273224561185461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2987641046790530992989125 560182696273224561185461)
            ·
              refine ⟨52517127775614802611137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 560182696273224561185461 52517127775614802611137)
              ·
                refine ⟨39387845831711101958353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52517127775614802611137 39387845831711101958353)
                ·
                  refine ⟨29540884373783326468765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39387845831711101958353 29540884373783326468765)
                  ·
                    refine ⟨11077831640168747425787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29540884373783326468765 11077831640168747425787)
                    ·
                      rfl

theorem cell22_32361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_32361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32361 prefixEnd_32361 := by exact prefixLift 32361
  have htrace : WordTrace (prefixWord ++ tailWord_32361) baseStart_32361 baseEnd_32361 := by
    simpa [prefixWord, tailWord_32361, baseEnd_32361] using wordTrace_append hprefix tailTrace_32361
  have hstable : (prefixWord ++ tailWord_32361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32361).length < 2 ^ (prefixWord ++ tailWord_32361).sum := by decide
  have hdescent : baseEnd_32361 < baseStart_32361 := by decide
  rcases family_descends (prefixWord ++ tailWord_32361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32391 : List Nat := [1, 1, 4, 2, 1, 5, 2, 6]
def baseStart_32391 : Nat := 118140960795 + 32391 * 2 ^ 59
def prefixEnd_32391 : Nat := 4983230072969 + 3 ^ 40 * 32391 * 2
def baseEnd_32391 : Nat := 1232011250362074352855

theorem tailTrace_32391 : CollatzResearch.WordTrace tailWord_32391 prefixEnd_32391 1232011250362074352855 := by
  unfold tailWord_32391
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181396825660413787489027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 787597883773609191659351 1181396825660413787489027)
  ·
    refine ⟨1772095238490620681233541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181396825660413787489027 1772095238490620681233541)
    ·
      refine ⟨332267857216991377731289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1772095238490620681233541 332267857216991377731289)
      ·
        refine ⟨249200892912743533298467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332267857216991377731289 249200892912743533298467)
        ·
          refine ⟨373801339369115299947701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249200892912743533298467 373801339369115299947701)
          ·
            refine ⟨35043875565854559370097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373801339369115299947701 35043875565854559370097)
            ·
              refine ⟨26282906674390919527573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35043875565854559370097 26282906674390919527573)
              ·
                refine ⟨1232011250362074352855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26282906674390919527573 1232011250362074352855)
                ·
                  rfl

theorem cell22_32391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 6].length) (baseStart_32391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32391 prefixEnd_32391 := by exact prefixLift 32391
  have htrace : WordTrace (prefixWord ++ tailWord_32391) baseStart_32391 baseEnd_32391 := by
    simpa [prefixWord, tailWord_32391, baseEnd_32391] using wordTrace_append hprefix tailTrace_32391
  have hstable : (prefixWord ++ tailWord_32391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32391).length < 2 ^ (prefixWord ++ tailWord_32391).sum := by decide
  have hdescent : baseEnd_32391 < baseStart_32391 := by decide
  rcases family_descends (prefixWord ++ tailWord_32391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32419 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 5]
def baseStart_32419 : Nat := 118140960795 + 32419 * 2 ^ 59
def prefixEnd_32419 : Nat := 4983230072969 + 3 ^ 40 * 32419 * 2
def baseEnd_32419 : Nat := 3699228741825309825203

theorem tailTrace_32419 : CollatzResearch.WordTrace tailWord_32419 prefixEnd_32419 3699228741825309825203 := by
  unfold tailWord_32419
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182418069558974569508311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 788278713039316379672207 1182418069558974569508311)
  ·
    refine ⟨1773627104338461854262467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1182418069558974569508311 1773627104338461854262467)
    ·
      refine ⟨2660440656507692781393701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773627104338461854262467 2660440656507692781393701)
      ·
        refine ⟨498832623095192396511319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2660440656507692781393701 498832623095192396511319)
        ·
          refine ⟨748248934642788594766979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498832623095192396511319 748248934642788594766979)
          ·
            refine ⟨1122373401964182892150469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748248934642788594766979 1122373401964182892150469)
            ·
              refine ⟨210445012868284292278213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1122373401964182892150469 210445012868284292278213)
              ·
                refine ⟨39458439912803304802165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210445012868284292278213 39458439912803304802165)
                ·
                  refine ⟨3699228741825309825203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39458439912803304802165 3699228741825309825203)
                  ·
                    rfl

theorem cell22_32419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 5].length) (baseStart_32419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32419 prefixEnd_32419 := by exact prefixLift 32419
  have htrace : WordTrace (prefixWord ++ tailWord_32419) baseStart_32419 baseEnd_32419 := by
    simpa [prefixWord, tailWord_32419, baseEnd_32419] using wordTrace_append hprefix tailTrace_32419
  have hstable : (prefixWord ++ tailWord_32419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32419).length < 2 ^ (prefixWord ++ tailWord_32419).sum := by decide
  have hdescent : baseEnd_32419 < baseStart_32419 := by decide
  rcases family_descends (prefixWord ++ tailWord_32419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32434 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_32434 : Nat := 118140960795 + 32434 * 2 ^ 59
def prefixEnd_32434 : Nat := 4983230072969 + 3 ^ 40 * 32434 * 2
def baseEnd_32434 : Nat := 11102821032020890350563

theorem tailTrace_32434 : CollatzResearch.WordTrace tailWord_32434 prefixEnd_32434 11102821032020890350563 := by
  unfold tailWord_32434
  simp only [CollatzResearch.WordTrace]
  refine ⟨295741291126158032826089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 788643443003088087536237 295741291126158032826089)
  ·
    refine ⟨221805968344618524619567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295741291126158032826089 221805968344618524619567)
    ·
      refine ⟨332708952516927786929351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221805968344618524619567 332708952516927786929351)
      ·
        refine ⟨499063428775391680394027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332708952516927786929351 499063428775391680394027)
        ·
          refine ⟨748595143163087520591041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499063428775391680394027 748595143163087520591041)
          ·
            refine ⟨561446357372315640443281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748595143163087520591041 561446357372315640443281)
            ·
              refine ⟨421084768029236730332461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561446357372315640443281 421084768029236730332461)
              ·
                refine ⟨157906788010963773874673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421084768029236730332461 157906788010963773874673)
                ·
                  refine ⟨118430091008222830406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157906788010963773874673 118430091008222830406005)
                  ·
                    refine ⟨11102821032020890350563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118430091008222830406005 11102821032020890350563)
                    ·
                      rfl

theorem cell22_32434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_32434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32434 prefixEnd_32434 := by exact prefixLift 32434
  have htrace : WordTrace (prefixWord ++ tailWord_32434) baseStart_32434 baseEnd_32434 := by
    simpa [prefixWord, tailWord_32434, baseEnd_32434] using wordTrace_append hprefix tailTrace_32434
  have hstable : (prefixWord ++ tailWord_32434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32434).length < 2 ^ (prefixWord ++ tailWord_32434).sum := by decide
  have hdescent : baseEnd_32434 < baseStart_32434 := by decide
  rcases family_descends (prefixWord ++ tailWord_32434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32479 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_32479 : Nat := 118140960795 + 32479 * 2 ^ 59
def prefixEnd_32479 : Nat := 4983230072969 + 3 ^ 40 * 32479 * 2
def baseEnd_32479 : Nat := 11118225451655772975425

theorem tailTrace_32479 : CollatzResearch.WordTrace tailWord_32479 prefixEnd_32479 11118225451655772975425 := by
  unfold tailWord_32479
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184606449341604816692491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 789737632894403211128327 1184606449341604816692491)
  ·
    refine ⟨1776909674012407225038737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184606449341604816692491 1776909674012407225038737)
    ·
      refine ⟨1332682255509305418779053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1776909674012407225038737 1332682255509305418779053)
      ·
        refine ⟨499755845815989532042145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1332682255509305418779053 499755845815989532042145)
        ·
          refine ⟨374816884361992149031609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499755845815989532042145 374816884361992149031609)
          ·
            refine ⟨281112663271494111773707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374816884361992149031609 281112663271494111773707)
            ·
              refine ⟨421668994907241167660561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281112663271494111773707 421668994907241167660561)
              ·
                refine ⟨316251746180430875745421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421668994907241167660561 316251746180430875745421)
                ·
                  refine ⟨118594404817661578404533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316251746180430875745421 118594404817661578404533)
                  ·
                    refine ⟨11118225451655772975425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118594404817661578404533 11118225451655772975425)
                    ·
                      rfl

theorem cell22_32479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_32479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32479 prefixEnd_32479 := by exact prefixLift 32479
  have htrace : WordTrace (prefixWord ++ tailWord_32479) baseStart_32479 baseEnd_32479 := by
    simpa [prefixWord, tailWord_32479, baseEnd_32479] using wordTrace_append hprefix tailTrace_32479
  have hstable : (prefixWord ++ tailWord_32479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32479).length < 2 ^ (prefixWord ++ tailWord_32479).sum := by decide
  have hdescent : baseEnd_32479 < baseStart_32479 := by decide
  rcases family_descends (prefixWord ++ tailWord_32479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32500 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_32500 : Nat := 118140960795 + 32500 * 2 ^ 59
def prefixEnd_32500 : Nat := 4983230072969 + 3 ^ 40 * 32500 * 2
def baseEnd_32500 : Nat := 11125414180818718200361

theorem tailTrace_32500 : CollatzResearch.WordTrace tailWord_32500 prefixEnd_32500 11125414180818718200361 := by
  unfold tailWord_32500
  simp only [CollatzResearch.WordTrace]
  refine ⟨592686191132762701603477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 790248254843683602137969 592686191132762701603477)
  ·
    refine ⟨27782165209348251637663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 592686191132762701603477 27782165209348251637663)
    ·
      refine ⟨41673247814022377456495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27782165209348251637663 41673247814022377456495)
      ·
        refine ⟨62509871721033566184743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41673247814022377456495 62509871721033566184743)
        ·
          refine ⟨93764807581550349277115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62509871721033566184743 93764807581550349277115)
          ·
            refine ⟨140647211372325523915673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93764807581550349277115 140647211372325523915673)
            ·
              refine ⟨105485408529244142936755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140647211372325523915673 105485408529244142936755)
              ·
                refine ⟨158228112793866214405133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105485408529244142936755 158228112793866214405133)
                ·
                  refine ⟨59335542297699830401925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158228112793866214405133 59335542297699830401925)
                  ·
                    refine ⟨11125414180818718200361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59335542297699830401925 11125414180818718200361)
                    ·
                      rfl

theorem cell22_32500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_32500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32500 prefixEnd_32500 := by exact prefixLift 32500
  have htrace : WordTrace (prefixWord ++ tailWord_32500) baseStart_32500 baseEnd_32500 := by
    simpa [prefixWord, tailWord_32500, baseEnd_32500] using wordTrace_append hprefix tailTrace_32500
  have hstable : (prefixWord ++ tailWord_32500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32500).length < 2 ^ (prefixWord ++ tailWord_32500).sum := by decide
  have hdescent : baseEnd_32500 < baseStart_32500 := by decide
  rcases family_descends (prefixWord ++ tailWord_32500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32511 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 2, 4]
def baseStart_32511 : Nat := 118140960795 + 32511 * 2 ^ 59
def prefixEnd_32511 : Nat := 4983230072969 + 3 ^ 40 * 32511 * 2
def baseEnd_32511 : Nat := 11129179705618356175327

theorem tailTrace_32511 : CollatzResearch.WordTrace tailWord_32511 prefixEnd_32511 11129179705618356175327 := by
  unfold tailWord_32511
  simp only [CollatzResearch.WordTrace]
  refine ⟨1185773585225674281857387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 790515723483782854571591 1185773585225674281857387)
  ·
    refine ⟨1778660377838511422786081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1185773585225674281857387 1778660377838511422786081)
    ·
      refine ⟨1333995283378883567089561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1778660377838511422786081 1333995283378883567089561)
      ·
        refine ⟨1000496462534162675317171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333995283378883567089561 1000496462534162675317171)
        ·
          refine ⟨1500744693801244012975757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000496462534162675317171 1500744693801244012975757)
          ·
            refine ⟨562779260175466504865909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500744693801244012975757 562779260175466504865909)
            ·
              refine ⟨52760555641449984831179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 562779260175466504865909 52760555641449984831179)
              ·
                refine ⟨79140833462174977246769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52760555641449984831179 79140833462174977246769)
                ·
                  refine ⟨59355625096631232935077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79140833462174977246769 59355625096631232935077)
                  ·
                    refine ⟨11129179705618356175327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59355625096631232935077 11129179705618356175327)
                    ·
                      rfl

theorem cell22_32511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_32511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32511 prefixEnd_32511 := by exact prefixLift 32511
  have htrace : WordTrace (prefixWord ++ tailWord_32511) baseStart_32511 baseEnd_32511 := by
    simpa [prefixWord, tailWord_32511, baseEnd_32511] using wordTrace_append hprefix tailTrace_32511
  have hstable : (prefixWord ++ tailWord_32511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32511).length < 2 ^ (prefixWord ++ tailWord_32511).sum := by decide
  have hdescent : baseEnd_32511 < baseStart_32511 := by decide
  rcases family_descends (prefixWord ++ tailWord_32511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32530 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_32530 : Nat := 118140960795 + 32530 * 2 ^ 59
def prefixEnd_32530 : Nat := 4983230072969 + 3 ^ 40 * 32530 * 2
def baseEnd_32530 : Nat := 11135683793908639950269

theorem tailTrace_32530 : CollatzResearch.WordTrace tailWord_32530 prefixEnd_32530 11135683793908639950269 := by
  unfold tailWord_32530
  simp only [CollatzResearch.WordTrace]
  refine ⟨296616643039210131699761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 790977714771227017866029 296616643039210131699761)
  ·
    refine ⟨222462482279407598774821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296616643039210131699761 222462482279407598774821)
    ·
      refine ⟨41711715427388924770279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222462482279407598774821 41711715427388924770279)
      ·
        refine ⟨62567573141083387155419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41711715427388924770279 62567573141083387155419)
        ·
          refine ⟨93851359711625080733129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62567573141083387155419 93851359711625080733129)
          ·
            refine ⟨70388519783718810549847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93851359711625080733129 70388519783718810549847)
            ·
              refine ⟨105582779675578215824771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70388519783718810549847 105582779675578215824771)
              ·
                refine ⟨158374169513367323737157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105582779675578215824771 158374169513367323737157)
                ·
                  refine ⟨29695156783756373200717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158374169513367323737157 29695156783756373200717)
                  ·
                    refine ⟨11135683793908639950269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29695156783756373200717 11135683793908639950269)
                    ·
                      rfl

theorem cell22_32530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_32530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32530 prefixEnd_32530 := by exact prefixLift 32530
  have htrace : WordTrace (prefixWord ++ tailWord_32530) baseStart_32530 baseEnd_32530 := by
    simpa [prefixWord, tailWord_32530, baseEnd_32530] using wordTrace_append hprefix tailTrace_32530
  have hstable : (prefixWord ++ tailWord_32530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32530).length < 2 ^ (prefixWord ++ tailWord_32530).sum := by decide
  have hdescent : baseEnd_32530 < baseStart_32530 := by decide
  rcases family_descends (prefixWord ++ tailWord_32530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32532 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 6]
def baseStart_32532 : Nat := 118140960795 + 32532 * 2 ^ 59
def prefixEnd_32532 : Nat := 4983230072969 + 3 ^ 40 * 32532 * 2
def baseEnd_32532 : Nat := 3712122811593767133421

theorem tailTrace_32532 : CollatzResearch.WordTrace tailWord_32532 prefixEnd_32532 3712122811593767133421 := by
  unfold tailWord_32532
  simp only [CollatzResearch.WordTrace]
  refine ⟨593269759074797434185925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 791026345433063245581233 593269759074797434185925)
  ·
    refine ⟨111238079826524518909861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 593269759074797434185925 111238079826524518909861)
    ·
      refine ⟨20857139967473347295599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111238079826524518909861 20857139967473347295599)
      ·
        refine ⟨31285709951210020943399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20857139967473347295599 31285709951210020943399)
        ·
          refine ⟨46928564926815031415099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31285709951210020943399 46928564926815031415099)
          ·
            refine ⟨70392847390222547122649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46928564926815031415099 70392847390222547122649)
            ·
              refine ⟨52794635542666910341987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70392847390222547122649 52794635542666910341987)
              ·
                refine ⟨79191953314000365512981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52794635542666910341987 79191953314000365512981)
                ·
                  refine ⟨3712122811593767133421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79191953314000365512981 3712122811593767133421)
                  ·
                    rfl

theorem cell22_32532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_32532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32532 prefixEnd_32532 := by exact prefixLift 32532
  have htrace : WordTrace (prefixWord ++ tailWord_32532) baseStart_32532 baseEnd_32532 := by
    simpa [prefixWord, tailWord_32532, baseEnd_32532] using wordTrace_append hprefix tailTrace_32532
  have hstable : (prefixWord ++ tailWord_32532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32532).length < 2 ^ (prefixWord ++ tailWord_32532).sum := by decide
  have hdescent : baseEnd_32532 < baseStart_32532 := by decide
  rcases family_descends (prefixWord ++ tailWord_32532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32601 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_32601 : Nat := 118140960795 + 32601 * 2 ^ 59
def prefixEnd_32601 : Nat := 4983230072969 + 3 ^ 40 * 32601 * 2
def baseEnd_32601 : Nat := 11159988544888121425051

theorem tailTrace_32601 : CollatzResearch.WordTrace tailWord_32601 prefixEnd_32601 11159988544888121425051 := by
  unfold tailWord_32601
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189056154899619652633657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 792704103266413101755771 1189056154899619652633657)
  ·
    refine ⟨891792116174714739475243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1189056154899619652633657 891792116174714739475243)
    ·
      refine ⟨1337688174262072109212865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891792116174714739475243 1337688174262072109212865)
      ·
        refine ⟨1003266130696554081909649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337688174262072109212865 1003266130696554081909649)
        ·
          refine ⟨752449598022415561432237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003266130696554081909649 752449598022415561432237)
          ·
            refine ⟨282168599258405835537089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752449598022415561432237 282168599258405835537089)
            ·
              refine ⟨211626449443804376652817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282168599258405835537089 211626449443804376652817)
              ·
                refine ⟨158719837082853282489613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211626449443804376652817 158719837082853282489613)
                ·
                  refine ⟨59519938906069980933605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158719837082853282489613 59519938906069980933605)
                  ·
                    refine ⟨11159988544888121425051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59519938906069980933605 11159988544888121425051)
                    ·
                      rfl

theorem cell22_32601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_32601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32601 prefixEnd_32601 := by exact prefixLift 32601
  have htrace : WordTrace (prefixWord ++ tailWord_32601) baseStart_32601 baseEnd_32601 := by
    simpa [prefixWord, tailWord_32601, baseEnd_32601] using wordTrace_append hprefix tailTrace_32601
  have hstable : (prefixWord ++ tailWord_32601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32601).length < 2 ^ (prefixWord ++ tailWord_32601).sum := by decide
  have hdescent : baseEnd_32601 < baseStart_32601 := by decide
  rcases family_descends (prefixWord ++ tailWord_32601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32616 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_32616 : Nat := 118140960795 + 32616 * 2 ^ 59
def prefixEnd_32616 : Nat := 4983230072969 + 3 ^ 40 * 32616 * 2
def baseEnd_32616 : Nat := 3721707783811027433335

theorem tailTrace_32616 : CollatzResearch.WordTrace tailWord_32616 prefixEnd_32616 3721707783811027433335 := by
  unfold tailWord_32616
  simp only [CollatzResearch.WordTrace]
  refine ⟨594801624922638607214851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 793068833230184809619801 594801624922638607214851)
  ·
    refine ⟨892202437383957910822277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 594801624922638607214851 892202437383957910822277)
    ·
      refine ⟨167287957009492108279177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 892202437383957910822277 167287957009492108279177)
      ·
        refine ⟨125465967757119081209383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167287957009492108279177 125465967757119081209383)
        ·
          refine ⟨188198951635678621814075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125465967757119081209383 188198951635678621814075)
          ·
            refine ⟨282298427453517932721113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188198951635678621814075 282298427453517932721113)
            ·
              refine ⟨211723820590138449540835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282298427453517932721113 211723820590138449540835)
              ·
                refine ⟨317585730885207674311253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211723820590138449540835 317585730885207674311253)
                ·
                  refine ⟨3721707783811027433335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 317585730885207674311253 3721707783811027433335)
                  ·
                    rfl

theorem cell22_32616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_32616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32616 prefixEnd_32616 := by exact prefixLift 32616
  have htrace : WordTrace (prefixWord ++ tailWord_32616) baseStart_32616 baseEnd_32616 := by
    simpa [prefixWord, tailWord_32616, baseEnd_32616] using wordTrace_append hprefix tailTrace_32616
  have hstable : (prefixWord ++ tailWord_32616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32616).length < 2 ^ (prefixWord ++ tailWord_32616).sum := by decide
  have hdescent : baseEnd_32616 < baseStart_32616 := by decide
  rcases family_descends (prefixWord ++ tailWord_32616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32633 : List Nat := [1, 2, 1, 3, 2, 2, 2, 5, 4]
def baseStart_32633 : Nat := 118140960795 + 32633 * 2 ^ 59
def prefixEnd_32633 : Nat := 4983230072969 + 3 ^ 40 * 32633 * 2
def baseEnd_32633 : Nat := 3723647599616901541651

theorem tailTrace_32633 : CollatzResearch.WordTrace tailWord_32633 prefixEnd_32633 3723647599616901541651 := by
  unfold tailWord_32633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190223290783689117798553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 793482193855792745199035 1190223290783689117798553)
  ·
    refine ⟨892667468087766838348915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1190223290783689117798553 892667468087766838348915)
    ·
      refine ⟨1339001202131650257523373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892667468087766838348915 1339001202131650257523373)
      ·
        refine ⟨502125450799368846571265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1339001202131650257523373 502125450799368846571265)
        ·
          refine ⟨376594088099526634928449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502125450799368846571265 376594088099526634928449)
          ·
            refine ⟨282445566074644976196337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376594088099526634928449 282445566074644976196337)
            ·
              refine ⟨211834174555983732147253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282445566074644976196337 211834174555983732147253)
              ·
                refine ⟨19859453864623474888805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211834174555983732147253 19859453864623474888805)
                ·
                  refine ⟨3723647599616901541651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19859453864623474888805 3723647599616901541651)
                  ·
                    rfl

theorem cell22_32633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_32633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32633 prefixEnd_32633 := by exact prefixLift 32633
  have htrace : WordTrace (prefixWord ++ tailWord_32633) baseStart_32633 baseEnd_32633 := by
    simpa [prefixWord, tailWord_32633, baseEnd_32633] using wordTrace_append hprefix tailTrace_32633
  have hstable : (prefixWord ++ tailWord_32633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32633).length < 2 ^ (prefixWord ++ tailWord_32633).sum := by decide
  have hdescent : baseEnd_32633 < baseStart_32633 := by decide
  rcases family_descends (prefixWord ++ tailWord_32633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32721 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_32721 : Nat := 118140960795 + 32721 * 2 ^ 59
def prefixEnd_32721 : Nat := 4983230072969 + 3 ^ 40 * 32721 * 2
def baseEnd_32721 : Nat := 11201066997247808424683

theorem tailTrace_32721 : CollatzResearch.WordTrace tailWord_32721 prefixEnd_32721 11201066997247808424683 := by
  unfold tailWord_32721
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193432914464880147002017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 795621942976586764668011 1193432914464880147002017)
  ·
    refine ⟨895074685848660110251513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1193432914464880147002017 895074685848660110251513)
    ·
      refine ⟨671306014386495082688635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895074685848660110251513 671306014386495082688635)
      ·
        refine ⟨1006959021579742624032953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671306014386495082688635 1006959021579742624032953)
        ·
          refine ⟨755219266184806968024715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006959021579742624032953 755219266184806968024715)
          ·
            refine ⟨1132828899277210452037073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755219266184806968024715 1132828899277210452037073)
            ·
              refine ⟨849621674457907839027805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132828899277210452037073 849621674457907839027805)
              ·
                refine ⟨318608127921715439635427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 849621674457907839027805 318608127921715439635427)
                ·
                  refine ⟨477912191882573159453141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318608127921715439635427 477912191882573159453141)
                  ·
                    refine ⟨11201066997247808424683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 477912191882573159453141 11201066997247808424683)
                    ·
                      rfl

theorem cell22_32721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_32721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32721 prefixEnd_32721 := by exact prefixLift 32721
  have htrace : WordTrace (prefixWord ++ tailWord_32721) baseStart_32721 baseEnd_32721 := by
    simpa [prefixWord, tailWord_32721, baseEnd_32721] using wordTrace_append hprefix tailTrace_32721
  have hstable : (prefixWord ++ tailWord_32721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32721).length < 2 ^ (prefixWord ++ tailWord_32721).sum := by decide
  have hdescent : baseEnd_32721 < baseStart_32721 := by decide
  rcases family_descends (prefixWord ++ tailWord_32721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32736 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_32736 : Nat := 118140960795 + 32736 * 2 ^ 59
def prefixEnd_32736 : Nat := 4983230072969 + 3 ^ 40 * 32736 * 2
def baseEnd_32736 : Nat := 11206201803792769299637

theorem tailTrace_32736 : CollatzResearch.WordTrace tailWord_32736 prefixEnd_32736 11206201803792769299637 := by
  unfold tailWord_32736
  simp only [CollatzResearch.WordTrace]
  refine ⟨596990004705268854399031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 795986672940358472532041 596990004705268854399031)
  ·
    refine ⟨895485007057903281598547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596990004705268854399031 895485007057903281598547)
    ·
      refine ⟨1343227510586854922397821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895485007057903281598547 1343227510586854922397821)
      ·
        refine ⟨503710316470070595899183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1343227510586854922397821 503710316470070595899183)
        ·
          refine ⟨755565474705105893848775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503710316470070595899183 755565474705105893848775)
          ·
            refine ⟨1133348212057658840773163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755565474705105893848775 1133348212057658840773163)
            ·
              refine ⟨1700022318086488261159745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133348212057658840773163 1700022318086488261159745)
              ·
                refine ⟨1275016738564866195869809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700022318086488261159745 1275016738564866195869809)
                ·
                  refine ⟨956262553923649646902357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1275016738564866195869809 956262553923649646902357)
                  ·
                    refine ⟨11206201803792769299637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 956262553923649646902357 11206201803792769299637)
                    ·
                      rfl

theorem cell22_32736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_32736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32736 prefixEnd_32736 := by exact prefixLift 32736
  have htrace : WordTrace (prefixWord ++ tailWord_32736) baseStart_32736 baseEnd_32736 := by
    simpa [prefixWord, tailWord_32736, baseEnd_32736] using wordTrace_append hprefix tailTrace_32736
  have hstable : (prefixWord ++ tailWord_32736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32736).length < 2 ^ (prefixWord ++ tailWord_32736).sum := by decide
  have hdescent : baseEnd_32736 < baseStart_32736 := by decide
  rcases family_descends (prefixWord ++ tailWord_32736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32804 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_32804 : Nat := 118140960795 + 32804 * 2 ^ 59
def prefixEnd_32804 : Nat := 4983230072969 + 3 ^ 40 * 32804 * 2
def baseEnd_32804 : Nat := 11229479593463258599429

theorem tailTrace_32804 : CollatzResearch.WordTrace tailWord_32804 prefixEnd_32804 11229479593463258599429 := by
  unfold tailWord_32804
  simp only [CollatzResearch.WordTrace]
  refine ⟨598230086582092661136733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 797640115442790214848977 598230086582092661136733)
  ·
    refine ⟨224336282468284747926275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 598230086582092661136733 224336282468284747926275)
    ·
      refine ⟨336504423702427121889413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224336282468284747926275 336504423702427121889413)
      ·
        refine ⟨63094579444205085354265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336504423702427121889413 63094579444205085354265)
        ·
          refine ⟨47320934583153814015699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63094579444205085354265 47320934583153814015699)
          ·
            refine ⟨70981401874730721023549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47320934583153814015699 70981401874730721023549)
            ·
              refine ⟨26618025703024020383831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70981401874730721023549 26618025703024020383831)
              ·
                refine ⟨39927038554536030575747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26618025703024020383831 39927038554536030575747)
                ·
                  refine ⟨59890557831804045863621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39927038554536030575747 59890557831804045863621)
                  ·
                    refine ⟨11229479593463258599429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59890557831804045863621 11229479593463258599429)
                    ·
                      rfl

theorem cell22_32804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_32804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32804 prefixEnd_32804 := by exact prefixLift 32804
  have htrace : WordTrace (prefixWord ++ tailWord_32804) baseStart_32804 baseEnd_32804 := by
    simpa [prefixWord, tailWord_32804, baseEnd_32804] using wordTrace_append hprefix tailTrace_32804
  have hstable : (prefixWord ++ tailWord_32804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32804).length < 2 ^ (prefixWord ++ tailWord_32804).sum := by decide
  have hdescent : baseEnd_32804 < baseStart_32804 := by decide
  rcases family_descends (prefixWord ++ tailWord_32804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32817 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_32817 : Nat := 118140960795 + 32817 * 2 ^ 59
def prefixEnd_32817 : Nat := 4983230072969 + 3 ^ 40 * 32817 * 2
def baseEnd_32817 : Nat := 11233929759135558024389

theorem tailTrace_32817 : CollatzResearch.WordTrace tailWord_32817 prefixEnd_32817 11233929759135558024389 := by
  unfold tailWord_32817
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196934322117088542496705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 797956214744725694997803 1196934322117088542496705)
  ·
    refine ⟨897700741587816406872529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1196934322117088542496705 897700741587816406872529)
    ·
      refine ⟨673275556190862305154397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 897700741587816406872529 673275556190862305154397)
      ·
        refine ⟨252478333571573364432899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673275556190862305154397 252478333571573364432899)
        ·
          refine ⟨378717500357360046649349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252478333571573364432899 378717500357360046649349)
          ·
            refine ⟨71009531317005008746753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378717500357360046649349 71009531317005008746753)
            ·
              refine ⟨53257148487753756560065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71009531317005008746753 53257148487753756560065)
              ·
                refine ⟨39942861365815317420049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53257148487753756560065 39942861365815317420049)
                ·
                  refine ⟨29957146024361488065037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39942861365815317420049 29957146024361488065037)
                  ·
                    refine ⟨11233929759135558024389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29957146024361488065037 11233929759135558024389)
                    ·
                      rfl

theorem cell22_32817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_32817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32817 prefixEnd_32817 := by exact prefixLift 32817
  have htrace : WordTrace (prefixWord ++ tailWord_32817) baseStart_32817 baseEnd_32817 := by
    simpa [prefixWord, tailWord_32817, baseEnd_32817] using wordTrace_append hprefix tailTrace_32817
  have hstable : (prefixWord ++ tailWord_32817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32817).length < 2 ^ (prefixWord ++ tailWord_32817).sum := by decide
  have hdescent : baseEnd_32817 < baseStart_32817 := by decide
  rcases family_descends (prefixWord ++ tailWord_32817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32858 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_32858 : Nat := 118140960795 + 32858 * 2 ^ 59
def prefixEnd_32858 : Nat := 4983230072969 + 3 ^ 40 * 32858 * 2
def baseEnd_32858 : Nat := 3749321632341705916421

theorem tailTrace_32858 : CollatzResearch.WordTrace tailWord_32858 prefixEnd_32858 3749321632341705916421 := by
  unfold tailWord_32858
  simp only [CollatzResearch.WordTrace]
  refine ⟨299607428742138136184807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 798953143312368363159485 299607428742138136184807)
  ·
    refine ⟨449411143113207204277211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299607428742138136184807 449411143113207204277211)
    ·
      refine ⟨674116714669810806415817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449411143113207204277211 674116714669810806415817)
      ·
        refine ⟨505587536002358104811863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674116714669810806415817 505587536002358104811863)
        ·
          refine ⟨758381304003537157217795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505587536002358104811863 758381304003537157217795)
          ·
            refine ⟨1137571956005305735826693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758381304003537157217795 1137571956005305735826693)
            ·
              refine ⟨213294741750994825467505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1137571956005305735826693 213294741750994825467505)
              ·
                refine ⟨159971056313246119100629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213294741750994825467505 159971056313246119100629)
                ·
                  refine ⟨3749321632341705916421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 159971056313246119100629 3749321632341705916421)
                  ·
                    rfl

theorem cell22_32858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_32858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32858 prefixEnd_32858 := by exact prefixLift 32858
  have htrace : WordTrace (prefixWord ++ tailWord_32858) baseStart_32858 baseEnd_32858 := by
    simpa [prefixWord, tailWord_32858, baseEnd_32858] using wordTrace_append hprefix tailTrace_32858
  have hstable : (prefixWord ++ tailWord_32858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32858).length < 2 ^ (prefixWord ++ tailWord_32858).sum := by decide
  have hdescent : baseEnd_32858 < baseStart_32858 := by decide
  rcases family_descends (prefixWord ++ tailWord_32858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32873 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_32873 : Nat := 118140960795 + 32873 * 2 ^ 59
def prefixEnd_32873 : Nat := 4983230072969 + 3 ^ 40 * 32873 * 2
def baseEnd_32873 : Nat := 11253099703570078624217

theorem tailTrace_32873 : CollatzResearch.WordTrace tailWord_32873 prefixEnd_32873 11253099703570078624217 := by
  unfold tailWord_32873
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198976809914210106535273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 799317873276140071023515 1198976809914210106535273)
  ·
    refine ⟨899232607435657579901455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1198976809914210106535273 899232607435657579901455)
    ·
      refine ⟨1348848911153486369852183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899232607435657579901455 1348848911153486369852183)
      ·
        refine ⟨2023273366730229554778275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348848911153486369852183 2023273366730229554778275)
        ·
          refine ⟨3034910050095344332167413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023273366730229554778275 3034910050095344332167413)
          ·
            refine ⟨284522817196438531140695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3034910050095344332167413 284522817196438531140695)
            ·
              refine ⟨426784225794657796711043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284522817196438531140695 426784225794657796711043)
              ·
                refine ⟨640176338691986695066565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426784225794657796711043 640176338691986695066565)
                ·
                  refine ⟨120033063504747505324981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640176338691986695066565 120033063504747505324981)
                  ·
                    refine ⟨11253099703570078624217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120033063504747505324981 11253099703570078624217)
                    ·
                      rfl

theorem cell22_32873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_32873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32873 prefixEnd_32873 := by exact prefixLift 32873
  have htrace : WordTrace (prefixWord ++ tailWord_32873) baseStart_32873 baseEnd_32873 := by
    simpa [prefixWord, tailWord_32873, baseEnd_32873] using wordTrace_append hprefix tailTrace_32873
  have hstable : (prefixWord ++ tailWord_32873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32873).length < 2 ^ (prefixWord ++ tailWord_32873).sum := by decide
  have hdescent : baseEnd_32873 < baseStart_32873 := by decide
  rcases family_descends (prefixWord ++ tailWord_32873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32892 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 5]
def baseStart_32892 : Nat := 118140960795 + 32892 * 2 ^ 59
def prefixEnd_32892 : Nat := 4983230072969 + 3 ^ 40 * 32892 * 2
def baseEnd_32892 : Nat := 3753201263953454133053

theorem tailTrace_32892 : CollatzResearch.WordTrace tailWord_32892 prefixEnd_32892 3753201263953454133053 := by
  unfold tailWord_32892
  simp only [CollatzResearch.WordTrace]
  refine ⟨599834898422688175738465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 799779864563584234317953 599834898422688175738465)
  ·
    refine ⟨449876173817016131803849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 599834898422688175738465 449876173817016131803849)
    ·
      refine ⟨337407130362762098852887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449876173817016131803849 337407130362762098852887)
      ·
        refine ⟨506110695544143148279331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337407130362762098852887 506110695544143148279331)
        ·
          refine ⟨759166043316214722418997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506110695544143148279331 759166043316214722418997)
          ·
            refine ⟨71171816560895130226781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 759166043316214722418997 71171816560895130226781)
            ·
              refine ⟨26689431210335673835043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71171816560895130226781 26689431210335673835043)
              ·
                refine ⟨40034146815503510752565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26689431210335673835043 40034146815503510752565)
                ·
                  refine ⟨3753201263953454133053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40034146815503510752565 3753201263953454133053)
                  ·
                    rfl

theorem cell22_32892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_32892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32892 prefixEnd_32892 := by exact prefixLift 32892
  have htrace : WordTrace (prefixWord ++ tailWord_32892) baseStart_32892 baseEnd_32892 := by
    simpa [prefixWord, tailWord_32892, baseEnd_32892] using wordTrace_append hprefix tailTrace_32892
  have hstable : (prefixWord ++ tailWord_32892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32892).length < 2 ^ (prefixWord ++ tailWord_32892).sum := by decide
  have hdescent : baseEnd_32892 < baseStart_32892 := by decide
  rcases family_descends (prefixWord ++ tailWord_32892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32952 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_32952 : Nat := 118140960795 + 32952 * 2 ^ 59
def prefixEnd_32952 : Nat := 4983230072969 + 3 ^ 40 * 32952 * 2
def baseEnd_32952 : Nat := 11280143018040205898975

theorem tailTrace_32952 : CollatzResearch.WordTrace tailWord_32952 prefixEnd_32952 11280143018040205898975 := by
  unfold tailWord_32952
  simp only [CollatzResearch.WordTrace]
  refine ⟨600929088314003299330555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 801238784418671065774073 600929088314003299330555)
  ·
    refine ⟨901393632471004948995833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 600929088314003299330555 901393632471004948995833)
    ·
      refine ⟨676045224353253711746875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 901393632471004948995833 676045224353253711746875)
      ·
        refine ⟨1014067836529880567620313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676045224353253711746875 1014067836529880567620313)
        ·
          refine ⟨760550877397410425715235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014067836529880567620313 760550877397410425715235)
          ·
            refine ⟨1140826316096115638572853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760550877397410425715235 1140826316096115638572853)
            ·
              refine ⟨106952467134010841116205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1140826316096115638572853 106952467134010841116205)
              ·
                refine ⟨40107175175254065418577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106952467134010841116205 40107175175254065418577)
                ·
                  refine ⟨30080381381440549063933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40107175175254065418577 30080381381440549063933)
                  ·
                    refine ⟨11280143018040205898975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30080381381440549063933 11280143018040205898975)
                    ·
                      rfl

theorem cell22_32952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_32952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32952 prefixEnd_32952 := by exact prefixLift 32952
  have htrace : WordTrace (prefixWord ++ tailWord_32952) baseStart_32952 baseEnd_32952 := by
    simpa [prefixWord, tailWord_32952, baseEnd_32952] using wordTrace_append hprefix tailTrace_32952
  have hstable : (prefixWord ++ tailWord_32952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32952).length < 2 ^ (prefixWord ++ tailWord_32952).sum := by decide
  have hdescent : baseEnd_32952 < baseStart_32952 := by decide
  rcases family_descends (prefixWord ++ tailWord_32952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32956 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_32956 : Nat := 118140960795 + 32956 * 2 ^ 59
def prefixEnd_32956 : Nat := 4983230072969 + 3 ^ 40 * 32956 * 2
def baseEnd_32956 : Nat := 11281512299785528798963

theorem tailTrace_32956 : CollatzResearch.WordTrace tailWord_32956 prefixEnd_32956 11281512299785528798963 := by
  unfold tailWord_32956
  simp only [CollatzResearch.WordTrace]
  refine ⟨601002034306757640903361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 801336045742343521204481 601002034306757640903361)
  ·
    refine ⟨450751525730068230677521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 601002034306757640903361 450751525730068230677521)
    ·
      refine ⟨338063644297551173008141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450751525730068230677521 338063644297551173008141)
      ·
        refine ⟨126773866611581689878053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338063644297551173008141 126773866611581689878053)
        ·
          refine ⟨23770099989671566852135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126773866611581689878053 23770099989671566852135)
          ·
            refine ⟨35655149984507350278203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23770099989671566852135 35655149984507350278203)
            ·
              refine ⟨53482724976761025417305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35655149984507350278203 53482724976761025417305)
              ·
                refine ⟨40112043732570769062979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53482724976761025417305 40112043732570769062979)
                ·
                  refine ⟨60168065598856153594469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40112043732570769062979 60168065598856153594469)
                  ·
                    refine ⟨11281512299785528798963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60168065598856153594469 11281512299785528798963)
                    ·
                      rfl

theorem cell22_32956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_32956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32956 prefixEnd_32956 := by exact prefixLift 32956
  have htrace : WordTrace (prefixWord ++ tailWord_32956) baseStart_32956 baseEnd_32956 := by
    simpa [prefixWord, tailWord_32956, baseEnd_32956] using wordTrace_append hprefix tailTrace_32956
  have hstable : (prefixWord ++ tailWord_32956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32956).length < 2 ^ (prefixWord ++ tailWord_32956).sum := by decide
  have hdescent : baseEnd_32956 < baseStart_32956 := by decide
  rcases family_descends (prefixWord ++ tailWord_32956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32982 : List Nat := [5, 2, 1, 2, 1, 11]
def baseStart_32982 : Nat := 118140960795 + 32982 * 2 ^ 59
def prefixEnd_32982 : Nat := 4983230072969 + 3 ^ 40 * 32982 * 2
def baseEnd_32982 : Nat := 139387810260865773443

theorem tailTrace_32982 : CollatzResearch.WordTrace tailWord_32982 prefixEnd_32982 139387810260865773443 := by
  unfold tailWord_32982
  simp only [CollatzResearch.WordTrace]
  refine ⟨75184522907457607640825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 801968244346214481502133 75184522907457607640825)
  ·
    refine ⟨56388392180593205730619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75184522907457607640825 56388392180593205730619)
    ·
      refine ⟨84582588270889808595929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56388392180593205730619 84582588270889808595929)
      ·
        refine ⟨63436941203167356446947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84582588270889808595929 63436941203167356446947)
        ·
          refine ⟨95155411804751034670421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63436941203167356446947 95155411804751034670421)
          ·
            refine ⟨139387810260865773443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 95155411804751034670421 139387810260865773443)
            ·
              rfl

theorem cell22_32982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 11].length) (baseStart_32982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_32982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_32982 prefixEnd_32982 := by exact prefixLift 32982
  have htrace : WordTrace (prefixWord ++ tailWord_32982) baseStart_32982 baseEnd_32982 := by
    simpa [prefixWord, tailWord_32982, baseEnd_32982] using wordTrace_append hprefix tailTrace_32982
  have hstable : (prefixWord ++ tailWord_32982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32982).length < 2 ^ (prefixWord ++ tailWord_32982).sum := by decide
  have hdescent : baseEnd_32982 < baseStart_32982 := by decide
  rcases family_descends (prefixWord ++ tailWord_32982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33025 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_33025 : Nat := 118140960795 + 33025 * 2 ^ 59
def prefixEnd_33025 : Nat := 4983230072969 + 3 ^ 40 * 33025 * 2
def baseEnd_33025 : Nat := 11305132409892348823751

theorem tailTrace_33025 : CollatzResearch.WordTrace tailWord_33025 prefixEnd_33025 11305132409892348823751 := by
  unfold tailWord_33025
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204520705363540066068529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 803013803575693377379019 1204520705363540066068529)
  ·
    refine ⟨903390529022655049551397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1204520705363540066068529 903390529022655049551397)
    ·
      refine ⟨169385724191747821790887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 903390529022655049551397 169385724191747821790887)
      ·
        refine ⟨254078586287621732686331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169385724191747821790887 254078586287621732686331)
        ·
          refine ⟨381117879431432599029497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254078586287621732686331 381117879431432599029497)
          ·
            refine ⟨285838409573574449272123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381117879431432599029497 285838409573574449272123)
            ·
              refine ⟨428757614360361673908185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285838409573574449272123 428757614360361673908185)
              ·
                refine ⟨321568210770271255431139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428757614360361673908185 321568210770271255431139)
                ·
                  refine ⟨482352316155406883146709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321568210770271255431139 482352316155406883146709)
                  ·
                    refine ⟨11305132409892348823751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 482352316155406883146709 11305132409892348823751)
                    ·
                      rfl

theorem cell22_33025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_33025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33025 prefixEnd_33025 := by exact prefixLift 33025
  have htrace : WordTrace (prefixWord ++ tailWord_33025) baseStart_33025 baseEnd_33025 := by
    simpa [prefixWord, tailWord_33025, baseEnd_33025] using wordTrace_append hprefix tailTrace_33025
  have hstable : (prefixWord ++ tailWord_33025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33025).length < 2 ^ (prefixWord ++ tailWord_33025).sum := by decide
  have hdescent : baseEnd_33025 < baseStart_33025 := by decide
  rcases family_descends (prefixWord ++ tailWord_33025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33087 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 6, 3]
def baseStart_33087 : Nat := 118140960795 + 33087 * 2 ^ 59
def prefixEnd_33087 : Nat := 4983230072969 + 3 ^ 40 * 33087 * 2
def baseEnd_33087 : Nat := 11326356276944853773561

theorem tailTrace_33087 : CollatzResearch.WordTrace tailWord_33087 prefixEnd_33087 11326356276944853773561 := by
  unfold tailWord_33087
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206782031138924654825515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 804521354092616436550343 1206782031138924654825515)
  ·
    refine ⟨1810173046708386982238273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1206782031138924654825515 1810173046708386982238273)
    ·
      refine ⟨1357629785031290236678705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1810173046708386982238273 1357629785031290236678705)
      ·
        refine ⟨1018222338773467677509029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1357629785031290236678705 1018222338773467677509029)
        ·
          refine ⟨190916688520025189532943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1018222338773467677509029 190916688520025189532943)
          ·
            refine ⟨286375032780037784299415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190916688520025189532943 286375032780037784299415)
            ·
              refine ⟨429562549170056676449123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286375032780037784299415 429562549170056676449123)
              ·
                refine ⟨644343823755085014673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429562549170056676449123 644343823755085014673685)
                ·
                  refine ⟨30203616738519610062829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 644343823755085014673685 30203616738519610062829)
                  ·
                    refine ⟨11326356276944853773561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30203616738519610062829 11326356276944853773561)
                    ·
                      rfl

theorem cell22_33087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_33087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33087 prefixEnd_33087 := by exact prefixLift 33087
  have htrace : WordTrace (prefixWord ++ tailWord_33087) baseStart_33087 baseEnd_33087 := by
    simpa [prefixWord, tailWord_33087, baseEnd_33087] using wordTrace_append hprefix tailTrace_33087
  have hstable : (prefixWord ++ tailWord_33087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33087).length < 2 ^ (prefixWord ++ tailWord_33087).sum := by decide
  have hdescent : baseEnd_33087 < baseStart_33087 := by decide
  rcases family_descends (prefixWord ++ tailWord_33087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33177 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_33177 : Nat := 118140960795 + 33177 * 2 ^ 59
def prefixEnd_33177 : Nat := 4983230072969 + 3 ^ 40 * 33177 * 2
def baseEnd_33177 : Nat := 11357165116214619023285

theorem tailTrace_33177 : CollatzResearch.WordTrace tailWord_33177 prefixEnd_33177 11357165116214619023285 := by
  unfold tailWord_33177
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210064600812870025601785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 806709733875246683734523 1210064600812870025601785)
  ·
    refine ⟨907548450609652519201339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1210064600812870025601785 907548450609652519201339)
    ·
      refine ⟨1361322675914478778802009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907548450609652519201339 1361322675914478778802009)
      ·
        refine ⟨1020992006935859084101507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1361322675914478778802009 1020992006935859084101507)
        ·
          refine ⟨1531488010403788626152261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020992006935859084101507 1531488010403788626152261)
          ·
            refine ⟨287154001950710367403549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1531488010403788626152261 287154001950710367403549)
            ·
              refine ⟨107682750731516387776331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287154001950710367403549 107682750731516387776331)
              ·
                refine ⟨161524126097274581664497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107682750731516387776331 161524126097274581664497)
                ·
                  refine ⟨121143094572955936248373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161524126097274581664497 121143094572955936248373)
                  ·
                    refine ⟨11357165116214619023285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121143094572955936248373 11357165116214619023285)
                    ·
                      rfl

theorem cell22_33177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_33177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33177 prefixEnd_33177 := by exact prefixLift 33177
  have htrace : WordTrace (prefixWord ++ tailWord_33177) baseStart_33177 baseEnd_33177 := by
    simpa [prefixWord, tailWord_33177, baseEnd_33177] using wordTrace_append hprefix tailTrace_33177
  have hstable : (prefixWord ++ tailWord_33177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33177).length < 2 ^ (prefixWord ++ tailWord_33177).sum := by decide
  have hdescent : baseEnd_33177 < baseStart_33177 := by decide
  rcases family_descends (prefixWord ++ tailWord_33177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33224 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_33224 : Nat := 118140960795 + 33224 * 2 ^ 59
def prefixEnd_33224 : Nat := 4983230072969 + 3 ^ 40 * 33224 * 2
def baseEnd_33224 : Nat := 3791084725574054366047

theorem tailTrace_33224 : CollatzResearch.WordTrace tailWord_33224 prefixEnd_33224 3791084725574054366047 := by
  unfold tailWord_33224
  simp only [CollatzResearch.WordTrace]
  refine ⟨605889415821298526281363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 807852554428398035041817 605889415821298526281363)
  ·
    refine ⟨908834123731947789422045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 605889415821298526281363 908834123731947789422045)
    ·
      refine ⟨340812796399480421033267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 908834123731947789422045 340812796399480421033267)
      ·
        refine ⟨511219194599220631549901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340812796399480421033267 511219194599220631549901)
        ·
          refine ⟨191707197974707736831213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511219194599220631549901 191707197974707736831213)
          ·
            refine ⟨71890199240515401311705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191707197974707736831213 71890199240515401311705)
            ·
              refine ⟨53917649430386550983779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71890199240515401311705 53917649430386550983779)
              ·
                refine ⟨80876474145579826475669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53917649430386550983779 80876474145579826475669)
                ·
                  refine ⟨3791084725574054366047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80876474145579826475669 3791084725574054366047)
                  ·
                    rfl

theorem cell22_33224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_33224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33224 prefixEnd_33224 := by exact prefixLift 33224
  have htrace : WordTrace (prefixWord ++ tailWord_33224) baseStart_33224 baseEnd_33224 := by
    simpa [prefixWord, tailWord_33224, baseEnd_33224] using wordTrace_append hprefix tailTrace_33224
  have hstable : (prefixWord ++ tailWord_33224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33224).length < 2 ^ (prefixWord ++ tailWord_33224).sum := by decide
  have hdescent : baseEnd_33224 < baseStart_33224 := by decide
  rcases family_descends (prefixWord ++ tailWord_33224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33258 : List Nat := [3, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_33258 : Nat := 118140960795 + 33258 * 2 ^ 59
def prefixEnd_33258 : Nat := 4983230072969 + 3 ^ 40 * 33258 * 2
def baseEnd_33258 : Nat := 3794964357185802582679

theorem tailTrace_33258 : CollatzResearch.WordTrace tailWord_33258 prefixEnd_33258 3794964357185802582679 := by
  unfold tailWord_33258
  simp only [CollatzResearch.WordTrace]
  refine ⟨303254728379855214825107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 808679275679613906200285 303254728379855214825107)
  ·
    refine ⟨454882092569782822237661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303254728379855214825107 454882092569782822237661)
    ·
      refine ⟨170580784713668558339123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454882092569782822237661 170580784713668558339123)
      ·
        refine ⟨255871177070502837508685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170580784713668558339123 255871177070502837508685)
        ·
          refine ⟨95951691401438564065757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255871177070502837508685 95951691401438564065757)
          ·
            refine ⟨35981884275539461524659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95951691401438564065757 35981884275539461524659)
            ·
              refine ⟨53972826413309192286989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35981884275539461524659 53972826413309192286989)
              ·
                refine ⟨20239809904990947107621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53972826413309192286989 20239809904990947107621)
                ·
                  refine ⟨3794964357185802582679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20239809904990947107621 3794964357185802582679)
                  ·
                    rfl

theorem cell22_33258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_33258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33258 prefixEnd_33258 := by exact prefixLift 33258
  have htrace : WordTrace (prefixWord ++ tailWord_33258) baseStart_33258 baseEnd_33258 := by
    simpa [prefixWord, tailWord_33258, baseEnd_33258] using wordTrace_append hprefix tailTrace_33258
  have hstable : (prefixWord ++ tailWord_33258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33258).length < 2 ^ (prefixWord ++ tailWord_33258).sum := by decide
  have hdescent : baseEnd_33258 < baseStart_33258 := by decide
  rcases family_descends (prefixWord ++ tailWord_33258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33297 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 9]
def baseStart_33297 : Nat := 118140960795 + 33297 * 2 ^ 59
def prefixEnd_33297 : Nat := 4983230072969 + 3 ^ 40 * 33297 * 2
def baseEnd_33297 : Nat := 3799414522858102007639

theorem tailTrace_33297 : CollatzResearch.WordTrace tailWord_33297 prefixEnd_33297 3799414522858102007639 := by
  unfold tailWord_33297
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214441360378130519970145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 809627573585420346646763 1214441360378130519970145)
  ·
    refine ⟨910831020283597889977609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1214441360378130519970145 910831020283597889977609)
    ·
      refine ⟨683123265212698417483207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 910831020283597889977609 683123265212698417483207)
      ·
        refine ⟨1024684897819047626224811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683123265212698417483207 1024684897819047626224811)
        ·
          refine ⟨1537027346728571439337217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024684897819047626224811 1537027346728571439337217)
          ·
            refine ⟨1152770510046428579502913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1537027346728571439337217 1152770510046428579502913)
            ·
              refine ⟨864577882534821434627185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152770510046428579502913 864577882534821434627185)
              ·
                refine ⟨648433411901116075970389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864577882534821434627185 648433411901116075970389)
                ·
                  refine ⟨3799414522858102007639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 648433411901116075970389 3799414522858102007639)
                  ·
                    rfl

theorem cell22_33297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_33297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33297 prefixEnd_33297 := by exact prefixLift 33297
  have htrace : WordTrace (prefixWord ++ tailWord_33297) baseStart_33297 baseEnd_33297 := by
    simpa [prefixWord, tailWord_33297, baseEnd_33297] using wordTrace_append hprefix tailTrace_33297
  have hstable : (prefixWord ++ tailWord_33297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33297).length < 2 ^ (prefixWord ++ tailWord_33297).sum := by decide
  have hdescent : baseEnd_33297 < baseStart_33297 := by decide
  rcases family_descends (prefixWord ++ tailWord_33297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33344 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_33344 : Nat := 118140960795 + 33344 * 2 ^ 59
def prefixEnd_33344 : Nat := 4983230072969 + 3 ^ 40 * 33344 * 2
def baseEnd_33344 : Nat := 11414332629081850097773

theorem tailTrace_33344 : CollatzResearch.WordTrace tailWord_33344 prefixEnd_33344 11414332629081850097773 := by
  unfold tailWord_33344
  simp only [CollatzResearch.WordTrace]
  refine ⟨608077795603928773465543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 810770394138571697954057 608077795603928773465543)
  ·
    refine ⟨912116693405893160198315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 608077795603928773465543 912116693405893160198315)
    ·
      refine ⟨1368175040108839740297473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 912116693405893160198315 1368175040108839740297473)
      ·
        refine ⟨1026131280081629805223105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1368175040108839740297473 1026131280081629805223105)
        ·
          refine ⟨769598460061222353917329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026131280081629805223105 769598460061222353917329)
          ·
            refine ⟨577198845045916765437997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769598460061222353917329 577198845045916765437997)
            ·
              refine ⟨216449566892218787039249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577198845045916765437997 216449566892218787039249)
              ·
                refine ⟨162337175169164090279437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216449566892218787039249 162337175169164090279437)
                ·
                  refine ⟨60876440688436533854789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162337175169164090279437 60876440688436533854789)
                  ·
                    refine ⟨11414332629081850097773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60876440688436533854789 11414332629081850097773)
                    ·
                      rfl

theorem cell22_33344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_33344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33344 prefixEnd_33344 := by exact prefixLift 33344
  have htrace : WordTrace (prefixWord ++ tailWord_33344) baseStart_33344 baseEnd_33344 := by
    simpa [prefixWord, tailWord_33344, baseEnd_33344] using wordTrace_append hprefix tailTrace_33344
  have hstable : (prefixWord ++ tailWord_33344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33344).length < 2 ^ (prefixWord ++ tailWord_33344).sum := by decide
  have hdescent : baseEnd_33344 < baseStart_33344 := by decide
  rcases family_descends (prefixWord ++ tailWord_33344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33376 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 4]
def baseStart_33376 : Nat := 118140960795 + 33376 * 2 ^ 59
def prefixEnd_33376 : Nat := 4983230072969 + 3 ^ 40 * 33376 * 2
def baseEnd_33376 : Nat := 3808428961014811099225

theorem tailTrace_33376 : CollatzResearch.WordTrace tailWord_33376 prefixEnd_33376 3808428961014811099225 := by
  unfold tailWord_33376
  simp only [CollatzResearch.WordTrace]
  refine ⟨608661363545963506047991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 811548484727951341397321 608661363545963506047991)
  ·
    refine ⟨912992045318945259071987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 608661363545963506047991 912992045318945259071987)
    ·
      refine ⟨1369488067978417888607981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 912992045318945259071987 1369488067978417888607981)
      ·
        refine ⟨513558025491906708227993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1369488067978417888607981 513558025491906708227993)
        ·
          refine ⟨385168519118930031170995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513558025491906708227993 385168519118930031170995)
          ·
            refine ⟨577752778678395046756493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385168519118930031170995 577752778678395046756493)
            ·
              refine ⟨216657292004398142533685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577752778678395046756493 216657292004398142533685)
              ·
                refine ⟨20311621125412325862533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216657292004398142533685 20311621125412325862533)
                ·
                  refine ⟨3808428961014811099225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20311621125412325862533 3808428961014811099225)
                  ·
                    rfl

theorem cell22_33376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_33376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33376 prefixEnd_33376 := by exact prefixLift 33376
  have htrace : WordTrace (prefixWord ++ tailWord_33376) baseStart_33376 baseEnd_33376 := by
    simpa [prefixWord, tailWord_33376, baseEnd_33376] using wordTrace_append hprefix tailTrace_33376
  have hstable : (prefixWord ++ tailWord_33376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33376).length < 2 ^ (prefixWord ++ tailWord_33376).sum := by decide
  have hdescent : baseEnd_33376 < baseStart_33376 := by decide
  rcases family_descends (prefixWord ++ tailWord_33376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33466 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_33466 : Nat := 118140960795 + 33466 * 2 ^ 59
def prefixEnd_33466 : Nat := 4983230072969 + 3 ^ 40 * 33466 * 2
def baseEnd_33466 : Nat := 3818698574104732849133

theorem tailTrace_33466 : CollatzResearch.WordTrace tailWord_33466 prefixEnd_33466 3818698574104732849133 := by
  unfold tailWord_33466
  simp only [CollatzResearch.WordTrace]
  refine ⟨305151324191468095718063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 813736864510581588581501 305151324191468095718063)
  ·
    refine ⟨457726986287202143577095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305151324191468095718063 457726986287202143577095)
    ·
      refine ⟨686590479430803215365643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457726986287202143577095 686590479430803215365643)
      ·
        refine ⟨1029885719146204823048465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686590479430803215365643 1029885719146204823048465)
        ·
          refine ⟨772414289359653617286349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1029885719146204823048465 772414289359653617286349)
          ·
            refine ⟨289655358509870106482381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772414289359653617286349 289655358509870106482381)
            ·
              refine ⟨108620759441201289930893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289655358509870106482381 108620759441201289930893)
              ·
                refine ⟨40732784790450483724085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108620759441201289930893 40732784790450483724085)
                ·
                  refine ⟨3818698574104732849133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40732784790450483724085 3818698574104732849133)
                  ·
                    rfl

theorem cell22_33466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_33466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33466 prefixEnd_33466 := by exact prefixLift 33466
  have htrace : WordTrace (prefixWord ++ tailWord_33466) baseStart_33466 baseEnd_33466 := by
    simpa [prefixWord, tailWord_33466, baseEnd_33466] using wordTrace_append hprefix tailTrace_33466
  have hstable : (prefixWord ++ tailWord_33466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33466).length < 2 ^ (prefixWord ++ tailWord_33466).sum := by decide
  have hdescent : baseEnd_33466 < baseStart_33466 := by decide
  rcases family_descends (prefixWord ++ tailWord_33466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33500 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_33500 : Nat := 118140960795 + 33500 * 2 ^ 59
def prefixEnd_33500 : Nat := 4983230072969 + 3 ^ 40 * 33500 * 2
def baseEnd_33500 : Nat := 3822578205716481065765

theorem tailTrace_33500 : CollatzResearch.WordTrace tailWord_33500 prefixEnd_33500 3822578205716481065765 := by
  unfold tailWord_33500
  simp only [CollatzResearch.WordTrace]
  refine ⟨610922689321348094804977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 814563585761797459739969 610922689321348094804977)
  ·
    refine ⟨458192016991011071103733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 610922689321348094804977 458192016991011071103733)
    ·
      refine ⟨42955501592907287915975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458192016991011071103733 42955501592907287915975)
      ·
        refine ⟨64433252389360931873963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42955501592907287915975 64433252389360931873963)
        ·
          refine ⟨96649878584041397810945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64433252389360931873963 96649878584041397810945)
          ·
            refine ⟨72487408938031048358209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96649878584041397810945 72487408938031048358209)
            ·
              refine ⟨54365556703523286268657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72487408938031048358209 54365556703523286268657)
              ·
                refine ⟨40774167527642464701493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54365556703523286268657 40774167527642464701493)
                ·
                  refine ⟨3822578205716481065765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40774167527642464701493 3822578205716481065765)
                  ·
                    rfl

theorem cell22_33500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_33500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33500 prefixEnd_33500 := by exact prefixLift 33500
  have htrace : WordTrace (prefixWord ++ tailWord_33500) baseStart_33500 baseEnd_33500 := by
    simpa [prefixWord, tailWord_33500, baseEnd_33500] using wordTrace_append hprefix tailTrace_33500
  have hstable : (prefixWord ++ tailWord_33500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33500).length < 2 ^ (prefixWord ++ tailWord_33500).sum := by decide
  have hdescent : baseEnd_33500 < baseStart_33500 := by decide
  rcases family_descends (prefixWord ++ tailWord_33500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33543 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 1, 5]
def baseStart_33543 : Nat := 118140960795 + 33543 * 2 ^ 59
def prefixEnd_33543 : Nat := 4983230072969 + 3 ^ 40 * 33543 * 2
def baseEnd_33543 : Nat := 11482454395911664372163

theorem tailTrace_33543 : CollatzResearch.WordTrace tailWord_33543 prefixEnd_33543 11482454395911664372163 := by
  unfold tailWord_33543
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223413717486914533425283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 815609144991276355616855 1223413717486914533425283)
  ·
    refine ⟨1835120576230371800137925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1223413717486914533425283 1835120576230371800137925)
    ·
      refine ⟨344085108043194712525861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1835120576230371800137925 344085108043194712525861)
      ·
        refine ⟨64515957758099008598599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 344085108043194712525861 64515957758099008598599)
        ·
          refine ⟨96773936637148512897899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64515957758099008598599 96773936637148512897899)
          ·
            refine ⟨145160904955722769346849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96773936637148512897899 145160904955722769346849)
            ·
              refine ⟨108870678716792077010137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145160904955722769346849 108870678716792077010137)
              ·
                refine ⟨81653009037594057757603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108870678716792077010137 81653009037594057757603)
                ·
                  refine ⟨122479513556391086636405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81653009037594057757603 122479513556391086636405)
                  ·
                    refine ⟨11482454395911664372163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122479513556391086636405 11482454395911664372163)
                    ·
                      rfl

theorem cell22_33543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_33543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33543 prefixEnd_33543 := by exact prefixLift 33543
  have htrace : WordTrace (prefixWord ++ tailWord_33543) baseStart_33543 baseEnd_33543 := by
    simpa [prefixWord, tailWord_33543, baseEnd_33543] using wordTrace_append hprefix tailTrace_33543
  have hstable : (prefixWord ++ tailWord_33543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33543).length < 2 ^ (prefixWord ++ tailWord_33543).sum := by decide
  have hdescent : baseEnd_33543 < baseStart_33543 := by decide
  rcases family_descends (prefixWord ++ tailWord_33543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33590 : List Nat := [5, 1, 2, 2, 2, 1, 1, 8]
def baseStart_33590 : Nat := 118140960795 + 33590 * 2 ^ 59
def prefixEnd_33590 : Nat := 4983230072969 + 3 ^ 40 * 33590 * 2
def baseEnd_33590 : Nat := 1277615939602134271891

theorem tailTrace_33590 : CollatzResearch.WordTrace tailWord_33590 prefixEnd_33590 1277615939602134271891 := by
  unfold tailWord_33590
  simp only [CollatzResearch.WordTrace]
  refine ⟨76570496769790097524139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 816751965544427706924149 76570496769790097524139)
  ·
    refine ⟨114855745154685146286209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76570496769790097524139 114855745154685146286209)
    ·
      refine ⟨86141808866013859714657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114855745154685146286209 86141808866013859714657)
      ·
        refine ⟨64606356649510394785993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86141808866013859714657 64606356649510394785993)
        ·
          refine ⟨48454767487132796089495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64606356649510394785993 48454767487132796089495)
          ·
            refine ⟨72682151230699194134243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48454767487132796089495 72682151230699194134243)
            ·
              refine ⟨109023226846048791201365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72682151230699194134243 109023226846048791201365)
              ·
                refine ⟨1277615939602134271891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 109023226846048791201365 1277615939602134271891)
                ·
                  rfl

theorem cell22_33590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_33590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33590 prefixEnd_33590 := by exact prefixLift 33590
  have htrace : WordTrace (prefixWord ++ tailWord_33590) baseStart_33590 baseEnd_33590 := by
    simpa [prefixWord, tailWord_33590, baseEnd_33590] using wordTrace_append hprefix tailTrace_33590
  have hstable : (prefixWord ++ tailWord_33590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33590).length < 2 ^ (prefixWord ++ tailWord_33590).sum := by decide
  have hdescent : baseEnd_33590 < baseStart_33590 := by decide
  rcases family_descends (prefixWord ++ tailWord_33590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33605 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_33605 : Nat := 118140960795 + 33605 * 2 ^ 59
def prefixEnd_33605 : Nat := 4983230072969 + 3 ^ 40 * 33605 * 2
def baseEnd_33605 : Nat := 11503678262964169321973

theorem tailTrace_33605 : CollatzResearch.WordTrace tailWord_33605 prefixEnd_33605 11503678262964169321973 := by
  unfold tailWord_33605
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225675043262299122182269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 817116695508199414788179 1225675043262299122182269)
  ·
    refine ⟨459628141223362170818351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1225675043262299122182269 459628141223362170818351)
    ·
      refine ⟨689442211835043256227527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459628141223362170818351 689442211835043256227527)
      ·
        refine ⟨1034163317752564884341291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689442211835043256227527 1034163317752564884341291)
        ·
          refine ⟨1551244976628847326511937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034163317752564884341291 1551244976628847326511937)
          ·
            refine ⟨1163433732471635494883953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551244976628847326511937 1163433732471635494883953)
            ·
              refine ⟨872575299353726621162965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163433732471635494883953 872575299353726621162965)
              ·
                refine ⟨20450983578602967683507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 872575299353726621162965 20450983578602967683507)
                ·
                  refine ⟨30676475367904451525261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20450983578602967683507 30676475367904451525261)
                  ·
                    refine ⟨11503678262964169321973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30676475367904451525261 11503678262964169321973)
                    ·
                      rfl

theorem cell22_33605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_33605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33605 prefixEnd_33605 := by exact prefixLift 33605
  have htrace : WordTrace (prefixWord ++ tailWord_33605) baseStart_33605 baseEnd_33605 := by
    simpa [prefixWord, tailWord_33605, baseEnd_33605] using wordTrace_append hprefix tailTrace_33605
  have hstable : (prefixWord ++ tailWord_33605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33605).length < 2 ^ (prefixWord ++ tailWord_33605).sum := by decide
  have hdescent : baseEnd_33605 < baseStart_33605 := by decide
  rcases family_descends (prefixWord ++ tailWord_33605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33616 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_33616 : Nat := 118140960795 + 33616 * 2 ^ 59
def prefixEnd_33616 : Nat := 4983230072969 + 3 ^ 40 * 33616 * 2
def baseEnd_33616 : Nat := 11507443787763807296939

theorem tailTrace_33616 : CollatzResearch.WordTrace tailWord_33616 prefixEnd_33616 11507443787763807296939 := by
  unfold tailWord_33616
  simp only [CollatzResearch.WordTrace]
  refine ⟨613038123111224000416351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 817384164148298667221801 613038123111224000416351)
  ·
    refine ⟨919557184666836000624527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613038123111224000416351 919557184666836000624527)
    ·
      refine ⟨1379335777000254000936791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919557184666836000624527 1379335777000254000936791)
      ·
        refine ⟨2069003665500381001405187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379335777000254000936791 2069003665500381001405187)
        ·
          refine ⟨3103505498250571502107781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069003665500381001405187 3103505498250571502107781)
          ·
            refine ⟨581907280921982156645209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3103505498250571502107781 581907280921982156645209)
            ·
              refine ⟨436430460691486617483907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581907280921982156645209 436430460691486617483907)
              ·
                refine ⟨654645691037229926225861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436430460691486617483907 654645691037229926225861)
                ·
                  refine ⟨122746067069480611167349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 654645691037229926225861 122746067069480611167349)
                  ·
                    refine ⟨11507443787763807296939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122746067069480611167349 11507443787763807296939)
                    ·
                      rfl

theorem cell22_33616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_33616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33616 prefixEnd_33616 := by exact prefixLift 33616
  have htrace : WordTrace (prefixWord ++ tailWord_33616) baseStart_33616 baseEnd_33616 := by
    simpa [prefixWord, tailWord_33616, baseEnd_33616] using wordTrace_append hprefix tailTrace_33616
  have hstable : (prefixWord ++ tailWord_33616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33616).length < 2 ^ (prefixWord ++ tailWord_33616).sum := by decide
  have hdescent : baseEnd_33616 < baseStart_33616 := by decide
  rcases family_descends (prefixWord ++ tailWord_33616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33618 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_33618 : Nat := 118140960795 + 33618 * 2 ^ 59
def prefixEnd_33618 : Nat := 4983230072969 + 3 ^ 40 * 33618 * 2
def baseEnd_33618 : Nat := 3836042809545489582311

theorem tailTrace_33618 : CollatzResearch.WordTrace tailWord_33618 prefixEnd_33618 3836042809545489582311 := by
  unfold tailWord_33618
  simp only [CollatzResearch.WordTrace]
  refine ⟨306537298053800585601377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 817432794810134894937005 306537298053800585601377)
  ·
    refine ⟨229902973540350439201033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 306537298053800585601377 229902973540350439201033)
    ·
      refine ⟨172427230155262829400775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229902973540350439201033 172427230155262829400775)
      ·
        refine ⟨258640845232894244101163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172427230155262829400775 258640845232894244101163)
        ·
          refine ⟨387961267849341366151745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258640845232894244101163 387961267849341366151745)
          ·
            refine ⟨290970950887006024613809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387961267849341366151745 290970950887006024613809)
            ·
              refine ⟨218228213165254518460357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290970950887006024613809 218228213165254518460357)
              ·
                refine ⟨40917789968485222211317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218228213165254518460357 40917789968485222211317)
                ·
                  refine ⟨3836042809545489582311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40917789968485222211317 3836042809545489582311)
                  ·
                    rfl

theorem cell22_33618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_33618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33618 prefixEnd_33618 := by exact prefixLift 33618
  have htrace : WordTrace (prefixWord ++ tailWord_33618) baseStart_33618 baseEnd_33618 := by
    simpa [prefixWord, tailWord_33618, baseEnd_33618] using wordTrace_append hprefix tailTrace_33618
  have hstable : (prefixWord ++ tailWord_33618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33618).length < 2 ^ (prefixWord ++ tailWord_33618).sum := by decide
  have hdescent : baseEnd_33618 < baseStart_33618 := by decide
  rcases family_descends (prefixWord ++ tailWord_33618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33635 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 5]
def baseStart_33635 : Nat := 118140960795 + 33635 * 2 ^ 59
def prefixEnd_33635 : Nat := 4983230072969 + 3 ^ 40 * 33635 * 2
def baseEnd_33635 : Nat := 3837982625351363690627

theorem tailTrace_33635 : CollatzResearch.WordTrace tailWord_33635 prefixEnd_33635 3837982625351363690627 := by
  unfold tailWord_33635
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226769233153614245774359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 817846155435742830516239 1226769233153614245774359)
  ·
    refine ⟨1840153849730421368661539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1226769233153614245774359 1840153849730421368661539)
    ·
      refine ⟨2760230774595632052992309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840153849730421368661539 2760230774595632052992309)
      ·
        refine ⟨258771635118340504968029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2760230774595632052992309 258771635118340504968029)
        ·
          refine ⟨97039363169377689363011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258771635118340504968029 97039363169377689363011)
          ·
            refine ⟨145559044754066534044517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97039363169377689363011 145559044754066534044517)
            ·
              refine ⟨27292320891387475133347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145559044754066534044517 27292320891387475133347)
              ·
                refine ⟨40938481337081212700021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27292320891387475133347 40938481337081212700021)
                ·
                  refine ⟨3837982625351363690627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40938481337081212700021 3837982625351363690627)
                  ·
                    rfl

theorem cell22_33635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 5].length) (baseStart_33635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33635 prefixEnd_33635 := by exact prefixLift 33635
  have htrace : WordTrace (prefixWord ++ tailWord_33635) baseStart_33635 baseEnd_33635 := by
    simpa [prefixWord, tailWord_33635, baseEnd_33635] using wordTrace_append hprefix tailTrace_33635
  have hstable : (prefixWord ++ tailWord_33635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33635).length < 2 ^ (prefixWord ++ tailWord_33635).sum := by decide
  have hdescent : baseEnd_33635 < baseStart_33635 := by decide
  rcases family_descends (prefixWord ++ tailWord_33635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33693 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_33693 : Nat := 118140960795 + 33693 * 2 ^ 59
def prefixEnd_33693 : Nat := 4983230072969 + 3 ^ 40 * 33693 * 2
def baseEnd_33693 : Nat := 11533802461361273121703

theorem tailTrace_33693 : CollatzResearch.WordTrace tailWord_33693 prefixEnd_33693 11533802461361273121703 := by
  unfold tailWord_33693
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228884666943490151385733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 819256444628993434257155 1228884666943490151385733)
  ·
    refine ⟨230415875051904403384825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1228884666943490151385733 230415875051904403384825)
    ·
      refine ⟨172811906288928302538619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230415875051904403384825 172811906288928302538619)
      ·
        refine ⟨259217859433392453807929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172811906288928302538619 259217859433392453807929)
        ·
          refine ⟨194413394575044340355947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259217859433392453807929 194413394575044340355947)
          ·
            refine ⟨291620091862566510533921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194413394575044340355947 291620091862566510533921)
            ·
              refine ⟨218715068896924882900441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291620091862566510533921 218715068896924882900441)
              ·
                refine ⟨164036301672693662175331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218715068896924882900441 164036301672693662175331)
                ·
                  refine ⟨246054452509040493262997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164036301672693662175331 246054452509040493262997)
                  ·
                    refine ⟨11533802461361273121703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 246054452509040493262997 11533802461361273121703)
                    ·
                      rfl

theorem cell22_33693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_33693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33693 prefixEnd_33693 := by exact prefixLift 33693
  have htrace : WordTrace (prefixWord ++ tailWord_33693) baseStart_33693 baseEnd_33693 := by
    simpa [prefixWord, tailWord_33693, baseEnd_33693] using wordTrace_append hprefix tailTrace_33693
  have hstable : (prefixWord ++ tailWord_33693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33693).length < 2 ^ (prefixWord ++ tailWord_33693).sum := by decide
  have hdescent : baseEnd_33693 < baseStart_33693 := by decide
  rcases family_descends (prefixWord ++ tailWord_33693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33695 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 1, 5]
def baseStart_33695 : Nat := 118140960795 + 33695 * 2 ^ 59
def prefixEnd_33695 : Nat := 4983230072969 + 3 ^ 40 * 33695 * 2
def baseEnd_33695 : Nat := 11534487102233934571697

theorem tailTrace_33695 : CollatzResearch.WordTrace tailWord_33695 prefixEnd_33695 11534487102233934571697 := by
  unfold tailWord_33695
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228957612936244492958539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 819305075290829661972359 1228957612936244492958539)
  ·
    refine ⟨1843436419404366739437809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1228957612936244492958539 1843436419404366739437809)
    ·
      refine ⟨1382577314553275054578357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1843436419404366739437809 1382577314553275054578357)
      ·
        refine ⟨129616623239369536366721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1382577314553275054578357 129616623239369536366721)
        ·
          refine ⟨97212467429527152275041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129616623239369536366721 97212467429527152275041)
          ·
            refine ⟨72909350572145364206281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97212467429527152275041 72909350572145364206281)
            ·
              refine ⟨54682012929109023154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72909350572145364206281 54682012929109023154711)
              ·
                refine ⟨82023019393663534732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54682012929109023154711 82023019393663534732067)
                ·
                  refine ⟨123034529090495302098101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82023019393663534732067 123034529090495302098101)
                  ·
                    refine ⟨11534487102233934571697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123034529090495302098101 11534487102233934571697)
                    ·
                      rfl

theorem cell22_33695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_33695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33695 prefixEnd_33695 := by exact prefixLift 33695
  have htrace : WordTrace (prefixWord ++ tailWord_33695) baseStart_33695 baseEnd_33695 := by
    simpa [prefixWord, tailWord_33695, baseEnd_33695] using wordTrace_append hprefix tailTrace_33695
  have hstable : (prefixWord ++ tailWord_33695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33695).length < 2 ^ (prefixWord ++ tailWord_33695).sum := by decide
  have hdescent : baseEnd_33695 < baseStart_33695 := by decide
  rcases family_descends (prefixWord ++ tailWord_33695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33716 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_33716 : Nat := 118140960795 + 33716 * 2 ^ 59
def prefixEnd_33716 : Nat := 4983230072969 + 3 ^ 40 * 33716 * 2
def baseEnd_33716 : Nat := 11541675831396879796633

theorem tailTrace_33716 : CollatzResearch.WordTrace tailWord_33716 prefixEnd_33716 11541675831396879796633 := by
  unfold tailWord_33716
  simp only [CollatzResearch.WordTrace]
  refine ⟨614861772930082539736501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 819815697240110052982001 614861772930082539736501)
  ·
    refine ⟨57643291212195238100297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 614861772930082539736501 57643291212195238100297)
    ·
      refine ⟨43232468409146428575223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57643291212195238100297 43232468409146428575223)
      ·
        refine ⟨64848702613719642862835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43232468409146428575223 64848702613719642862835)
        ·
          refine ⟨97273053920579464294253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64848702613719642862835 97273053920579464294253)
          ·
            refine ⟨36477395220217299110345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97273053920579464294253 36477395220217299110345)
            ·
              refine ⟨27358046415162974332759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36477395220217299110345 27358046415162974332759)
              ·
                refine ⟨41037069622744461499139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27358046415162974332759 41037069622744461499139)
                ·
                  refine ⟨61555604434116692248709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41037069622744461499139 61555604434116692248709)
                  ·
                    refine ⟨11541675831396879796633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61555604434116692248709 11541675831396879796633)
                    ·
                      rfl

theorem cell22_33716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_33716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33716 prefixEnd_33716 := by exact prefixLift 33716
  have htrace : WordTrace (prefixWord ++ tailWord_33716) baseStart_33716 baseEnd_33716 := by
    simpa [prefixWord, tailWord_33716, baseEnd_33716] using wordTrace_append hprefix tailTrace_33716
  have hstable : (prefixWord ++ tailWord_33716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33716).length < 2 ^ (prefixWord ++ tailWord_33716).sum := by decide
  have hdescent : baseEnd_33716 < baseStart_33716 := by decide
  rcases family_descends (prefixWord ++ tailWord_33716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33757 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_33757 : Nat := 118140960795 + 33757 * 2 ^ 59
def prefixEnd_33757 : Nat := 4983230072969 + 3 ^ 40 * 33757 * 2
def baseEnd_33757 : Nat := 11555710969286439521507

theorem tailTrace_33757 : CollatzResearch.WordTrace tailWord_33757 prefixEnd_33757 11555710969286439521507 := by
  unfold tailWord_33757
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231218938711629081715525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 820812625807752721143683 1231218938711629081715525)
  ·
    refine ⟨230853551008430452821661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1231218938711629081715525 230853551008430452821661)
    ·
      refine ⟨86570081628161419808123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230853551008430452821661 86570081628161419808123)
      ·
        refine ⟨129855122442242129712185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86570081628161419808123 129855122442242129712185)
        ·
          refine ⟨97391341831681597284139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129855122442242129712185 97391341831681597284139)
          ·
            refine ⟨146087012747522395926209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97391341831681597284139 146087012747522395926209)
            ·
              refine ⟨109565259560641796944657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146087012747522395926209 109565259560641796944657)
              ·
                refine ⟨82173944670481347708493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109565259560641796944657 82173944670481347708493)
                ·
                  refine ⟨30815229251430505390685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82173944670481347708493 30815229251430505390685)
                  ·
                    refine ⟨11555710969286439521507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30815229251430505390685 11555710969286439521507)
                    ·
                      rfl

theorem cell22_33757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_33757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33757 prefixEnd_33757 := by exact prefixLift 33757
  have htrace : WordTrace (prefixWord ++ tailWord_33757) baseStart_33757 baseEnd_33757 := by
    simpa [prefixWord, tailWord_33757, baseEnd_33757] using wordTrace_append hprefix tailTrace_33757
  have hstable : (prefixWord ++ tailWord_33757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33757).length < 2 ^ (prefixWord ++ tailWord_33757).sum := by decide
  have hdescent : baseEnd_33757 < baseStart_33757 := by decide
  rcases family_descends (prefixWord ++ tailWord_33757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33768 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_33768 : Nat := 118140960795 + 33768 * 2 ^ 59
def prefixEnd_33768 : Nat := 4983230072969 + 3 ^ 40 * 33768 * 2
def baseEnd_33768 : Nat := 11559476494086077496473

theorem tailTrace_33768 : CollatzResearch.WordTrace tailWord_33768 prefixEnd_33768 11559476494086077496473 := by
  unfold tailWord_33768
  simp only [CollatzResearch.WordTrace]
  refine ⟨615810070835888980182979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 821080094447851973577305 615810070835888980182979)
  ·
    refine ⟨923715106253833470274469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 615810070835888980182979 923715106253833470274469)
    ·
      refine ⟨173196582422593775676463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 923715106253833470274469 173196582422593775676463)
      ·
        refine ⟨259794873633890663514695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173196582422593775676463 259794873633890663514695)
        ·
          refine ⟨389692310450835995272043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259794873633890663514695 389692310450835995272043)
          ·
            refine ⟨584538465676253992908065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389692310450835995272043 584538465676253992908065)
            ·
              refine ⟨438403849257190494681049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584538465676253992908065 438403849257190494681049)
              ·
                refine ⟨328802886942892871010787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438403849257190494681049 328802886942892871010787)
                ·
                  refine ⟨493204330414339306516181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328802886942892871010787 493204330414339306516181)
                  ·
                    refine ⟨11559476494086077496473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 493204330414339306516181 11559476494086077496473)
                    ·
                      rfl

theorem cell22_33768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_33768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33768 prefixEnd_33768 := by exact prefixLift 33768
  have htrace : WordTrace (prefixWord ++ tailWord_33768) baseStart_33768 baseEnd_33768 := by
    simpa [prefixWord, tailWord_33768, baseEnd_33768] using wordTrace_append hprefix tailTrace_33768
  have hstable : (prefixWord ++ tailWord_33768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33768).length < 2 ^ (prefixWord ++ tailWord_33768).sum := by decide
  have hdescent : baseEnd_33768 < baseStart_33768 := by decide
  rcases family_descends (prefixWord ++ tailWord_33768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33849 : List Nat := [1, 2, 1, 5, 2, 1, 4, 2, 4]
def baseStart_33849 : Nat := 118140960795 + 33849 * 2 ^ 59
def prefixEnd_33849 : Nat := 4983230072969 + 3 ^ 40 * 33849 * 2
def baseEnd_33849 : Nat := 3862401483142955407075

theorem tailTrace_33849 : CollatzResearch.WordTrace tailWord_33849 prefixEnd_33849 3862401483142955407075 := by
  unfold tailWord_33849
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234574454378328794064601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 823049636252219196043067 1234574454378328794064601)
  ·
    refine ⟨925930840783746595548451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1234574454378328794064601 925930840783746595548451)
    ·
      refine ⟨1388896261175619893322677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925930840783746595548451 1388896261175619893322677)
      ·
        refine ⟨130209024485214364999001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1388896261175619893322677 130209024485214364999001)
        ·
          refine ⟨97656768363910773749251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130209024485214364999001 97656768363910773749251)
          ·
            refine ⟨146485152545866160623877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97656768363910773749251 146485152545866160623877)
            ·
              refine ⟨27465966102349905116977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146485152545866160623877 27465966102349905116977)
              ·
                refine ⟨20599474576762428837733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27465966102349905116977 20599474576762428837733)
                ·
                  refine ⟨3862401483142955407075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20599474576762428837733 3862401483142955407075)
                  ·
                    rfl

theorem cell22_33849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_33849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33849 prefixEnd_33849 := by exact prefixLift 33849
  have htrace : WordTrace (prefixWord ++ tailWord_33849) baseStart_33849 baseEnd_33849 := by
    simpa [prefixWord, tailWord_33849, baseEnd_33849] using wordTrace_append hprefix tailTrace_33849
  have hstable : (prefixWord ++ tailWord_33849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33849).length < 2 ^ (prefixWord ++ tailWord_33849).sum := by decide
  have hdescent : baseEnd_33849 < baseStart_33849 := by decide
  rcases family_descends (prefixWord ++ tailWord_33849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33875 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 5, 3]
def baseStart_33875 : Nat := 118140960795 + 33875 * 2 ^ 59
def prefixEnd_33875 : Nat := 4983230072969 + 3 ^ 40 * 33875 * 2
def baseEnd_33875 : Nat := 11596104780773465071145

theorem tailTrace_33875 : CollatzResearch.WordTrace tailWord_33875 prefixEnd_33875 11596104780773465071145 := by
  unfold tailWord_33875
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235522752284135234511079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 823681834856090156340719 1235522752284135234511079)
  ·
    refine ⟨1853284128426202851766619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235522752284135234511079 1853284128426202851766619)
    ·
      refine ⟨2779926192639304277649929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853284128426202851766619 2779926192639304277649929)
      ·
        refine ⟨2084944644479478208237447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2779926192639304277649929 2084944644479478208237447)
        ·
          refine ⟨3127416966719217312356171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084944644479478208237447 3127416966719217312356171)
          ·
            refine ⟨4691125450078825968534257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127416966719217312356171 4691125450078825968534257)
            ·
              refine ⟨3518344087559119476400693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4691125450078825968534257 3518344087559119476400693)
              ·
                refine ⟨329844758208667450912565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3518344087559119476400693 329844758208667450912565)
                ·
                  refine ⟨30922946082062573523053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329844758208667450912565 30922946082062573523053)
                  ·
                    refine ⟨11596104780773465071145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30922946082062573523053 11596104780773465071145)
                    ·
                      rfl

theorem cell22_33875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 3].length) (baseStart_33875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33875 prefixEnd_33875 := by exact prefixLift 33875
  have htrace : WordTrace (prefixWord ++ tailWord_33875) baseStart_33875 baseEnd_33875 := by
    simpa [prefixWord, tailWord_33875, baseEnd_33875] using wordTrace_append hprefix tailTrace_33875
  have hstable : (prefixWord ++ tailWord_33875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33875).length < 2 ^ (prefixWord ++ tailWord_33875).sum := by decide
  have hdescent : baseEnd_33875 < baseStart_33875 := by decide
  rcases family_descends (prefixWord ++ tailWord_33875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33905 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 5]
def baseStart_33905 : Nat := 118140960795 + 33905 * 2 ^ 59
def prefixEnd_33905 : Nat := 4983230072969 + 3 ^ 40 * 33905 * 2
def baseEnd_33905 : Nat := 3868791464621128940351

theorem tailTrace_33905 : CollatzResearch.WordTrace tailWord_33905 prefixEnd_33905 3868791464621128940351 := by
  unfold tailWord_33905
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236616942175450358103169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 824411294783633572068779 1236616942175450358103169)
  ·
    refine ⟨927462706631587768577377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1236616942175450358103169 927462706631587768577377)
    ·
      refine ⟨695597029973690826433033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927462706631587768577377 695597029973690826433033)
      ·
        refine ⟨521697772480268119824775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 695597029973690826433033 521697772480268119824775)
        ·
          refine ⟨782546658720402179737163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521697772480268119824775 782546658720402179737163)
          ·
            refine ⟨1173819988080603269605745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782546658720402179737163 1173819988080603269605745)
            ·
              refine ⟨880364991060452452204309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173819988080603269605745 880364991060452452204309)
              ·
                refine ⟨41267108955958708697077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 880364991060452452204309 41267108955958708697077)
                ·
                  refine ⟨3868791464621128940351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41267108955958708697077 3868791464621128940351)
                  ·
                    rfl

theorem cell22_33905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_33905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33905 prefixEnd_33905 := by exact prefixLift 33905
  have htrace : WordTrace (prefixWord ++ tailWord_33905) baseStart_33905 baseEnd_33905 := by
    simpa [prefixWord, tailWord_33905, baseEnd_33905] using wordTrace_append hprefix tailTrace_33905
  have hstable : (prefixWord ++ tailWord_33905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33905).length < 2 ^ (prefixWord ++ tailWord_33905).sum := by decide
  have hdescent : baseEnd_33905 < baseStart_33905 := by decide
  rcases family_descends (prefixWord ++ tailWord_33905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33920 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_33920 : Nat := 118140960795 + 33920 * 2 ^ 59
def prefixEnd_33920 : Nat := 4983230072969 + 3 ^ 40 * 33920 * 2
def baseEnd_33920 : Nat := 11611509200408347696007

theorem tailTrace_33920 : CollatzResearch.WordTrace tailWord_33920 prefixEnd_33920 11611509200408347696007 := by
  unfold tailWord_33920
  simp only [CollatzResearch.WordTrace]
  refine ⟨618582018560553959949607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 824776024747405279932809 618582018560553959949607)
  ·
    refine ⟨927873027840830939924411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618582018560553959949607 927873027840830939924411)
    ·
      refine ⟨1391809541761246409886617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927873027840830939924411 1391809541761246409886617)
      ·
        refine ⟨1043857156320934807414963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1391809541761246409886617 1043857156320934807414963)
        ·
          refine ⟨1565785734481402211122445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043857156320934807414963 1565785734481402211122445)
          ·
            refine ⟨587169650430525829170917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1565785734481402211122445 587169650430525829170917)
            ·
              refine ⟨110094309455723592969547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 587169650430525829170917 110094309455723592969547)
              ·
                refine ⟨165141464183585389454321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110094309455723592969547 165141464183585389454321)
                ·
                  refine ⟨123856098137689042090741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165141464183585389454321 123856098137689042090741)
                  ·
                    refine ⟨11611509200408347696007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123856098137689042090741 11611509200408347696007)
                    ·
                      rfl

theorem cell22_33920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_33920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33920 prefixEnd_33920 := by exact prefixLift 33920
  have htrace : WordTrace (prefixWord ++ tailWord_33920) baseStart_33920 baseEnd_33920 := by
    simpa [prefixWord, tailWord_33920, baseEnd_33920] using wordTrace_append hprefix tailTrace_33920
  have hstable : (prefixWord ++ tailWord_33920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33920).length < 2 ^ (prefixWord ++ tailWord_33920).sum := by decide
  have hdescent : baseEnd_33920 < baseStart_33920 := by decide
  rcases family_descends (prefixWord ++ tailWord_33920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33952 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_33952 : Nat := 118140960795 + 33952 * 2 ^ 59
def prefixEnd_33952 : Nat := 4983230072969 + 3 ^ 40 * 33952 * 2
def baseEnd_33952 : Nat := 11622463454370930895909

theorem tailTrace_33952 : CollatzResearch.WordTrace tailWord_33952 prefixEnd_33952 11622463454370930895909 := by
  unfold tailWord_33952
  simp only [CollatzResearch.WordTrace]
  refine ⟨619165586502588692532055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 825554115336784923376073 619165586502588692532055)
  ·
    refine ⟨928748379753883038798083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 619165586502588692532055 928748379753883038798083)
    ·
      refine ⟨1393122569630824558197125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928748379753883038798083 1393122569630824558197125)
      ·
        refine ⟨261210481805779604661961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1393122569630824558197125 261210481805779604661961)
        ·
          refine ⟨195907861354334703496471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261210481805779604661961 195907861354334703496471)
          ·
            refine ⟨293861792031502055244707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195907861354334703496471 293861792031502055244707)
            ·
              refine ⟨440792688047253082867061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293861792031502055244707 440792688047253082867061)
              ·
                refine ⟨41324314504429976518787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 440792688047253082867061 41324314504429976518787)
                ·
                  refine ⟨61986471756644964778181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41324314504429976518787 61986471756644964778181)
                  ·
                    refine ⟨11622463454370930895909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61986471756644964778181 11622463454370930895909)
                    ·
                      rfl

theorem cell22_33952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_33952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33952 prefixEnd_33952 := by exact prefixLift 33952
  have htrace : WordTrace (prefixWord ++ tailWord_33952) baseStart_33952 baseEnd_33952 := by
    simpa [prefixWord, tailWord_33952, baseEnd_33952] using wordTrace_append hprefix tailTrace_33952
  have hstable : (prefixWord ++ tailWord_33952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33952).length < 2 ^ (prefixWord ++ tailWord_33952).sum := by decide
  have hdescent : baseEnd_33952 < baseStart_33952 := by decide
  rcases family_descends (prefixWord ++ tailWord_33952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33967 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 4]
def baseStart_33967 : Nat := 118140960795 + 33967 * 2 ^ 59
def prefixEnd_33967 : Nat := 4983230072969 + 3 ^ 40 * 33967 * 2
def baseEnd_33967 : Nat := 3875866086971963923621

theorem tailTrace_33967 : CollatzResearch.WordTrace tailWord_33967 prefixEnd_33967 3875866086971963923621 := by
  unfold tailWord_33967
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238878267950834946860155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 825918845300556631240103 1238878267950834946860155)
  ·
    refine ⟨1858317401926252420290233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1238878267950834946860155 1858317401926252420290233)
    ·
      refine ⟨1393738051444689315217675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1858317401926252420290233 1393738051444689315217675)
      ·
        refine ⟨2090607077167033972826513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393738051444689315217675 2090607077167033972826513)
        ·
          refine ⟨1567955307875275479619885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2090607077167033972826513 1567955307875275479619885)
          ·
            refine ⟨587983240453228304857457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1567955307875275479619885 587983240453228304857457)
            ·
              refine ⟨440987430339921228643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587983240453228304857457 440987430339921228643093)
              ·
                refine ⟨20671285797183807592645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 440987430339921228643093 20671285797183807592645)
                ·
                  refine ⟨3875866086971963923621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20671285797183807592645 3875866086971963923621)
                  ·
                    rfl

theorem cell22_33967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 4].length) (baseStart_33967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_33967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_33967 prefixEnd_33967 := by exact prefixLift 33967
  have htrace : WordTrace (prefixWord ++ tailWord_33967) baseStart_33967 baseEnd_33967 := by
    simpa [prefixWord, tailWord_33967, baseEnd_33967] using wordTrace_append hprefix tailTrace_33967
  have hstable : (prefixWord ++ tailWord_33967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33967).length < 2 ^ (prefixWord ++ tailWord_33967).sum := by decide
  have hdescent : baseEnd_33967 < baseStart_33967 := by decide
  rcases family_descends (prefixWord ++ tailWord_33967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34029 : List Nat := [1, 5, 1, 2, 2, 3, 1, 7]
def baseStart_34029 : Nat := 118140960795 + 34029 * 2 ^ 59
def prefixEnd_34029 : Nat := 4983230072969 + 3 ^ 40 * 34029 * 2
def baseEnd_34029 : Nat := 1294313569774266302297

theorem tailTrace_34029 : CollatzResearch.WordTrace tailWord_34029 prefixEnd_34029 1294313569774266302297 := by
  unfold tailWord_34029
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241139593726219535617141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 827426395817479690411427 1241139593726219535617141)
  ·
    refine ⟨116356836911833081464107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1241139593726219535617141 116356836911833081464107)
    ·
      refine ⟨174535255367749622196161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116356836911833081464107 174535255367749622196161)
      ·
        refine ⟨130901441525812216647121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174535255367749622196161 130901441525812216647121)
        ·
          refine ⟨98176081144359162485341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130901441525812216647121 98176081144359162485341)
          ·
            refine ⟨36816030429134685932003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98176081144359162485341 36816030429134685932003)
            ·
              refine ⟨55224045643702028898005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36816030429134685932003 55224045643702028898005)
              ·
                refine ⟨1294313569774266302297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55224045643702028898005 1294313569774266302297)
                ·
                  rfl

theorem cell22_34029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 7].length) (baseStart_34029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34029 prefixEnd_34029 := by exact prefixLift 34029
  have htrace : WordTrace (prefixWord ++ tailWord_34029) baseStart_34029 baseEnd_34029 := by
    simpa [prefixWord, tailWord_34029, baseEnd_34029] using wordTrace_append hprefix tailTrace_34029
  have hstable : (prefixWord ++ tailWord_34029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34029).length < 2 ^ (prefixWord ++ tailWord_34029).sum := by decide
  have hdescent : baseEnd_34029 < baseStart_34029 := by decide
  rcases family_descends (prefixWord ++ tailWord_34029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34040 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_34040 : Nat := 118140960795 + 34040 * 2 ^ 59
def prefixEnd_34040 : Nat := 4983230072969 + 3 ^ 40 * 34040 * 2
def baseEnd_34040 : Nat := 3884195884256011565213

theorem tailTrace_34040 : CollatzResearch.WordTrace tailWord_34040 prefixEnd_34040 3884195884256011565213 := by
  unfold tailWord_34040
  simp only [CollatzResearch.WordTrace]
  refine ⟨620770398343184207133787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 827693864457578942845049 620770398343184207133787)
  ·
    refine ⟨931155597514776310700681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620770398343184207133787 931155597514776310700681)
    ·
      refine ⟨698366698136082233025511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 931155597514776310700681 698366698136082233025511)
      ·
        refine ⟨1047550047204123349538267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 698366698136082233025511 1047550047204123349538267)
        ·
          refine ⟨1571325070806185024307401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1047550047204123349538267 1571325070806185024307401)
          ·
            refine ⟨1178493803104638768230551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1571325070806185024307401 1178493803104638768230551)
            ·
              refine ⟨1767740704656958152345827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178493803104638768230551 1767740704656958152345827)
              ·
                refine ⟨2651611056985437228518741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767740704656958152345827 2651611056985437228518741)
                ·
                  refine ⟨3884195884256011565213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 2651611056985437228518741 3884195884256011565213)
                  ·
                    rfl

theorem cell22_34040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_34040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34040 prefixEnd_34040 := by exact prefixLift 34040
  have htrace : WordTrace (prefixWord ++ tailWord_34040) baseStart_34040 baseEnd_34040 := by
    simpa [prefixWord, tailWord_34040, baseEnd_34040] using wordTrace_append hprefix tailTrace_34040
  have hstable : (prefixWord ++ tailWord_34040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34040).length < 2 ^ (prefixWord ++ tailWord_34040).sum := by decide
  have hdescent : baseEnd_34040 < baseStart_34040 := by decide
  rcases family_descends (prefixWord ++ tailWord_34040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34072 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_34072 : Nat := 118140960795 + 34072 * 2 ^ 59
def prefixEnd_34072 : Nat := 4983230072969 + 3 ^ 40 * 34072 * 2
def baseEnd_34072 : Nat := 11663541906730617895541

theorem tailTrace_34072 : CollatzResearch.WordTrace tailWord_34072 prefixEnd_34072 11663541906730617895541 := by
  unfold tailWord_34072
  simp only [CollatzResearch.WordTrace]
  refine ⟨621353966285218939716235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 828471955046958586288313 621353966285218939716235)
  ·
    refine ⟨932030949427828409574353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 621353966285218939716235 932030949427828409574353)
    ·
      refine ⟨699023212070871307180765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 932030949427828409574353 699023212070871307180765)
      ·
        refine ⟨262133704526576740192787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 699023212070871307180765 262133704526576740192787)
        ·
          refine ⟨393200556789865110289181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262133704526576740192787 393200556789865110289181)
          ·
            refine ⟨147450208796199416358443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393200556789865110289181 147450208796199416358443)
            ·
              refine ⟨221175313194299124537665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147450208796199416358443 221175313194299124537665)
              ·
                refine ⟨165881484895724343403249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221175313194299124537665 165881484895724343403249)
                ·
                  refine ⟨124411113671793257552437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165881484895724343403249 124411113671793257552437)
                  ·
                    refine ⟨11663541906730617895541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124411113671793257552437 11663541906730617895541)
                    ·
                      rfl

theorem cell22_34072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_34072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34072 prefixEnd_34072 := by exact prefixLift 34072
  have htrace : WordTrace (prefixWord ++ tailWord_34072) baseStart_34072 baseEnd_34072 := by
    simpa [prefixWord, tailWord_34072, baseEnd_34072] using wordTrace_append hprefix tailTrace_34072
  have hstable : (prefixWord ++ tailWord_34072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34072).length < 2 ^ (prefixWord ++ tailWord_34072).sum := by decide
  have hdescent : baseEnd_34072 < baseStart_34072 := by decide
  rcases family_descends (prefixWord ++ tailWord_34072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34074 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_34074 : Nat := 118140960795 + 34074 * 2 ^ 59
def prefixEnd_34074 : Nat := 4983230072969 + 3 ^ 40 * 34074 * 2
def baseEnd_34074 : Nat := 3888075515867759781845

theorem tailTrace_34074 : CollatzResearch.WordTrace tailWord_34074 prefixEnd_34074 3888075515867759781845 := by
  unfold tailWord_34074
  simp only [CollatzResearch.WordTrace]
  refine ⟨310695219640798055251319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 828520585708794814003517 310695219640798055251319)
  ·
    refine ⟨466042829461197082876979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 310695219640798055251319 466042829461197082876979)
    ·
      refine ⟨699064244191795624315469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466042829461197082876979 699064244191795624315469)
      ·
        refine ⟨262149091571923359118301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 699064244191795624315469 262149091571923359118301)
        ·
          refine ⟨98305909339471259669363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262149091571923359118301 98305909339471259669363)
          ·
            refine ⟨147458864009206889504045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98305909339471259669363 147458864009206889504045)
            ·
              refine ⟨55297074003452583564017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147458864009206889504045 55297074003452583564017)
              ·
                refine ⟨41472805502589437673013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55297074003452583564017 41472805502589437673013)
                ·
                  refine ⟨3888075515867759781845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41472805502589437673013 3888075515867759781845)
                  ·
                    rfl

theorem cell22_34074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_34074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34074 prefixEnd_34074 := by exact prefixLift 34074
  have htrace : WordTrace (prefixWord ++ tailWord_34074) baseStart_34074 baseEnd_34074 := by
    simpa [prefixWord, tailWord_34074, baseEnd_34074] using wordTrace_append hprefix tailTrace_34074
  have hstable : (prefixWord ++ tailWord_34074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34074).length < 2 ^ (prefixWord ++ tailWord_34074).sum := by decide
  have hdescent : baseEnd_34074 < baseStart_34074 := by decide
  rcases family_descends (prefixWord ++ tailWord_34074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34117 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_34117 : Nat := 118140960795 + 34117 * 2 ^ 59
def prefixEnd_34117 : Nat := 4983230072969 + 3 ^ 40 * 34117 * 2
def baseEnd_34117 : Nat := 11678946326365500520403

theorem tailTrace_34117 : CollatzResearch.WordTrace tailWord_34117 prefixEnd_34117 11678946326365500520403 := by
  unfold tailWord_34117
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244349217407410564820605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 829566144938273709880403 1244349217407410564820605)
  ·
    refine ⟨466630956527778961807727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1244349217407410564820605 466630956527778961807727)
    ·
      refine ⟨699946434791668442711591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466630956527778961807727 699946434791668442711591)
      ·
        refine ⟨1049919652187502664067387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699946434791668442711591 1049919652187502664067387)
        ·
          refine ⟨1574879478281253996101081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049919652187502664067387 1574879478281253996101081)
          ·
            refine ⟨1181159608710940497075811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574879478281253996101081 1181159608710940497075811)
            ·
              refine ⟨1771739413066410745613717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181159608710940497075811 1771739413066410745613717)
              ·
                refine ⟨83050284987488003700643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1771739413066410745613717 83050284987488003700643)
                ·
                  refine ⟨124575427481232005550965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83050284987488003700643 124575427481232005550965)
                  ·
                    refine ⟨11678946326365500520403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124575427481232005550965 11678946326365500520403)
                    ·
                      rfl

theorem cell22_34117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_34117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34117 prefixEnd_34117 := by exact prefixLift 34117
  have htrace : WordTrace (prefixWord ++ tailWord_34117) baseStart_34117 baseEnd_34117 := by
    simpa [prefixWord, tailWord_34117, baseEnd_34117] using wordTrace_append hprefix tailTrace_34117
  have hstable : (prefixWord ++ tailWord_34117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34117).length < 2 ^ (prefixWord ++ tailWord_34117).sum := by decide
  have hdescent : baseEnd_34117 < baseStart_34117 := by decide
  rcases family_descends (prefixWord ++ tailWord_34117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34136 : List Nat := [2, 1, 2, 2, 1, 1, 7, 2, 4]
def baseStart_34136 : Nat := 118140960795 + 34136 * 2 ^ 59
def prefixEnd_34136 : Nat := 4983230072969 + 3 ^ 40 * 34136 * 2
def baseEnd_34136 : Nat := 3895150138218594765115

theorem tailTrace_34136 : CollatzResearch.WordTrace tailWord_34136 prefixEnd_34136 3895150138218594765115 := by
  unfold tailWord_34136
  simp only [CollatzResearch.WordTrace]
  refine ⟨622521102169288404881131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 830028136225717873174841 622521102169288404881131)
  ·
    refine ⟨933781653253932607321697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 622521102169288404881131 933781653253932607321697)
    ·
      refine ⟨700336239940449455491273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 933781653253932607321697 700336239940449455491273)
      ·
        refine ⟨525252179955337091618455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700336239940449455491273 525252179955337091618455)
        ·
          refine ⟨787878269933005637427683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525252179955337091618455 787878269933005637427683)
          ·
            refine ⟨1181817404899508456141525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787878269933005637427683 1181817404899508456141525)
            ·
              refine ⟨27698845427332229440817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1181817404899508456141525 27698845427332229440817)
              ·
                refine ⟨20774134070499172080613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27698845427332229440817 20774134070499172080613)
                ·
                  refine ⟨3895150138218594765115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20774134070499172080613 3895150138218594765115)
                  ·
                    rfl

theorem cell22_34136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_34136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34136 prefixEnd_34136 := by exact prefixLift 34136
  have htrace : WordTrace (prefixWord ++ tailWord_34136) baseStart_34136 baseEnd_34136 := by
    simpa [prefixWord, tailWord_34136, baseEnd_34136] using wordTrace_append hprefix tailTrace_34136
  have hstable : (prefixWord ++ tailWord_34136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34136).length < 2 ^ (prefixWord ++ tailWord_34136).sum := by decide
  have hdescent : baseEnd_34136 < baseStart_34136 := by decide
  rcases family_descends (prefixWord ++ tailWord_34136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34147 : List Nat := [1, 1, 1, 5, 2, 2, 1, 9]
def baseStart_34147 : Nat := 118140960795 + 34147 * 2 ^ 59
def prefixEnd_34147 : Nat := 4983230072969 + 3 ^ 40 * 34147 * 2
def baseEnd_34147 : Nat := 1298801771050602474479

theorem tailTrace_34147 : CollatzResearch.WordTrace tailWord_34147 prefixEnd_34147 1298801771050602474479 := by
  unfold tailWord_34147
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245443407298725688412695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 830295604865817125608463 1245443407298725688412695)
  ·
    refine ⟨1868165110948088532619043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245443407298725688412695 1868165110948088532619043)
    ·
      refine ⟨2802247666422132798928565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868165110948088532619043 2802247666422132798928565)
      ·
        refine ⟨262710718727074949899553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2802247666422132798928565 262710718727074949899553)
        ·
          refine ⟨197033039045306212424665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262710718727074949899553 197033039045306212424665)
          ·
            refine ⟨147774779283979659318499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197033039045306212424665 147774779283979659318499)
            ·
              refine ⟨221662168925969488977749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147774779283979659318499 221662168925969488977749)
              ·
                refine ⟨1298801771050602474479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 221662168925969488977749 1298801771050602474479)
                ·
                  rfl

theorem cell22_34147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 9].length) (baseStart_34147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34147 prefixEnd_34147 := by exact prefixLift 34147
  have htrace : WordTrace (prefixWord ++ tailWord_34147) baseStart_34147 baseEnd_34147 := by
    simpa [prefixWord, tailWord_34147, baseEnd_34147] using wordTrace_append hprefix tailTrace_34147
  have hstable : (prefixWord ++ tailWord_34147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34147).length < 2 ^ (prefixWord ++ tailWord_34147).sum := by decide
  have hdescent : baseEnd_34147 < baseStart_34147 := by decide
  rcases family_descends (prefixWord ++ tailWord_34147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34254 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_34254 : Nat := 118140960795 + 34254 * 2 ^ 59
def prefixEnd_34254 : Nat := 4983230072969 + 3 ^ 40 * 34254 * 2
def baseEnd_34254 : Nat := 3908614742047603281661

theorem tailTrace_34254 : CollatzResearch.WordTrace tailWord_34254 prefixEnd_34254 3908614742047603281661 := by
  unfold tailWord_34254
  simp only [CollatzResearch.WordTrace]
  refine ⟨156168252238885370319727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 832897345274055308371877 156168252238885370319727)
  ·
    refine ⟨234252378358328055479591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156168252238885370319727 234252378358328055479591)
    ·
      refine ⟨351378567537492083219387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234252378358328055479591 351378567537492083219387)
      ·
        refine ⟨527067851306238124829081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351378567537492083219387 527067851306238124829081)
        ·
          refine ⟨395300888479678593621811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527067851306238124829081 395300888479678593621811)
          ·
            refine ⟨592951332719517890432717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395300888479678593621811 592951332719517890432717)
            ·
              refine ⟨222356749769819208912269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 592951332719517890432717 222356749769819208912269)
              ·
                refine ⟨83383781163682203342101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222356749769819208912269 83383781163682203342101)
                ·
                  refine ⟨3908614742047603281661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83383781163682203342101 3908614742047603281661)
                  ·
                    rfl

theorem cell22_34254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_34254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34254 prefixEnd_34254 := by exact prefixLift 34254
  have htrace : WordTrace (prefixWord ++ tailWord_34254) baseStart_34254 baseEnd_34254 := by
    simpa [prefixWord, tailWord_34254, baseEnd_34254] using wordTrace_append hprefix tailTrace_34254
  have hstable : (prefixWord ++ tailWord_34254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34254).length < 2 ^ (prefixWord ++ tailWord_34254).sum := by decide
  have hdescent : baseEnd_34254 < baseStart_34254 := by decide
  rcases family_descends (prefixWord ++ tailWord_34254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34286 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_34286 : Nat := 118140960795 + 34286 * 2 ^ 59
def prefixEnd_34286 : Nat := 4983230072969 + 3 ^ 40 * 34286 * 2
def baseEnd_34286 : Nat := 11736798480105393044885

theorem tailTrace_34286 : CollatzResearch.WordTrace tailWord_34286 prefixEnd_34286 11736798480105393044885 := by
  unfold tailWord_34286
  simp only [CollatzResearch.WordTrace]
  refine ⟨156314144224394053465339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 833675435863434951815141 156314144224394053465339)
  ·
    refine ⟨234471216336591080198009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156314144224394053465339 234471216336591080198009)
    ·
      refine ⟨175853412252443310148507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234471216336591080198009 175853412252443310148507)
      ·
        refine ⟨263780118378664965222761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175853412252443310148507 263780118378664965222761)
        ·
          refine ⟨197835088783998723917071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263780118378664965222761 197835088783998723917071)
          ·
            refine ⟨296752633175998085875607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197835088783998723917071 296752633175998085875607)
            ·
              refine ⟨445128949763997128813411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296752633175998085875607 445128949763997128813411)
              ·
                refine ⟨667693424645995693220117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445128949763997128813411 667693424645995693220117)
                ·
                  refine ⟨31298129280281048119693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 667693424645995693220117 31298129280281048119693)
                  ·
                    refine ⟨11736798480105393044885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31298129280281048119693 11736798480105393044885)
                    ·
                      rfl

theorem cell22_34286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_34286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34286 prefixEnd_34286 := by exact prefixLift 34286
  have htrace : WordTrace (prefixWord ++ tailWord_34286) baseStart_34286 baseEnd_34286 := by
    simpa [prefixWord, tailWord_34286, baseEnd_34286] using wordTrace_append hprefix tailTrace_34286
  have hstable : (prefixWord ++ tailWord_34286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34286).length < 2 ^ (prefixWord ++ tailWord_34286).sum := by decide
  have hdescent : baseEnd_34286 < baseStart_34286 := by decide
  rcases family_descends (prefixWord ++ tailWord_34286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34288 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 4]
def baseStart_34288 : Nat := 118140960795 + 34288 * 2 ^ 59
def prefixEnd_34288 : Nat := 4983230072969 + 3 ^ 40 * 34288 * 2
def baseEnd_34288 : Nat := 3912494373659351498293

theorem tailTrace_34288 : CollatzResearch.WordTrace tailWord_34288 prefixEnd_34288 3912494373659351498293 := by
  unfold tailWord_34288
  simp only [CollatzResearch.WordTrace]
  refine ⟨625293049893953384647759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 833724066525271179530345 625293049893953384647759)
  ·
    refine ⟨937939574840930076971639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 625293049893953384647759 937939574840930076971639)
    ·
      refine ⟨1406909362261395115457459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937939574840930076971639 1406909362261395115457459)
      ·
        refine ⟨2110364043392092673186189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406909362261395115457459 2110364043392092673186189)
        ·
          refine ⟨791386516272034752444821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2110364043392092673186189 791386516272034752444821)
          ·
            refine ⟨37096242950251629020851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 791386516272034752444821 37096242950251629020851)
            ·
              refine ⟨55644364425377443531277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37096242950251629020851 55644364425377443531277)
              ·
                refine ⟨20866636659516541324229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55644364425377443531277 20866636659516541324229)
                ·
                  refine ⟨3912494373659351498293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20866636659516541324229 3912494373659351498293)
                  ·
                    rfl

theorem cell22_34288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_34288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34288 prefixEnd_34288 := by exact prefixLift 34288
  have htrace : WordTrace (prefixWord ++ tailWord_34288) baseStart_34288 baseEnd_34288 := by
    simpa [prefixWord, tailWord_34288, baseEnd_34288] using wordTrace_append hprefix tailTrace_34288
  have hstable : (prefixWord ++ tailWord_34288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34288).length < 2 ^ (prefixWord ++ tailWord_34288).sum := by decide
  have hdescent : baseEnd_34288 < baseStart_34288 := by decide
  rcases family_descends (prefixWord ++ tailWord_34288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34301 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_34301 : Nat := 118140960795 + 34301 * 2 ^ 59
def prefixEnd_34301 : Nat := 4983230072969 + 3 ^ 40 * 34301 * 2
def baseEnd_34301 : Nat := 11741933286650353919839

theorem tailTrace_34301 : CollatzResearch.WordTrace tailWord_34301 prefixEnd_34301 11741933286650353919839 := by
  unfold tailWord_34301
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251060248740809989518757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 834040165827206659679171 1251060248740809989518757)
  ·
    refine ⟨234573796638901873034767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1251060248740809989518757 234573796638901873034767)
    ·
      refine ⟨351860694958352809552151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234573796638901873034767 351860694958352809552151)
      ·
        refine ⟨527791042437529214328227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351860694958352809552151 527791042437529214328227)
        ·
          refine ⟨791686563656293821492341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527791042437529214328227 791686563656293821492341)
          ·
            refine ⟨74220615342777545764907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 791686563656293821492341 74220615342777545764907)
            ·
              refine ⟨111330923014166318647361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74220615342777545764907 111330923014166318647361)
              ·
                refine ⟨83498192260624738985521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111330923014166318647361 83498192260624738985521)
                ·
                  refine ⟨62623644195468554239141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83498192260624738985521 62623644195468554239141)
                  ·
                    refine ⟨11741933286650353919839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62623644195468554239141 11741933286650353919839)
                    ·
                      rfl

theorem cell22_34301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_34301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34301 prefixEnd_34301 := by exact prefixLift 34301
  have htrace : WordTrace (prefixWord ++ tailWord_34301) baseStart_34301 baseEnd_34301 := by
    simpa [prefixWord, tailWord_34301, baseEnd_34301] using wordTrace_append hprefix tailTrace_34301
  have hstable : (prefixWord ++ tailWord_34301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34301).length < 2 ^ (prefixWord ++ tailWord_34301).sum := by decide
  have hdescent : baseEnd_34301 < baseStart_34301 := by decide
  rcases family_descends (prefixWord ++ tailWord_34301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34305 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 4]
def baseStart_34305 : Nat := 118140960795 + 34305 * 2 ^ 59
def prefixEnd_34305 : Nat := 4983230072969 + 3 ^ 40 * 34305 * 2
def baseEnd_34305 : Nat := 3914434189465225606609

theorem tailTrace_34305 : CollatzResearch.WordTrace tailWord_34305 prefixEnd_34305 3914434189465225606609 := by
  unfold tailWord_34305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251206140726318672664369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 834137427150879115109579 1251206140726318672664369)
  ·
    refine ⟨938404605544739004498277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1251206140726318672664369 938404605544739004498277)
    ·
      refine ⟨175950863539638563343427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 938404605544739004498277 175950863539638563343427)
      ·
        refine ⟨263926295309457845015141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175950863539638563343427 263926295309457845015141)
        ·
          refine ⟨49486180370523345940339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263926295309457845015141 49486180370523345940339)
          ·
            refine ⟨74229270555785018910509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49486180370523345940339 74229270555785018910509)
            ·
              refine ⟨27835976458419382091441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74229270555785018910509 27835976458419382091441)
              ·
                refine ⟨20876982343814536568581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27835976458419382091441 20876982343814536568581)
                ·
                  refine ⟨3914434189465225606609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20876982343814536568581 3914434189465225606609)
                  ·
                    rfl

theorem cell22_34305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_34305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34305 prefixEnd_34305 := by exact prefixLift 34305
  have htrace : WordTrace (prefixWord ++ tailWord_34305) baseStart_34305 baseEnd_34305 := by
    simpa [prefixWord, tailWord_34305, baseEnd_34305] using wordTrace_append hprefix tailTrace_34305
  have hstable : (prefixWord ++ tailWord_34305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34305).length < 2 ^ (prefixWord ++ tailWord_34305).sum := by decide
  have hdescent : baseEnd_34305 < baseStart_34305 := by decide
  rcases family_descends (prefixWord ++ tailWord_34305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34316 : List Nat := [2, 2, 1, 2, 5, 1, 2, 7]
def baseStart_34316 : Nat := 118140960795 + 34316 * 2 ^ 59
def prefixEnd_34316 : Nat := 4983230072969 + 3 ^ 40 * 34316 * 2
def baseEnd_34316 : Nat := 1305229788132812754977

theorem tailTrace_34316 : CollatzResearch.WordTrace tailWord_34316 prefixEnd_34316 1305229788132812754977 := by
  unfold tailWord_34316
  simp only [CollatzResearch.WordTrace]
  refine ⟨625803671843233775657401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 834404895790978367543201 625803671843233775657401)
  ·
    refine ⟨469352753882425331743051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 625803671843233775657401 469352753882425331743051)
    ·
      refine ⟨704029130823637997614577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469352753882425331743051 704029130823637997614577)
      ·
        refine ⟨528021848117728498210933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704029130823637997614577 528021848117728498210933)
        ·
          refine ⟨49502048261037046707275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 528021848117728498210933 49502048261037046707275)
          ·
            refine ⟨74253072391555570060913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49502048261037046707275 74253072391555570060913)
            ·
              refine ⟨55689804293666677545685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74253072391555570060913 55689804293666677545685)
              ·
                refine ⟨1305229788132812754977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55689804293666677545685 1305229788132812754977)
                ·
                  rfl

theorem cell22_34316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_34316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34316 prefixEnd_34316 := by exact prefixLift 34316
  have htrace : WordTrace (prefixWord ++ tailWord_34316) baseStart_34316 baseEnd_34316 := by
    simpa [prefixWord, tailWord_34316, baseEnd_34316] using wordTrace_append hprefix tailTrace_34316
  have hstable : (prefixWord ++ tailWord_34316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34316).length < 2 ^ (prefixWord ++ tailWord_34316).sum := by decide
  have hdescent : baseEnd_34316 < baseStart_34316 := by decide
  rcases family_descends (prefixWord ++ tailWord_34316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34361 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 5]
def baseStart_34361 : Nat := 118140960795 + 34361 * 2 ^ 59
def prefixEnd_34361 : Nat := 4983230072969 + 3 ^ 40 * 34361 * 2
def baseEnd_34361 : Nat := 3920824170943399139885

theorem tailTrace_34361 : CollatzResearch.WordTrace tailWord_34361 prefixEnd_34361 3920824170943399139885 := by
  unfold tailWord_34361
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253248628523440236702937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 835499085682293491135291 1253248628523440236702937)
  ·
    refine ⟨939936471392580177527203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1253248628523440236702937 939936471392580177527203)
    ·
      refine ⟨1409904707088870266290805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939936471392580177527203 1409904707088870266290805)
      ·
        refine ⟨132178566289581587464763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1409904707088870266290805 132178566289581587464763)
        ·
          refine ⟨198267849434372381197145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132178566289581587464763 198267849434372381197145)
          ·
            refine ⟨148700887075779285897859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198267849434372381197145 148700887075779285897859)
            ·
              refine ⟨223051330613668928846789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148700887075779285897859 223051330613668928846789)
              ·
                refine ⟨41822124490062924158773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223051330613668928846789 41822124490062924158773)
                ·
                  refine ⟨3920824170943399139885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41822124490062924158773 3920824170943399139885)
                  ·
                    rfl

theorem cell22_34361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_34361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34361 prefixEnd_34361 := by exact prefixLift 34361
  have htrace : WordTrace (prefixWord ++ tailWord_34361) baseStart_34361 baseEnd_34361 := by
    simpa [prefixWord, tailWord_34361, baseEnd_34361] using wordTrace_append hprefix tailTrace_34361
  have hstable : (prefixWord ++ tailWord_34361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34361).length < 2 ^ (prefixWord ++ tailWord_34361).sum := by decide
  have hdescent : baseEnd_34361 < baseStart_34361 := by decide
  rcases family_descends (prefixWord ++ tailWord_34361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34391 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 3, 4]
def baseStart_34391 : Nat := 118140960795 + 34391 * 2 ^ 59
def prefixEnd_34391 : Nat := 4983230072969 + 3 ^ 40 * 34391 * 2
def baseEnd_34391 : Nat := 11772742125920119169563

theorem tailTrace_34391 : CollatzResearch.WordTrace tailWord_34391 prefixEnd_34391 11772742125920119169563 := by
  unfold tailWord_34391
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254342818414755360295027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 836228545609836906863351 1254342818414755360295027)
  ·
    refine ⟨1881514227622133040442541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1254342818414755360295027 1881514227622133040442541)
    ·
      refine ⟨705567835358299890165953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1881514227622133040442541 705567835358299890165953)
      ·
        refine ⟨529175876518724917624465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 705567835358299890165953 529175876518724917624465)
        ·
          refine ⟨396881907389043688218349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529175876518724917624465 396881907389043688218349)
          ·
            refine ⟨148830715270891383081881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396881907389043688218349 148830715270891383081881)
            ·
              refine ⟨111623036453168537311411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148830715270891383081881 111623036453168537311411)
              ·
                refine ⟨167434554679752805967117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111623036453168537311411 167434554679752805967117)
                ·
                  refine ⟨62787958004907302237669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167434554679752805967117 62787958004907302237669)
                  ·
                    refine ⟨11772742125920119169563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62787958004907302237669 11772742125920119169563)
                    ·
                      rfl

theorem cell22_34391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_34391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34391 prefixEnd_34391 := by exact prefixLift 34391
  have htrace : WordTrace (prefixWord ++ tailWord_34391) baseStart_34391 baseEnd_34391 := by
    simpa [prefixWord, tailWord_34391, baseEnd_34391] using wordTrace_append hprefix tailTrace_34391
  have hstable : (prefixWord ++ tailWord_34391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34391).length < 2 ^ (prefixWord ++ tailWord_34391).sum := by decide
  have hdescent : baseEnd_34391 < baseStart_34391 := by decide
  rcases family_descends (prefixWord ++ tailWord_34391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34588 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_34588 : Nat := 118140960795 + 34588 * 2 ^ 59
def prefixEnd_34588 : Nat := 4983230072969 + 3 ^ 40 * 34588 * 2
def baseEnd_34588 : Nat := 11840179251877271993959

theorem tailTrace_34588 : CollatzResearch.WordTrace tailWord_34588 prefixEnd_34588 11840179251877271993959 := by
  unfold tailWord_34588
  simp only [CollatzResearch.WordTrace]
  refine ⟨630763999350529002608209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 841018665800705336810945 630763999350529002608209)
  ·
    refine ⟨473072999512896751956157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 630763999350529002608209 473072999512896751956157)
    ·
      refine ⟨177402374817336281983559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 473072999512896751956157 177402374817336281983559)
      ·
        refine ⟨266103562226004422975339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177402374817336281983559 266103562226004422975339)
        ·
          refine ⟨399155343339006634463009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266103562226004422975339 399155343339006634463009)
          ·
            refine ⟨299366507504254975847257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399155343339006634463009 299366507504254975847257)
            ·
              refine ⟨224524880628191231885443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299366507504254975847257 224524880628191231885443)
              ·
                refine ⟨336787320942286847828165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224524880628191231885443 336787320942286847828165)
                ·
                  refine ⟨63147622676678783967781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 336787320942286847828165 63147622676678783967781)
                  ·
                    refine ⟨11840179251877271993959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63147622676678783967781 11840179251877271993959)
                    ·
                      rfl

theorem cell22_34588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_34588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34588 prefixEnd_34588 := by exact prefixLift 34588
  have htrace : WordTrace (prefixWord ++ tailWord_34588) baseStart_34588 baseEnd_34588 := by
    simpa [prefixWord, tailWord_34588, baseEnd_34588] using wordTrace_append hprefix tailTrace_34588
  have hstable : (prefixWord ++ tailWord_34588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34588).length < 2 ^ (prefixWord ++ tailWord_34588).sum := by decide
  have hdescent : baseEnd_34588 < baseStart_34588 := by decide
  rcases family_descends (prefixWord ++ tailWord_34588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_34601 : Nat := 118140960795 + 34601 * 2 ^ 59
def prefixEnd_34601 : Nat := 4983230072969 + 3 ^ 40 * 34601 * 2
def baseEnd_34601 : Nat := 11844629417549571418919

theorem tailTrace_34601 : CollatzResearch.WordTrace tailWord_34601 prefixEnd_34601 11844629417549571418919 := by
  unfold tailWord_34601
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262002147653961225439657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 841334765102640816959771 1262002147653961225439657)
  ·
    refine ⟨946501610740470919079743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1262002147653961225439657 946501610740470919079743)
    ·
      refine ⟨1419752416110706378619615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946501610740470919079743 1419752416110706378619615)
      ·
        refine ⟨2129628624166059567929423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419752416110706378619615 2129628624166059567929423)
        ·
          refine ⟨3194442936249089351894135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129628624166059567929423 3194442936249089351894135)
          ·
            refine ⟨4791664404373634027841203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194442936249089351894135 4791664404373634027841203)
            ·
              refine ⟨7187496606560451041761805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791664404373634027841203 7187496606560451041761805)
              ·
                refine ⟨2695311227460169140660677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7187496606560451041761805 2695311227460169140660677)
                ·
                  refine ⟨505370855148781713873877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2695311227460169140660677 505370855148781713873877)
                  ·
                    refine ⟨11844629417549571418919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 505370855148781713873877 11844629417549571418919)
                    ·
                      rfl

theorem cell22_34601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_34601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34601 prefixEnd_34601 := by exact prefixLift 34601
  have htrace : WordTrace (prefixWord ++ tailWord_34601) baseStart_34601 baseEnd_34601 := by
    simpa [prefixWord, tailWord_34601, baseEnd_34601] using wordTrace_append hprefix tailTrace_34601
  have hstable : (prefixWord ++ tailWord_34601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34601).length < 2 ^ (prefixWord ++ tailWord_34601).sum := by decide
  have hdescent : baseEnd_34601 < baseStart_34601 := by decide
  rcases family_descends (prefixWord ++ tailWord_34601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34663 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_34663 : Nat := 118140960795 + 34663 * 2 ^ 59
def prefixEnd_34663 : Nat := 4983230072969 + 3 ^ 40 * 34663 * 2
def baseEnd_34663 : Nat := 11865853284602076368729

theorem tailTrace_34663 : CollatzResearch.WordTrace tailWord_34663 prefixEnd_34663 11865853284602076368729 := by
  unfold tailWord_34663
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264263473429345814196643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 842842315619563876131095 1264263473429345814196643)
  ·
    refine ⟨1896395210144018721294965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264263473429345814196643 1896395210144018721294965)
    ·
      refine ⟨177787050951001755121403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1896395210144018721294965 177787050951001755121403)
      ·
        refine ⟨266680576426502632682105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177787050951001755121403 266680576426502632682105)
        ·
          refine ⟨200010432319876974511579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266680576426502632682105 200010432319876974511579)
          ·
            refine ⟨300015648479815461767369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200010432319876974511579 300015648479815461767369)
            ·
              refine ⟨225011736359861596325527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300015648479815461767369 225011736359861596325527)
              ·
                refine ⟨337517604539792394488291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225011736359861596325527 337517604539792394488291)
                ·
                  refine ⟨506276406809688591732437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337517604539792394488291 506276406809688591732437)
                  ·
                    refine ⟨11865853284602076368729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 506276406809688591732437 11865853284602076368729)
                    ·
                      rfl

theorem cell22_34663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_34663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34663 prefixEnd_34663 := by exact prefixLift 34663
  have htrace : WordTrace (prefixWord ++ tailWord_34663) baseStart_34663 baseEnd_34663 := by
    simpa [prefixWord, tailWord_34663, baseEnd_34663] using wordTrace_append hprefix tailTrace_34663
  have hstable : (prefixWord ++ tailWord_34663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34663).length < 2 ^ (prefixWord ++ tailWord_34663).sum := by decide
  have hdescent : baseEnd_34663 < baseStart_34663 := by decide
  rcases family_descends (prefixWord ++ tailWord_34663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34723 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_34723 : Nat := 118140960795 + 34723 * 2 ^ 59
def prefixEnd_34723 : Nat := 4983230072969 + 3 ^ 40 * 34723 * 2
def baseEnd_34723 : Nat := 11886392510781919868545

theorem tailTrace_34723 : CollatzResearch.WordTrace tailWord_34723 prefixEnd_34723 11886392510781919868545 := by
  unfold tailWord_34723
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266451853211976061380823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 844301235474650707587215 1266451853211976061380823)
  ·
    refine ⟨1899677779817964092071235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1266451853211976061380823 1899677779817964092071235)
    ·
      refine ⟨2849516669726946138106853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1899677779817964092071235 2849516669726946138106853)
      ·
        refine ⟨534284375573802400895035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2849516669726946138106853 534284375573802400895035)
        ·
          refine ⟨801426563360703601342553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534284375573802400895035 801426563360703601342553)
          ·
            refine ⟨601069922520527701006915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801426563360703601342553 601069922520527701006915)
            ·
              refine ⟨901604883780791551510373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601069922520527701006915 901604883780791551510373)
              ·
                refine ⟨169050915708898415908195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 901604883780791551510373 169050915708898415908195)
                ·
                  refine ⟨253576373563347623862293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169050915708898415908195 253576373563347623862293)
                  ·
                    refine ⟨11886392510781919868545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 253576373563347623862293 11886392510781919868545)
                    ·
                      rfl

theorem cell22_34723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_34723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34723 prefixEnd_34723 := by exact prefixLift 34723
  have htrace : WordTrace (prefixWord ++ tailWord_34723) baseStart_34723 baseEnd_34723 := by
    simpa [prefixWord, tailWord_34723, baseEnd_34723] using wordTrace_append hprefix tailTrace_34723
  have hstable : (prefixWord ++ tailWord_34723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34723).length < 2 ^ (prefixWord ++ tailWord_34723).sum := by decide
  have hdescent : baseEnd_34723 < baseStart_34723 := by decide
  rcases family_descends (prefixWord ++ tailWord_34723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34738 : List Nat := [3, 2, 1, 1, 1, 1, 1, 12]
def baseStart_34738 : Nat := 118140960795 + 34738 * 2 ^ 59
def prefixEnd_34738 : Nat := 4983230072969 + 3 ^ 40 * 34738 * 2
def baseEnd_34738 : Nat := 1321280813036320082611

theorem tailTrace_34738 : CollatzResearch.WordTrace tailWord_34738 prefixEnd_34738 1321280813036320082611 := by
  unfold tailWord_34738
  simp only [CollatzResearch.WordTrace]
  refine ⟨316749737039408405794217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 844665965438422415451245 316749737039408405794217)
  ·
    refine ⟨237562302779556304345663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 316749737039408405794217 237562302779556304345663)
    ·
      refine ⟨356343454169334456518495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237562302779556304345663 356343454169334456518495)
      ·
        refine ⟨534515181254001684777743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356343454169334456518495 534515181254001684777743)
        ·
          refine ⟨801772771881002527166615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534515181254001684777743 801772771881002527166615)
          ·
            refine ⟨1202659157821503790749923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801772771881002527166615 1202659157821503790749923)
            ·
              refine ⟨1803988736732255686124885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202659157821503790749923 1803988736732255686124885)
              ·
                refine ⟨1321280813036320082611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 1803988736732255686124885 1321280813036320082611)
                ·
                  rfl

theorem cell22_34738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_34738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34738 prefixEnd_34738 := by exact prefixLift 34738
  have htrace : WordTrace (prefixWord ++ tailWord_34738) baseStart_34738 baseEnd_34738 := by
    simpa [prefixWord, tailWord_34738, baseEnd_34738] using wordTrace_append hprefix tailTrace_34738
  have hstable : (prefixWord ++ tailWord_34738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34738).length < 2 ^ (prefixWord ++ tailWord_34738).sum := by decide
  have hdescent : baseEnd_34738 < baseStart_34738 := by decide
  rcases family_descends (prefixWord ++ tailWord_34738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34768 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_34768 : Nat := 118140960795 + 34768 * 2 ^ 59
def prefixEnd_34768 : Nat := 4983230072969 + 3 ^ 40 * 34768 * 2
def baseEnd_34768 : Nat := 11901796930416802493407

theorem tailTrace_34768 : CollatzResearch.WordTrace tailWord_34768 prefixEnd_34768 11901796930416802493407 := by
  unfold tailWord_34768
  simp only [CollatzResearch.WordTrace]
  refine ⟨634046569024474373384479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 845395425365965831179305 634046569024474373384479)
  ·
    refine ⟨951069853536711560076719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634046569024474373384479 951069853536711560076719)
    ·
      refine ⟨1426604780305067340115079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 951069853536711560076719 1426604780305067340115079)
      ·
        refine ⟨2139907170457601010172619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426604780305067340115079 2139907170457601010172619)
        ·
          refine ⟨3209860755686401515258929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139907170457601010172619 3209860755686401515258929)
          ·
            refine ⟨2407395566764801136444197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209860755686401515258929 2407395566764801136444197)
            ·
              refine ⟨451386668768400213083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2407395566764801136444197 451386668768400213083287)
              ·
                refine ⟨677080003152600319624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451386668768400213083287 677080003152600319624931)
                ·
                  refine ⟨1015620004728900479437397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677080003152600319624931 1015620004728900479437397)
                  ·
                    refine ⟨11901796930416802493407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1015620004728900479437397 11901796930416802493407)
                    ·
                      rfl

theorem cell22_34768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_34768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34768 prefixEnd_34768 := by exact prefixLift 34768
  have htrace : WordTrace (prefixWord ++ tailWord_34768) baseStart_34768 baseEnd_34768 := by
    simpa [prefixWord, tailWord_34768, baseEnd_34768] using wordTrace_append hprefix tailTrace_34768
  have hstable : (prefixWord ++ tailWord_34768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34768).length < 2 ^ (prefixWord ++ tailWord_34768).sum := by decide
  have hdescent : baseEnd_34768 < baseStart_34768 := by decide
  rcases family_descends (prefixWord ++ tailWord_34768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34787 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 3, 3]
def baseStart_34787 : Nat := 118140960795 + 34787 * 2 ^ 59
def prefixEnd_34787 : Nat := 4983230072969 + 3 ^ 40 * 34787 * 2
def baseEnd_34787 : Nat := 11908301018707086268349

theorem tailTrace_34787 : CollatzResearch.WordTrace tailWord_34787 prefixEnd_34787 11908301018707086268349 := by
  unfold tailWord_34787
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268786124980114991710615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 845857416653409994473743 1268786124980114991710615)
  ·
    refine ⟨1903179187470172487565923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268786124980114991710615 1903179187470172487565923)
    ·
      refine ⟨2854768781205258731348885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903179187470172487565923 2854768781205258731348885)
      ·
        refine ⟨133817286618996503031979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2854768781205258731348885 133817286618996503031979)
        ·
          refine ⟨200725929928494754547969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133817286618996503031979 200725929928494754547969)
          ·
            refine ⟨150544447446371065910977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200725929928494754547969 150544447446371065910977)
            ·
              refine ⟨112908335584778299433233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150544447446371065910977 112908335584778299433233)
              ·
                refine ⟨84681251688583724574925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112908335584778299433233 84681251688583724574925)
                ·
                  refine ⟨31755469383218896715597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84681251688583724574925 31755469383218896715597)
                  ·
                    refine ⟨11908301018707086268349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31755469383218896715597 11908301018707086268349)
                    ·
                      rfl

theorem cell22_34787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 3].length) (baseStart_34787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34787 prefixEnd_34787 := by exact prefixLift 34787
  have htrace : WordTrace (prefixWord ++ tailWord_34787) baseStart_34787 baseEnd_34787 := by
    simpa [prefixWord, tailWord_34787, baseEnd_34787] using wordTrace_append hprefix tailTrace_34787
  have hstable : (prefixWord ++ tailWord_34787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34787).length < 2 ^ (prefixWord ++ tailWord_34787).sum := by decide
  have hdescent : baseEnd_34787 < baseStart_34787 := by decide
  rcases family_descends (prefixWord ++ tailWord_34787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34821 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_34821 : Nat := 118140960795 + 34821 * 2 ^ 59
def prefixEnd_34821 : Nat := 4983230072969 + 3 ^ 40 * 34821 * 2
def baseEnd_34821 : Nat := 11919939913542330918245

theorem tailTrace_34821 : CollatzResearch.WordTrace tailWord_34821 prefixEnd_34821 11919939913542330918245 := by
  unfold tailWord_34821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270026206856938798448317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 846684137904625865632211 1270026206856938798448317)
  ·
    refine ⟨476259827571352049418119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1270026206856938798448317 476259827571352049418119)
    ·
      refine ⟨714389741357028074127179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476259827571352049418119 714389741357028074127179)
      ·
        refine ⟨1071584612035542111190769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714389741357028074127179 1071584612035542111190769)
        ·
          refine ⟨803688459026656583393077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1071584612035542111190769 803688459026656583393077)
          ·
            refine ⟨75345793033749054693101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 803688459026656583393077 75345793033749054693101)
            ·
              refine ⟨28254672387655895509913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75345793033749054693101 28254672387655895509913)
              ·
                refine ⟨21191004290741921632435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28254672387655895509913 21191004290741921632435)
                ·
                  refine ⟨31786506436112882448653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21191004290741921632435 31786506436112882448653)
                  ·
                    refine ⟨11919939913542330918245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31786506436112882448653 11919939913542330918245)
                    ·
                      rfl

theorem cell22_34821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_34821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34821 prefixEnd_34821 := by exact prefixLift 34821
  have htrace : WordTrace (prefixWord ++ tailWord_34821) baseStart_34821 baseEnd_34821 := by
    simpa [prefixWord, tailWord_34821, baseEnd_34821] using wordTrace_append hprefix tailTrace_34821
  have hstable : (prefixWord ++ tailWord_34821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34821).length < 2 ^ (prefixWord ++ tailWord_34821).sum := by decide
  have hdescent : baseEnd_34821 < baseStart_34821 := by decide
  rcases family_descends (prefixWord ++ tailWord_34821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34864 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 1, 4]
def baseStart_34864 : Nat := 118140960795 + 34864 * 2 ^ 59
def prefixEnd_34864 : Nat := 4983230072969 + 3 ^ 40 * 34864 * 2
def baseEnd_34864 : Nat := 11934659692304552093113

theorem tailTrace_34864 : CollatzResearch.WordTrace tailWord_34864 prefixEnd_34864 11934659692304552093113 := by
  unfold tailWord_34864
  simp only [CollatzResearch.WordTrace]
  refine ⟨635797272850578571131823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 847729697134104761509097 635797272850578571131823)
  ·
    refine ⟨953695909275867856697735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 635797272850578571131823 953695909275867856697735)
    ·
      refine ⟨1430543863913801785046603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953695909275867856697735 1430543863913801785046603)
      ·
        refine ⟨2145815795870702677569905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430543863913801785046603 2145815795870702677569905)
        ·
          refine ⟨1609361846903027008177429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2145815795870702677569905 1609361846903027008177429)
          ·
            refine ⟨75438836573579391008317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1609361846903027008177429 75438836573579391008317)
            ·
              refine ⟨28289563715092271628119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75438836573579391008317 28289563715092271628119)
              ·
                refine ⟨42434345572638407442179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28289563715092271628119 42434345572638407442179)
                ·
                  refine ⟨63651518358957611163269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42434345572638407442179 63651518358957611163269)
                  ·
                    refine ⟨11934659692304552093113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63651518358957611163269 11934659692304552093113)
                    ·
                      rfl

theorem cell22_34864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_34864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34864 prefixEnd_34864 := by exact prefixLift 34864
  have htrace : WordTrace (prefixWord ++ tailWord_34864) baseStart_34864 baseEnd_34864 := by
    simpa [prefixWord, tailWord_34864, baseEnd_34864] using wordTrace_append hprefix tailTrace_34864
  have hstable : (prefixWord ++ tailWord_34864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34864).length < 2 ^ (prefixWord ++ tailWord_34864).sum := by decide
  have hdescent : baseEnd_34864 < baseStart_34864 := by decide
  rcases family_descends (prefixWord ++ tailWord_34864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34879 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 4]
def baseStart_34879 : Nat := 118140960795 + 34879 * 2 ^ 59
def prefixEnd_34879 : Nat := 4983230072969 + 3 ^ 40 * 34879 * 2
def baseEnd_34879 : Nat := 3979931499616504322689

theorem tailTrace_34879 : CollatzResearch.WordTrace tailWord_34879 prefixEnd_34879 3979931499616504322689 := by
  unfold tailWord_34879
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272141640646814704059691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 848094427097876469373127 1272141640646814704059691)
  ·
    refine ⟨1908212460970222056089537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1272141640646814704059691 1908212460970222056089537)
    ·
      refine ⟨1431159345727666542067153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1908212460970222056089537 1431159345727666542067153)
      ·
        refine ⟨1073369509295749906550365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1431159345727666542067153 1073369509295749906550365)
        ·
          refine ⟨402513565985906214956387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1073369509295749906550365 402513565985906214956387)
          ·
            refine ⟨603770348978859322434581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402513565985906214956387 603770348978859322434581)
            ·
              refine ⟨28301735108384030739121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 603770348978859322434581 28301735108384030739121)
              ·
                refine ⟨21226301331288023054341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28301735108384030739121 21226301331288023054341)
                ·
                  refine ⟨3979931499616504322689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21226301331288023054341 3979931499616504322689)
                  ·
                    rfl

theorem cell22_34879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 4].length) (baseStart_34879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34879 prefixEnd_34879 := by exact prefixLift 34879
  have htrace : WordTrace (prefixWord ++ tailWord_34879) baseStart_34879 baseEnd_34879 := by
    simpa [prefixWord, tailWord_34879, baseEnd_34879] using wordTrace_append hprefix tailTrace_34879
  have hstable : (prefixWord ++ tailWord_34879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34879).length < 2 ^ (prefixWord ++ tailWord_34879).sum := by decide
  have hdescent : baseEnd_34879 < baseStart_34879 := by decide
  rcases family_descends (prefixWord ++ tailWord_34879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34894 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_34894 : Nat := 118140960795 + 34894 * 2 ^ 59
def prefixEnd_34894 : Nat := 4983230072969 + 3 ^ 40 * 34894 * 2
def baseEnd_34894 : Nat := 11944929305394473843021

theorem tailTrace_34894 : CollatzResearch.WordTrace tailWord_34894 prefixEnd_34894 11944929305394473843021 := by
  unfold tailWord_34894
  simp only [CollatzResearch.WordTrace]
  refine ⟨159086091949059033231967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 848459157061648177237157 159086091949059033231967)
  ·
    refine ⟨238629137923588549847951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159086091949059033231967 238629137923588549847951)
    ·
      refine ⟨357943706885382824771927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238629137923588549847951 357943706885382824771927)
      ·
        refine ⟨536915560328074237157891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357943706885382824771927 536915560328074237157891)
        ·
          refine ⟨805373340492111355736837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536915560328074237157891 805373340492111355736837)
          ·
            refine ⟨151007501342270879200657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 805373340492111355736837 151007501342270879200657)
            ·
              refine ⟨113255626006703159400493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151007501342270879200657 113255626006703159400493)
              ·
                refine ⟨42470859752513684775185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113255626006703159400493 42470859752513684775185)
                ·
                  refine ⟨31853144814385263581389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42470859752513684775185 31853144814385263581389)
                  ·
                    refine ⟨11944929305394473843021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31853144814385263581389 11944929305394473843021)
                    ·
                      rfl

theorem cell22_34894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_34894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34894 prefixEnd_34894 := by exact prefixLift 34894
  have htrace : WordTrace (prefixWord ++ tailWord_34894) baseStart_34894 baseEnd_34894 := by
    simpa [prefixWord, tailWord_34894, baseEnd_34894] using wordTrace_append hprefix tailTrace_34894
  have hstable : (prefixWord ++ tailWord_34894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34894).length < 2 ^ (prefixWord ++ tailWord_34894).sum := by decide
  have hdescent : baseEnd_34894 < baseStart_34894 := by decide
  rcases family_descends (prefixWord ++ tailWord_34894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34909 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_34909 : Nat := 118140960795 + 34909 * 2 ^ 59
def prefixEnd_34909 : Nat := 4983230072969 + 3 ^ 40 * 34909 * 2
def baseEnd_34909 : Nat := 11950064111939434717975

theorem tailTrace_34909 : CollatzResearch.WordTrace tailWord_34909 prefixEnd_34909 11950064111939434717975 := by
  unfold tailWord_34909
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273235830538129827651781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 848823887025419885101187 1273235830538129827651781)
  ·
    refine ⟨238731718225899342684709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1273235830538129827651781 238731718225899342684709)
    ·
      refine ⟨44762197167356126753383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238731718225899342684709 44762197167356126753383)
      ·
        refine ⟨67143295751034190130075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44762197167356126753383 67143295751034190130075)
        ·
          refine ⟨100714943626551285195113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67143295751034190130075 100714943626551285195113)
          ·
            refine ⟨75536207719913463896335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100714943626551285195113 75536207719913463896335)
            ·
              refine ⟨113304311579870195844503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75536207719913463896335 113304311579870195844503)
              ·
                refine ⟨169956467369805293766755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113304311579870195844503 169956467369805293766755)
                ·
                  refine ⟨254934701054707940650133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169956467369805293766755 254934701054707940650133)
                  ·
                    refine ⟨11950064111939434717975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 254934701054707940650133 11950064111939434717975)
                    ·
                      rfl

theorem cell22_34909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_34909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34909 prefixEnd_34909 := by exact prefixLift 34909
  have htrace : WordTrace (prefixWord ++ tailWord_34909) baseStart_34909 baseEnd_34909 := by
    simpa [prefixWord, tailWord_34909, baseEnd_34909] using wordTrace_append hprefix tailTrace_34909
  have hstable : (prefixWord ++ tailWord_34909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34909).length < 2 ^ (prefixWord ++ tailWord_34909).sum := by decide
  have hdescent : baseEnd_34909 < baseStart_34909 := by decide
  rcases family_descends (prefixWord ++ tailWord_34909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34973 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_34973 : Nat := 118140960795 + 34973 * 2 ^ 59
def prefixEnd_34973 : Nat := 4983230072969 + 3 ^ 40 * 34973 * 2
def baseEnd_34973 : Nat := 11971972619864601117779

theorem tailTrace_34973 : CollatzResearch.WordTrace tailWord_34973 prefixEnd_34973 11971972619864601117779 := by
  unfold tailWord_34973
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275570102306268757981573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 850380068204179171987715 1275570102306268757981573)
  ·
    refine ⟨239169394182425392121545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1275570102306268757981573 239169394182425392121545)
    ·
      refine ⟨179377045636819044091159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239169394182425392121545 179377045636819044091159)
      ·
        refine ⟨269065568455228566136739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179377045636819044091159 269065568455228566136739)
        ·
          refine ⟨403598352682842849205109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269065568455228566136739 403598352682842849205109)
          ·
            refine ⟨37837345564016517112979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 403598352682842849205109 37837345564016517112979)
            ·
              refine ⟨56756018346024775669469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37837345564016517112979 56756018346024775669469)
              ·
                refine ⟨21283506879759290876051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56756018346024775669469 21283506879759290876051)
                ·
                  refine ⟨31925260319638936314077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21283506879759290876051 31925260319638936314077)
                  ·
                    refine ⟨11971972619864601117779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31925260319638936314077 11971972619864601117779)
                    ·
                      rfl

theorem cell22_34973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_34973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34973 prefixEnd_34973 := by exact prefixLift 34973
  have htrace : WordTrace (prefixWord ++ tailWord_34973) baseStart_34973 baseEnd_34973 := by
    simpa [prefixWord, tailWord_34973, baseEnd_34973] using wordTrace_append hprefix tailTrace_34973
  have hstable : (prefixWord ++ tailWord_34973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34973).length < 2 ^ (prefixWord ++ tailWord_34973).sum := by decide
  have hdescent : baseEnd_34973 < baseStart_34973 := by decide
  rcases family_descends (prefixWord ++ tailWord_34973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34990 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_34990 : Nat := 118140960795 + 34990 * 2 ^ 59
def prefixEnd_34990 : Nat := 4983230072969 + 3 ^ 40 * 34990 * 2
def baseEnd_34990 : Nat := 11977792067282223442727

theorem tailTrace_34990 : CollatzResearch.WordTrace tailWord_34990 prefixEnd_34990 11977792067282223442727 := by
  unfold tailWord_34990
  simp only [CollatzResearch.WordTrace]
  refine ⟨159523767905585082668803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 850793428829787107566949 159523767905585082668803)
  ·
    refine ⟨239285651858377624003205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159523767905585082668803 239285651858377624003205)
    ·
      refine ⟨44866059723445804500601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239285651858377624003205 44866059723445804500601)
      ·
        refine ⟨33649544792584353375451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44866059723445804500601 33649544792584353375451)
        ·
          refine ⟨50474317188876530063177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33649544792584353375451 50474317188876530063177)
          ·
            refine ⟨37855737891657397547383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50474317188876530063177 37855737891657397547383)
            ·
              refine ⟨56783606837486096321075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37855737891657397547383 56783606837486096321075)
              ·
                refine ⟨85175410256229144481613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56783606837486096321075 85175410256229144481613)
                ·
                  refine ⟨31940778846085929180605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85175410256229144481613 31940778846085929180605)
                  ·
                    refine ⟨11977792067282223442727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31940778846085929180605 11977792067282223442727)
                    ·
                      rfl

theorem cell22_34990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_34990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_34990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_34990 prefixEnd_34990 := by exact prefixLift 34990
  have htrace : WordTrace (prefixWord ++ tailWord_34990) baseStart_34990 baseEnd_34990 := by
    simpa [prefixWord, tailWord_34990, baseEnd_34990] using wordTrace_append hprefix tailTrace_34990
  have hstable : (prefixWord ++ tailWord_34990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34990).length < 2 ^ (prefixWord ++ tailWord_34990).sum := by decide
  have hdescent : baseEnd_34990 < baseStart_34990 := by decide
  rcases family_descends (prefixWord ++ tailWord_34990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35048 : List Nat := [2, 1, 4, 1, 2, 4, 2, 2, 4]
def baseStart_35048 : Nat := 118140960795 + 35048 * 2 ^ 59
def prefixEnd_35048 : Nat := 4983230072969 + 3 ^ 40 * 35048 * 2
def baseEnd_35048 : Nat := 3999215550863135164183

theorem tailTrace_35048 : CollatzResearch.WordTrace tailWord_35048 prefixEnd_35048 3999215550863135164183 := by
  unfold tailWord_35048
  simp only [CollatzResearch.WordTrace]
  refine ⟨639152788517278283480899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 852203718023037711307865 639152788517278283480899)
  ·
    refine ⟨958729182775917425221349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 639152788517278283480899 958729182775917425221349)
    ·
      refine ⟨179761721770484517229003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 958729182775917425221349 179761721770484517229003)
      ·
        refine ⟨269642582655726775843505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179761721770484517229003 269642582655726775843505)
        ·
          refine ⟨202231936991795081882629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269642582655726775843505 202231936991795081882629)
          ·
            refine ⟨37918488185961577852993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202231936991795081882629 37918488185961577852993)
            ·
              refine ⟨28438866139471183389745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37918488185961577852993 28438866139471183389745)
              ·
                refine ⟨21329149604603387542309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28438866139471183389745 21329149604603387542309)
                ·
                  refine ⟨3999215550863135164183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21329149604603387542309 3999215550863135164183)
                  ·
                    rfl

theorem cell22_35048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_35048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35048 prefixEnd_35048 := by exact prefixLift 35048
  have htrace : WordTrace (prefixWord ++ tailWord_35048) baseStart_35048 baseEnd_35048 := by
    simpa [prefixWord, tailWord_35048, baseEnd_35048] using wordTrace_append hprefix tailTrace_35048
  have hstable : (prefixWord ++ tailWord_35048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35048).length < 2 ^ (prefixWord ++ tailWord_35048).sum := by decide
  have hdescent : baseEnd_35048 < baseStart_35048 := by decide
  rcases family_descends (prefixWord ++ tailWord_35048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35076 : List Nat := [2, 3, 2, 2, 3, 1, 3, 6]
def baseStart_35076 : Nat := 118140960795 + 35076 * 2 ^ 59
def prefixEnd_35076 : Nat := 4983230072969 + 3 ^ 40 * 35076 * 2
def baseEnd_35076 : Nat := 1334136847200740643607

theorem tailTrace_35076 : CollatzResearch.WordTrace tailWord_35076 prefixEnd_35076 1334136847200740643607 := by
  unfold tailWord_35076
  simp only [CollatzResearch.WordTrace]
  refine ⟨639663410466558674490541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 852884547288744899320721 639663410466558674490541)
  ·
    refine ⟨239873778924959502933953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 639663410466558674490541 239873778924959502933953)
    ·
      refine ⟨179905334193719627200465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239873778924959502933953 179905334193719627200465)
      ·
        refine ⟨134929000645289720400349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179905334193719627200465 134929000645289720400349)
        ·
          refine ⟨50598375241983645150131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134929000645289720400349 50598375241983645150131)
          ·
            refine ⟨75897562862975467725197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50598375241983645150131 75897562862975467725197)
            ·
              refine ⟨28461586073615800396949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75897562862975467725197 28461586073615800396949)
              ·
                refine ⟨1334136847200740643607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28461586073615800396949 1334136847200740643607)
                ·
                  rfl

theorem cell22_35076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 6].length) (baseStart_35076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35076 prefixEnd_35076 := by exact prefixLift 35076
  have htrace : WordTrace (prefixWord ++ tailWord_35076) baseStart_35076 baseEnd_35076 := by
    simpa [prefixWord, tailWord_35076, baseEnd_35076] using wordTrace_append hprefix tailTrace_35076
  have hstable : (prefixWord ++ tailWord_35076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35076).length < 2 ^ (prefixWord ++ tailWord_35076).sum := by decide
  have hdescent : baseEnd_35076 < baseStart_35076 := by decide
  rcases family_descends (prefixWord ++ tailWord_35076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35104 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_35104 : Nat := 118140960795 + 35104 * 2 ^ 59
def prefixEnd_35104 : Nat := 4983230072969 + 3 ^ 40 * 35104 * 2
def baseEnd_35104 : Nat := 4005605532341308697459

theorem tailTrace_35104 : CollatzResearch.WordTrace tailWord_35104 prefixEnd_35104 4005605532341308697459 := by
  unfold tailWord_35104
  simp only [CollatzResearch.WordTrace]
  refine ⟨640174032415839065500183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 853565376554452087333577 640174032415839065500183)
  ·
    refine ⟨960261048623758598250275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640174032415839065500183 960261048623758598250275)
    ·
      refine ⟨1440391572935637897375413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960261048623758598250275 1440391572935637897375413)
      ·
        refine ⟨135036709962716052878945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1440391572935637897375413 135036709962716052878945)
        ·
          refine ⟨101277532472037039659209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135036709962716052878945 101277532472037039659209)
          ·
            refine ⟨75958149354027779744407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101277532472037039659209 75958149354027779744407)
            ·
              refine ⟨113937224031041669616611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75958149354027779744407 113937224031041669616611)
              ·
                refine ⟨170905836046562504424917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113937224031041669616611 170905836046562504424917)
                ·
                  refine ⟨4005605532341308697459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 170905836046562504424917 4005605532341308697459)
                  ·
                    rfl

theorem cell22_35104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_35104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35104 prefixEnd_35104 := by exact prefixLift 35104
  have htrace : WordTrace (prefixWord ++ tailWord_35104) baseStart_35104 baseEnd_35104 := by
    simpa [prefixWord, tailWord_35104, baseEnd_35104] using wordTrace_append hprefix tailTrace_35104
  have hstable : (prefixWord ++ tailWord_35104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35104).length < 2 ^ (prefixWord ++ tailWord_35104).sum := by decide
  have hdescent : baseEnd_35104 < baseStart_35104 := by decide
  rcases family_descends (prefixWord ++ tailWord_35104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35108 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_35108 : Nat := 118140960795 + 35108 * 2 ^ 59
def prefixEnd_35108 : Nat := 4983230072969 + 3 ^ 40 * 35108 * 2
def baseEnd_35108 : Nat := 12018185878769248992365

theorem tailTrace_35108 : CollatzResearch.WordTrace tailWord_35108 prefixEnd_35108 12018185878769248992365 := by
  unfold tailWord_35108
  simp only [CollatzResearch.WordTrace]
  refine ⟨640246978408593407072989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 853662637878124542763985 640246978408593407072989)
  ·
    refine ⟨240092616903222527652371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 640246978408593407072989 240092616903222527652371)
    ·
      refine ⟨360138925354833791478557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240092616903222527652371 360138925354833791478557)
      ·
        refine ⟨135052097008062671804459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360138925354833791478557 135052097008062671804459)
        ·
          refine ⟨202578145512094007706689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135052097008062671804459 202578145512094007706689)
          ·
            refine ⟨151933609134070505780017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202578145512094007706689 151933609134070505780017)
            ·
              refine ⟨113950206850552879335013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151933609134070505780017 113950206850552879335013)
              ·
                refine ⟨21365663784478664875315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113950206850552879335013 21365663784478664875315)
                ·
                  refine ⟨32048495676717997312973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21365663784478664875315 32048495676717997312973)
                  ·
                    refine ⟨12018185878769248992365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32048495676717997312973 12018185878769248992365)
                    ·
                      rfl

theorem cell22_35108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_35108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35108 prefixEnd_35108 := by exact prefixLift 35108
  have htrace : WordTrace (prefixWord ++ tailWord_35108) baseStart_35108 baseEnd_35108 := by
    simpa [prefixWord, tailWord_35108, baseEnd_35108] using wordTrace_append hprefix tailTrace_35108
  have hstable : (prefixWord ++ tailWord_35108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35108).length < 2 ^ (prefixWord ++ tailWord_35108).sum := by decide
  have hdescent : baseEnd_35108 < baseStart_35108 := by decide
  rcases family_descends (prefixWord ++ tailWord_35108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35202 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_35202 : Nat := 118140960795 + 35202 * 2 ^ 59
def prefixEnd_35202 : Nat := 4983230072969 + 3 ^ 40 * 35202 * 2
def baseEnd_35202 : Nat := 12050363999784337142077

theorem tailTrace_35202 : CollatzResearch.WordTrace tailWord_35202 prefixEnd_35202 12050363999784337142077 := by
  unfold tailWord_35202
  simp only [CollatzResearch.WordTrace]
  refine ⟨320980604619160217016965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 855948278984427245378573 320980604619160217016965)
  ·
    refine ⟨60183863366092540690681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 320980604619160217016965 60183863366092540690681)
    ·
      refine ⟨45137897524569405518011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60183863366092540690681 45137897524569405518011)
      ·
        refine ⟨67706846286854108277017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45137897524569405518011 67706846286854108277017)
        ·
          refine ⟨50780134715140581207763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67706846286854108277017 50780134715140581207763)
          ·
            refine ⟨76170202072710871811645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50780134715140581207763 76170202072710871811645)
            ·
              refine ⟨28563825777266576929367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76170202072710871811645 28563825777266576929367)
              ·
                refine ⟨42845738665899865394051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28563825777266576929367 42845738665899865394051)
                ·
                  refine ⟨64268607998849798091077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42845738665899865394051 64268607998849798091077)
                  ·
                    refine ⟨12050363999784337142077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64268607998849798091077 12050363999784337142077)
                    ·
                      rfl

theorem cell22_35202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_35202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35202 prefixEnd_35202 := by exact prefixLift 35202
  have htrace : WordTrace (prefixWord ++ tailWord_35202) baseStart_35202 baseEnd_35202 := by
    simpa [prefixWord, tailWord_35202, baseEnd_35202] using wordTrace_append hprefix tailTrace_35202
  have hstable : (prefixWord ++ tailWord_35202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35202).length < 2 ^ (prefixWord ++ tailWord_35202).sum := by decide
  have hdescent : baseEnd_35202 < baseStart_35202 := by decide
  rcases family_descends (prefixWord ++ tailWord_35202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35260 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_35260 : Nat := 118140960795 + 35260 * 2 ^ 59
def prefixEnd_35260 : Nat := 4983230072969 + 3 ^ 40 * 35260 * 2
def baseEnd_35260 : Nat := 12070218585091519191899

theorem tailTrace_35260 : CollatzResearch.WordTrace tailWord_35260 prefixEnd_35260 12070218585091519191899 := by
  unfold tailWord_35260
  simp only [CollatzResearch.WordTrace]
  refine ⟨643018926133258386839617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 857358568177677849119489 643018926133258386839617)
  ·
    refine ⟨482264194599943790129713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 643018926133258386839617 482264194599943790129713)
    ·
      refine ⟨361698145949957842597285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 482264194599943790129713 361698145949957842597285)
      ·
        refine ⟨67818402365617095486991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 361698145949957842597285 67818402365617095486991)
        ·
          refine ⟨101727603548425643230487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67818402365617095486991 101727603548425643230487)
          ·
            refine ⟨152591405322638464845731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101727603548425643230487 152591405322638464845731)
            ·
              refine ⟨228887107983957697268597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152591405322638464845731 228887107983957697268597)
              ·
                refine ⟨21458166373496034118931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228887107983957697268597 21458166373496034118931)
                ·
                  refine ⟨32187249560244051178397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21458166373496034118931 32187249560244051178397)
                  ·
                    refine ⟨12070218585091519191899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32187249560244051178397 12070218585091519191899)
                    ·
                      rfl

theorem cell22_35260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_35260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35260 prefixEnd_35260 := by exact prefixLift 35260
  have htrace : WordTrace (prefixWord ++ tailWord_35260) baseStart_35260 baseEnd_35260 := by
    simpa [prefixWord, tailWord_35260, baseEnd_35260] using wordTrace_append hprefix tailTrace_35260
  have hstable : (prefixWord ++ tailWord_35260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35260).length < 2 ^ (prefixWord ++ tailWord_35260).sum := by decide
  have hdescent : baseEnd_35260 < baseStart_35260 := by decide
  rcases family_descends (prefixWord ++ tailWord_35260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35303 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 1, 4]
def baseStart_35303 : Nat := 118140960795 + 35303 * 2 ^ 59
def prefixEnd_35303 : Nat := 4983230072969 + 3 ^ 40 * 35303 * 2
def baseEnd_35303 : Nat := 12084938363853740366767

theorem tailTrace_35303 : CollatzResearch.WordTrace tailWord_35303 prefixEnd_35303 12084938363853740366767 := by
  unfold tailWord_35303
  simp only [CollatzResearch.WordTrace]
  refine ⟨1287606191110735117494563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 858404127407156744996375 1287606191110735117494563)
  ·
    refine ⟨1931409286666102676241845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1287606191110735117494563 1931409286666102676241845)
    ·
      refine ⟨181069620624947125897673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1931409286666102676241845 181069620624947125897673)
      ·
        refine ⟨135802215468710344423255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181069620624947125897673 135802215468710344423255)
        ·
          refine ⟨203703323203065516634883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135802215468710344423255 203703323203065516634883)
          ·
            refine ⟨305554984804598274952325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203703323203065516634883 305554984804598274952325)
            ·
              refine ⟨57291559650862176553561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305554984804598274952325 57291559650862176553561)
              ·
                refine ⟨42968669738146632415171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57291559650862176553561 42968669738146632415171)
                ·
                  refine ⟨64453004607219948622757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42968669738146632415171 64453004607219948622757)
                  ·
                    refine ⟨12084938363853740366767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64453004607219948622757 12084938363853740366767)
                    ·
                      rfl

theorem cell22_35303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_35303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35303 prefixEnd_35303 := by exact prefixLift 35303
  have htrace : WordTrace (prefixWord ++ tailWord_35303) baseStart_35303 baseEnd_35303 := by
    simpa [prefixWord, tailWord_35303, baseEnd_35303] using wordTrace_append hprefix tailTrace_35303
  have hstable : (prefixWord ++ tailWord_35303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35303).length < 2 ^ (prefixWord ++ tailWord_35303).sum := by decide
  have hdescent : baseEnd_35303 < baseStart_35303 := by decide
  rcases family_descends (prefixWord ++ tailWord_35303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35331 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 2, 4]
def baseStart_35331 : Nat := 118140960795 + 35331 * 2 ^ 59
def prefixEnd_35331 : Nat := 4983230072969 + 3 ^ 40 * 35331 * 2
def baseEnd_35331 : Nat := 12094523336071000666681

theorem tailTrace_35331 : CollatzResearch.WordTrace tailWord_35331 prefixEnd_35331 12094523336071000666681 := by
  unfold tailWord_35331
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288627435009295899513847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 859084956672863933009231 1288627435009295899513847)
  ·
    refine ⟨1932941152513943849270771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1288627435009295899513847 1932941152513943849270771)
    ·
      refine ⟨2899411728770915773906157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932941152513943849270771 2899411728770915773906157)
      ·
        refine ⟨1087279398289093415214809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2899411728770915773906157 1087279398289093415214809)
        ·
          refine ⟨815459548716820061411107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087279398289093415214809 815459548716820061411107)
          ·
            refine ⟨1223189323075230092116661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815459548716820061411107 1223189323075230092116661)
            ·
              refine ⟨114673999038302821135937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1223189323075230092116661 114673999038302821135937)
              ·
                refine ⟨86005499278727115851953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114673999038302821135937 86005499278727115851953)
                ·
                  refine ⟨64504124459045336888965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86005499278727115851953 64504124459045336888965)
                  ·
                    refine ⟨12094523336071000666681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64504124459045336888965 12094523336071000666681)
                    ·
                      rfl

theorem cell22_35331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_35331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35331 prefixEnd_35331 := by exact prefixLift 35331
  have htrace : WordTrace (prefixWord ++ tailWord_35331) baseStart_35331 baseEnd_35331 := by
    simpa [prefixWord, tailWord_35331, baseEnd_35331] using wordTrace_append hprefix tailTrace_35331
  have hstable : (prefixWord ++ tailWord_35331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35331).length < 2 ^ (prefixWord ++ tailWord_35331).sum := by decide
  have hdescent : baseEnd_35331 < baseStart_35331 := by decide
  rcases family_descends (prefixWord ++ tailWord_35331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35335 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 6]
def baseStart_35335 : Nat := 118140960795 + 35335 * 2 ^ 59
def prefixEnd_35335 : Nat := 4983230072969 + 3 ^ 40 * 35335 * 2
def baseEnd_35335 : Nat := 4031964205938774522223

theorem tailTrace_35335 : CollatzResearch.WordTrace tailWord_35335 prefixEnd_35335 4031964205938774522223 := by
  unfold tailWord_35335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288773326994804582659459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 859182217996536388439639 1288773326994804582659459)
  ·
    refine ⟨1933159990492206873989189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1288773326994804582659459 1933159990492206873989189)
    ·
      refine ⟨362467498217288788872973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1933159990492206873989189 362467498217288788872973)
      ·
        refine ⟨135925311831483295827365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362467498217288788872973 135925311831483295827365)
        ·
          refine ⟨25485995968403117967631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135925311831483295827365 25485995968403117967631)
          ·
            refine ⟨38228993952604676951447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25485995968403117967631 38228993952604676951447)
            ·
              refine ⟨57343490928907015427171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38228993952604676951447 57343490928907015427171)
              ·
                refine ⟨86015236393360523140757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57343490928907015427171 86015236393360523140757)
                ·
                  refine ⟨4031964205938774522223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86015236393360523140757 4031964205938774522223)
                  ·
                    rfl

theorem cell22_35335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 6].length) (baseStart_35335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35335 prefixEnd_35335 := by exact prefixLift 35335
  have htrace : WordTrace (prefixWord ++ tailWord_35335) baseStart_35335 baseEnd_35335 := by
    simpa [prefixWord, tailWord_35335, baseEnd_35335] using wordTrace_append hprefix tailTrace_35335
  have hstable : (prefixWord ++ tailWord_35335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35335).length < 2 ^ (prefixWord ++ tailWord_35335).sum := by decide
  have hdescent : baseEnd_35335 < baseStart_35335 := by decide
  rcases family_descends (prefixWord ++ tailWord_35335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35344 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_35344 : Nat := 118140960795 + 35344 * 2 ^ 59
def prefixEnd_35344 : Nat := 4983230072969 + 3 ^ 40 * 35344 * 2
def baseEnd_35344 : Nat := 12098973501743300091641

theorem tailTrace_35344 : CollatzResearch.WordTrace tailWord_35344 prefixEnd_35344 12098973501743300091641 := by
  unfold tailWord_35344
  simp only [CollatzResearch.WordTrace]
  refine ⟨644550791981099559868543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 859401055974799413158057 644550791981099559868543)
  ·
    refine ⟨966826187971649339802815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 644550791981099559868543 966826187971649339802815)
    ·
      refine ⟨1450239281957474009704223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966826187971649339802815 1450239281957474009704223)
      ·
        refine ⟨2175358922936211014556335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450239281957474009704223 2175358922936211014556335)
        ·
          refine ⟨3263038384404316521834503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175358922936211014556335 3263038384404316521834503)
          ·
            refine ⟨4894557576606474782751755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263038384404316521834503 4894557576606474782751755)
            ·
              refine ⟨7341836364909712174127633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894557576606474782751755 7341836364909712174127633)
              ·
                refine ⟨5506377273682284130595725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7341836364909712174127633 5506377273682284130595725)
                ·
                  refine ⟨2064891477630856548973397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5506377273682284130595725 2064891477630856548973397)
                  ·
                    refine ⟨12098973501743300091641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2064891477630856548973397 12098973501743300091641)
                    ·
                      rfl

theorem cell22_35344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_35344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35344 prefixEnd_35344 := by exact prefixLift 35344
  have htrace : WordTrace (prefixWord ++ tailWord_35344) baseStart_35344 baseEnd_35344 := by
    simpa [prefixWord, tailWord_35344, baseEnd_35344] using wordTrace_append hprefix tailTrace_35344
  have hstable : (prefixWord ++ tailWord_35344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35344).length < 2 ^ (prefixWord ++ tailWord_35344).sum := by decide
  have hdescent : baseEnd_35344 < baseStart_35344 := by decide
  rcases family_descends (prefixWord ++ tailWord_35344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35380 : List Nat := [2, 5, 1, 3, 2, 9]
def baseStart_35380 : Nat := 118140960795 + 35380 * 2 ^ 59
def prefixEnd_35380 : Nat := 4983230072969 + 3 ^ 40 * 35380 * 2
def baseEnd_35380 : Nat := 149522185647545755451

theorem tailTrace_35380 : CollatzResearch.WordTrace tailWord_35380 prefixEnd_35380 149522185647545755451 := by
  unfold tailWord_35380
  simp only [CollatzResearch.WordTrace]
  refine ⟨645207305915888634023797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 860276407887851512031729 645207305915888634023797)
  ·
    refine ⟨60488184929614559439731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 645207305915888634023797 60488184929614559439731)
    ·
      refine ⟨90732277394421839159597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60488184929614559439731 90732277394421839159597)
      ·
        refine ⟨34024604022908189684849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90732277394421839159597 34024604022908189684849)
        ·
          refine ⟨25518453017181142263637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34024604022908189684849 25518453017181142263637)
          ·
            refine ⟨149522185647545755451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 25518453017181142263637 149522185647545755451)
            ·
              rfl

theorem cell22_35380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 9].length) (baseStart_35380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35380 prefixEnd_35380 := by exact prefixLift 35380
  have htrace : WordTrace (prefixWord ++ tailWord_35380) baseStart_35380 baseEnd_35380 := by
    simpa [prefixWord, tailWord_35380, baseEnd_35380] using wordTrace_append hprefix tailTrace_35380
  have hstable : (prefixWord ++ tailWord_35380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35380).length < 2 ^ (prefixWord ++ tailWord_35380).sum := by decide
  have hdescent : baseEnd_35380 < baseStart_35380 := by decide
  rcases family_descends (prefixWord ++ tailWord_35380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35406 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_35406 : Nat := 118140960795 + 35406 * 2 ^ 59
def prefixEnd_35406 : Nat := 4983230072969 + 3 ^ 40 * 35406 * 2
def baseEnd_35406 : Nat := 12120197368795805041451

theorem tailTrace_35406 : CollatzResearch.WordTrace tailWord_35406 prefixEnd_35406 12120197368795805041451 := by
  unfold tailWord_35406
  simp only [CollatzResearch.WordTrace]
  refine ⟨161420363717197963561759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 860908606491722472329381 161420363717197963561759)
  ·
    refine ⟨242130545575796945342639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161420363717197963561759 242130545575796945342639)
    ·
      refine ⟨363195818363695418013959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242130545575796945342639 363195818363695418013959)
      ·
        refine ⟨544793727545543127020939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363195818363695418013959 544793727545543127020939)
        ·
          refine ⟨817190591318314690531409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544793727545543127020939 817190591318314690531409)
          ·
            refine ⟨612892943488736017898557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817190591318314690531409 612892943488736017898557)
            ·
              refine ⟨229834853808276006711959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 612892943488736017898557 229834853808276006711959)
              ·
                refine ⟨344752280712414010067939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229834853808276006711959 344752280712414010067939)
                ·
                  refine ⟨517128421068621015101909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344752280712414010067939 517128421068621015101909)
                  ·
                    refine ⟨12120197368795805041451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 517128421068621015101909 12120197368795805041451)
                    ·
                      rfl

theorem cell22_35406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_35406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35406 prefixEnd_35406 := by exact prefixLift 35406
  have htrace : WordTrace (prefixWord ++ tailWord_35406) baseStart_35406 baseEnd_35406 := by
    simpa [prefixWord, tailWord_35406, baseEnd_35406] using wordTrace_append hprefix tailTrace_35406
  have hstable : (prefixWord ++ tailWord_35406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35406).length < 2 ^ (prefixWord ++ tailWord_35406).sum := by decide
  have hdescent : baseEnd_35406 < baseStart_35406 := by decide
  rcases family_descends (prefixWord ++ tailWord_35406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35442 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_35442 : Nat := 118140960795 + 35442 * 2 ^ 59
def prefixEnd_35442 : Nat := 4983230072969 + 3 ^ 40 * 35442 * 2
def baseEnd_35442 : Nat := 4044173634834570380447

theorem tailTrace_35442 : CollatzResearch.WordTrace tailWord_35442 prefixEnd_35442 4044173634834570380447 := by
  unfold tailWord_35442
  simp only [CollatzResearch.WordTrace]
  refine ⟨323168984401790464201145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 861783958404774571203053 323168984401790464201145)
  ·
    refine ⟨242376738301342848150859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 323168984401790464201145 242376738301342848150859)
    ·
      refine ⟨363565107452014272226289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242376738301342848150859 363565107452014272226289)
      ·
        refine ⟨272673830589010704169717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363565107452014272226289 272673830589010704169717)
        ·
          refine ⟨25563171617719753515911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 272673830589010704169717 25563171617719753515911)
          ·
            refine ⟨38344757426579630273867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25563171617719753515911 38344757426579630273867)
            ·
              refine ⟨57517136139869445410801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38344757426579630273867 57517136139869445410801)
              ·
                refine ⟨43137852104902084058101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57517136139869445410801 43137852104902084058101)
                ·
                  refine ⟨4044173634834570380447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43137852104902084058101 4044173634834570380447)
                  ·
                    rfl

theorem cell22_35442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_35442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35442 prefixEnd_35442 := by exact prefixLift 35442
  have htrace : WordTrace (prefixWord ++ tailWord_35442) baseStart_35442 baseEnd_35442 := by
    simpa [prefixWord, tailWord_35442, baseEnd_35442] using wordTrace_append hprefix tailTrace_35442
  have hstable : (prefixWord ++ tailWord_35442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35442).length < 2 ^ (prefixWord ++ tailWord_35442).sum := by decide
  have hdescent : baseEnd_35442 < baseStart_35442 := by decide
  rcases family_descends (prefixWord ++ tailWord_35442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35481 : List Nat := [1, 2, 1, 2, 1, 2, 5, 8]
def baseStart_35481 : Nat := 118140960795 + 35481 * 2 ^ 59
def prefixEnd_35481 : Nat := 4983230072969 + 3 ^ 40 * 35481 * 2
def baseEnd_35481 : Nat := 1349541266835623268469

theorem tailTrace_35481 : CollatzResearch.WordTrace tailWord_35481 prefixEnd_35481 1349541266835623268469 := by
  unfold tailWord_35481
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294098384465871517474297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 862732256310581011649531 1294098384465871517474297)
  ·
    refine ⟨970573788349403638105723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1294098384465871517474297 970573788349403638105723)
    ·
      refine ⟨1455860682524105457158585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970573788349403638105723 1455860682524105457158585)
      ·
        refine ⟨1091895511893079092868939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1455860682524105457158585 1091895511893079092868939)
        ·
          refine ⟨1637843267839618639303409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091895511893079092868939 1637843267839618639303409)
          ·
            refine ⟨1228382450879713979477557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637843267839618639303409 1228382450879713979477557)
            ·
              refine ⟨115160854769973185576021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1228382450879713979477557 115160854769973185576021)
              ·
                refine ⟨1349541266835623268469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 115160854769973185576021 1349541266835623268469)
                ·
                  rfl

theorem cell22_35481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 8].length) (baseStart_35481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35481 prefixEnd_35481 := by exact prefixLift 35481
  have htrace : WordTrace (prefixWord ++ tailWord_35481) baseStart_35481 baseEnd_35481 := by
    simpa [prefixWord, tailWord_35481, baseEnd_35481] using wordTrace_append hprefix tailTrace_35481
  have hstable : (prefixWord ++ tailWord_35481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35481).length < 2 ^ (prefixWord ++ tailWord_35481).sum := by decide
  have hdescent : baseEnd_35481 < baseStart_35481 := by decide
  rcases family_descends (prefixWord ++ tailWord_35481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35502 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_35502 : Nat := 118140960795 + 35502 * 2 ^ 59
def prefixEnd_35502 : Nat := 4983230072969 + 3 ^ 40 * 35502 * 2
def baseEnd_35502 : Nat := 12153060130683554641157

theorem tailTrace_35502 : CollatzResearch.WordTrace tailWord_35502 prefixEnd_35502 12153060130683554641157 := by
  unfold tailWord_35502
  simp only [CollatzResearch.WordTrace]
  refine ⟨161858039673724012998595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 863242878259861402659173 161858039673724012998595)
  ·
    refine ⟨242787059510586019497893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161858039673724012998595 242787059510586019497893)
    ·
      refine ⟨45522573658234878655855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242787059510586019497893 45522573658234878655855)
      ·
        refine ⟨68283860487352317983783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45522573658234878655855 68283860487352317983783)
        ·
          refine ⟨102425790731028476975675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68283860487352317983783 102425790731028476975675)
          ·
            refine ⟨153638686096542715463513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102425790731028476975675 153638686096542715463513)
            ·
              refine ⟨115229014572407036597635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153638686096542715463513 115229014572407036597635)
              ·
                refine ⟨172843521858610554896453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115229014572407036597635 172843521858610554896453)
                ·
                  refine ⟨32408160348489479043085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172843521858610554896453 32408160348489479043085)
                  ·
                    refine ⟨12153060130683554641157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32408160348489479043085 12153060130683554641157)
                    ·
                      rfl

theorem cell22_35502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_35502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35502 prefixEnd_35502 := by exact prefixLift 35502
  have htrace : WordTrace (prefixWord ++ tailWord_35502) baseStart_35502 baseEnd_35502 := by
    simpa [prefixWord, tailWord_35502, baseEnd_35502] using wordTrace_append hprefix tailTrace_35502
  have hstable : (prefixWord ++ tailWord_35502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35502).length < 2 ^ (prefixWord ++ tailWord_35502).sum := by decide
  have hdescent : baseEnd_35502 < baseStart_35502 := by decide
  rcases family_descends (prefixWord ++ tailWord_35502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
